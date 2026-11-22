-- Prove2me | solution 2 for MasulloGRH.expDecayStage_frechet_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T18:59:56.625374+00:00
-- url     : https://prove2.me/submissions/88fa855e-3700-43d1-aa59-a1ba77fa9612

import Theorems.Thm_MasulloGRH_expDecayStage_concrete
import Theorems.Thm_MasulloGRH_expWeighted_projective_isFrechet
import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le

set_option autoImplicit false

universe u

namespace MasulloGRHStageFNAux



open MasulloGRH MeasureTheory

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

lemma extendPullback_top {m n r s : ℕ} {d : Fin s → ℕ}
    (π : (⊤ : Subgroup H) →* Multiplicative (ElemGroup m n r s d))
    (g : ElemGroup m n r s d → ℂ) (x : H) :
    extendPullback ⊤ π g x = g (Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)) := by
  unfold extendPullback
  rw [dif_pos (Subgroup.mem_top x)]

lemma pullback_mul {m n r s : ℕ} {d : Fin s → ℕ} (k : Subgroup H)
    (π : (⊤ : Subgroup H) →* Multiplicative (ElemGroup m n r s d))
    (hπ : IsElemPresentation ⊤ k π) (g : ElemGroup m n r s d → ℂ) (x y : H) (hy : y ∈ k) :
    extendPullback ⊤ π g (x * y) = extendPullback ⊤ π g x := by
  rw [extendPullback_top, extendPullback_top]
  have h1 : π ⟨y, Subgroup.mem_top y⟩ = 1 := (hπ.2.2.2.2 ⟨y, Subgroup.mem_top y⟩).2 hy
  have : (⟨x * y, Subgroup.mem_top _⟩ : (⊤ : Subgroup H)) =
      ⟨x, Subgroup.mem_top x⟩ * ⟨y, Subgroup.mem_top y⟩ := rfl
  rw [this, map_mul, h1, mul_one]

lemma average_eq (k₀ : Subgroup H) (hk₀ : IsCompact (k₀ : Set H)) (f : H → ℂ)
    (hf : ∀ x, ∀ y ∈ k₀, f (x * y) = f x) (x : H) :
    schwartzBruhatAverage ⊤ k₀ f x = f x := by
  letI : MeasurableSpace k₀ := borel k₀
  haveI : BorelSpace k₀ := ⟨rfl⟩
  haveI : CompactSpace k₀ := isCompact_iff_compactSpace.mp hk₀
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h1 : (fun y : k₀ => f (x * y)) = fun _ => f x := funext fun y => hf x y y.2
  have h2 : subgroupHaar k₀ = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk₀]
  simp only [h1, h2, integral_const]
  have h3 : (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k₀)) Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts k₀))
    simpa using this
  simp [measureReal_def, h3]

lemma es_ext {m n r s : ℕ} {d : Fin s → ℕ} {f g : ElemSchwartz m n r s d}
    (h : ∀ z, f.toFun z = g.toFun z) : f = g :=
  Subtype.ext (funext h)

lemma cont_of_top_eq {α β : Type*} [TopologicalSpace α] {tβ t' : TopologicalSpace β}
    (h : tβ = t') {f : α → β} (hf : @Continuous α β _ t' f) : @Continuous α β _ tβ f := by
  rw [h]; exact hf

lemma cont_dom_of_top_eq {α β : Type*} {tα t' : TopologicalSpace α} [TopologicalSpace β]
    (h : tα = t') {f : α → β} (hf : @Continuous α β t' _ f) : @Continuous α β tα _ f := by
  rw [h]; exact hf


/-- the kernel of a module as a subgroup -/
def modKer {m : H → ℝ} (hm : IsModule m) : Subgroup H where
  carrier := {g | m g = 1}
  one_mem' := by
    show m 1 = 1
    have h := hm.map_mul 1 1
    rw [mul_one] at h
    have hp := hm.pos 1
    nlinarith
  mul_mem' {a b} ha hb := by
    show m (a * b) = 1
    rw [hm.map_mul, show m a = 1 from ha, show m b = 1 from hb, one_mul]
  inv_mem' {a} ha := by
    show m a⁻¹ = 1
    have h := hm.map_mul a a⁻¹
    rw [mul_inv_cancel, show m a = 1 from ha, one_mul] at h
    have h1 := hm.map_mul 1 1
    rw [mul_one] at h1
    have hp := hm.pos 1
    have : m 1 = 1 := by nlinarith
    rw [← h, this]

lemma module_mul_of_compact {m : H → ℝ} (hm : IsRposModule m) (k : Subgroup H)
    (hk : IsCompact (k : Set H)) (x y : H) (hy : y ∈ k) : m (x * y) = m x := by
  have h := (isCompact_moduleKernel_and_compact_le H m hm (modKer hm.1) (fun _ => Iff.rfl)).2 k hk hy
  rw [hm.1.map_mul, show m y = 1 from h, mul_one]


end MasulloGRHStageFNAux

open MasulloGRH MasulloGRHStageFNAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsFrechet (ExpDecayStage G m I k) ∧ IsNuclear (ExpDecayStage G m I k) := by
  obtain ⟨hs, hnuc, hW⟩ := expDecayStage_concrete G m hm I hne k hk
  refine ⟨?_, hnuc⟩
  obtain ⟨m₁, n₁, r₁, s₁, d₁, π, hπ⟩ := exists_elemPresentation_of_isStructuralPair G ⊤ k hs
  obtain ⟨W, hWa, hWtop, hWsurj⟩ := hW m₁ n₁ r₁ s₁ d₁ π hπ
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hk
  obtain ⟨a₀, ha₀⟩ := hne
  have hne : I.Nonempty := ⟨a₀, ha₀⟩
  -- the quotient map `q : G → G/k = E`
  let q : G → ElemGroup m₁ n₁ r₁ s₁ d₁ := fun x =>
    Multiplicative.toAdd (π ⟨x, Subgroup.mem_top x⟩)
  have hqs : Function.Surjective q := by
    intro e
    obtain ⟨x, hx⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd e)
    exact ⟨x, by show Multiplicative.toAdd (π ⟨(x : G), _⟩) = e; rw [Subtype.coe_eta, hx]; rfl⟩
  have hqmul : ∀ x y, q (x * y) = q x + q y := by
    intro x y
    have : (⟨x * y, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) =
        ⟨x, Subgroup.mem_top x⟩ * ⟨y, Subgroup.mem_top y⟩ := rfl
    show Multiplicative.toAdd (π _) = _
    rw [this, map_mul]; rfl
  have hqc : Continuous q :=
    continuous_toAdd.comp (hπ.2.1.comp (continuous_id.subtype_mk _))
  have hqo : IsOpenMap q := by
    intro U hU
    have h1 : IsOpen (π '' ((Subtype.val : (⊤ : Subgroup G) → G) ⁻¹' U)) :=
      hπ.2.2.1 _ (hU.preimage continuous_subtype_val)
    have h2 : q '' U = Multiplicative.ofAdd ⁻¹' (π '' ((Subtype.val : (⊤ : Subgroup G) → G) ⁻¹' U)) := by
      ext e
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩
      · rintro ⟨x, hx, hxe⟩
        exact ⟨x, hx, by show Multiplicative.toAdd (π ⟨(x : G), _⟩) = e; rw [Subtype.coe_eta, hxe]; rfl⟩
    rw [h2]
    exact h1.preimage continuous_ofAdd
  have hqq : Topology.IsQuotientMap q := hqo.isQuotientMap hqc hqs
  have hqker : ∀ x y, q x = q y → m x = m y := by
    intro x y hxy
    have h1 : π ⟨x⁻¹ * y, Subgroup.mem_top _⟩ = 1 := by
      have h2 : q (x⁻¹ * y) = 0 := by
        have h3 : q x + q (x⁻¹ * y) = q y := by rw [← hqmul, mul_inv_cancel_left]
        rw [hxy] at h3
        exact add_eq_left.mp h3
      exact h2
    have h4 : x⁻¹ * y ∈ k := (hπ.2.2.2.2 _).1 h1
    have := module_mul_of_compact hm k hkc x (x⁻¹ * y) h4
    rw [mul_inv_cancel_left] at this
    exact this.symm
  let μ : ElemGroup m₁ n₁ r₁ s₁ d₁ → ℝ := fun e => m (Classical.choose (hqs e))
  have hμ : ∀ x, μ (q x) = m x := fun x => hqker _ _ (Classical.choose_spec (hqs (q x)))
  have hμpos : ∀ e, 0 < μ e := fun e => hm.1.pos _
  have hμmul : ∀ e e', μ (e + e') = μ e * μ e' := by
    intro e e'
    obtain ⟨x, rfl⟩ := hqs e
    obtain ⟨y, rfl⟩ := hqs e'
    rw [← hqmul, hμ, hμ, hμ, hm.1.map_mul]
  have hμc : Continuous μ := by
    rw [hqq.continuous_iff]
    have : μ ∘ q = m := funext hμ
    rw [this]
    exact hm.1.continuous
  have hmpos : ∀ (x : G) (a : ℝ), ((m x ^ a : ℝ) : ℂ) ≠ 0 := fun x a =>
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (hm.1.pos x) a).ne'
  refine expWeighted_projective_isFrechet m₁ n₁ r₁ s₁ d₁ hπ.1 μ hμpos hμmul hμc I hI hne
    (ExpDecayStage G m I k) W ?_ hWtop ?_ ?_
  · intro a ha b hb ϕ e
    obtain ⟨x, rfl⟩ := hqs e
    rw [hμ]
    show (W a ϕ).toFun (Multiplicative.toAdd (π ⟨x, _⟩)) =
      _ * (W b ϕ).toFun (Multiplicative.toAdd (π ⟨x, _⟩))
    rw [hWa a ha ϕ x, hWa b hb ϕ x, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_add (hm.1.pos x), sub_add_cancel]
  · intro ϕ h0
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have h1 := hWa a₀ ha₀ ϕ x
    rw [h0 a₀ ha₀] at h1
    have h2 : ((m x ^ a₀ : ℝ) : ℂ) * (ExpDecayStage.incl G m I k ϕ).toFun x = 0 := h1.symm
    exact (mul_eq_zero.1 h2).resolve_left (hmpos x a₀)
  · intro g hg
    refine hWsurj g fun a ha b hb x => ?_
    have := hg a ha b hb (q x)
    rw [hμ] at this
    exact this
