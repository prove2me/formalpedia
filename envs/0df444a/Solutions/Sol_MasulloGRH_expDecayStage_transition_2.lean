-- Prove2me | solution 2 for MasulloGRH.expDecayStage_transition
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T18:59:53.31488+00:00
-- url     : https://prove2.me/submissions/4adf462f-d539-48ff-b816-a41eb09c75ab

import Theorems.Thm_MasulloGRH_expDecayStage_concrete
import Theorems.Thm_MasulloGRH_schwartzBruhatAverage_transfer
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup

set_option autoImplicit false

universe u

namespace MasulloGRHTransitionAux

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

end MasulloGRHTransitionAux

open MasulloGRH MasulloGRHTransitionAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k k' : Subgroup G)
    (hk : IsGoodSubgroup k) (hk' : IsGoodSubgroup k') (hle : k' ≤ k) :
    ∃ f : ExpDecayStage G m I k → ExpDecayStage G m I k', Continuous f ∧
      ∀ y, ExpDecayStage.incl G m I k' (f y) = ExpDecayStage.incl G m I k y := by
  obtain ⟨hs, -, hW⟩ := expDecayStage_concrete G m hm I hne k hk
  obtain ⟨hs', -, hW'⟩ := expDecayStage_concrete G m hm I hne k' hk'
  obtain ⟨m₁, n₁, r₁, s₁, d₁, π, hπ⟩ := exists_elemPresentation_of_isStructuralPair G ⊤ k hs
  obtain ⟨m₂, n₂, r₂, s₂, d₂, π', hπ'⟩ := exists_elemPresentation_of_isStructuralPair G ⊤ k' hs'
  obtain ⟨W, hWa, hWtop, -⟩ := hW m₁ n₁ r₁ s₁ d₁ π hπ
  obtain ⟨W', hWa', hWtop', -⟩ := hW' m₂ n₂ r₂ s₂ d₂ π' hπ'
  obtain ⟨T, hTc, hT⟩ := schwartzBruhatAverage_transfer G ⊤ k m₁ n₁ r₁ s₁ d₁ π hs hπ
    ⊤ k' m₂ n₂ r₂ s₂ d₂ π' hs' hπ'
  have hk'c : IsCompact (k' : Set G) := isCompact_of_isGoodSubgroup G k' hk'
  have hWc : ∀ a ∈ I, Continuous (W a) := fun a ha =>
    cont_dom_of_top_eq hWtop (continuous_iInf_dom (continuous_iInf_dom (i := ha)
      continuous_induced_dom))
  let f : ExpDecayStage G m I k → ExpDecayStage G m I k' :=
    fun y => ⟨y.1, fun h hh g => y.2 h (hle hh) g⟩
  refine ⟨f, ?_, fun y => rfl⟩
  refine cont_of_top_eq hWtop' ?_
  refine continuous_iInf_rng.2 fun a => continuous_iInf_rng.2 fun ha => continuous_induced_rng.2 ?_
  have e : (W' a ∘ f) = T ∘ W a := by
    funext y
    refine es_ext fun z => ?_
    obtain ⟨x, hx⟩ := hπ'.2.2.2.1 (Multiplicative.ofAdd z)
    have hz : z = Multiplicative.toAdd (π' ⟨(x : G), Subgroup.mem_top _⟩) := by
      rw [Subtype.coe_eta, hx]; rfl
    have h1 := congrFun (hT (W a y)) (x : G)
    rw [average_eq k' hk'c _ (fun x y hy =>
      pullback_mul k π hπ _ x y (hle hy)), extendPullback_top, extendPullback_top] at h1
    show (W' a (f y)).toFun z = (T (W a y)).toFun z
    rw [hz, ← h1, hWa' a ha (f y) x, hWa a ha y x]
    rfl
  rw [e]
  exact hTc.comp (hWc a ha)
