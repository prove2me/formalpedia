-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_averaging
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T14:39:05.381177+00:00
-- url     : https://prove2.me/submissions/61eb1fd5-f3b8-43d6-a991-115bfebbb214

import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_exists_elemPresentation_of_isStructuralPair
import Theorems.Thm_MasulloGRH_schwartzBruhatAverage_transfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MasulloGRH

open MeasureTheory

namespace AveragingAux

/-! ### Continuity of Schwartz–Bruhat functions -/

theorem continuous_of_isRapidDecay {m n r s : ℕ} {d : Fin s → ℕ}
    (g : ElemGroup m n r s d → ℂ) (hg : IsRapidDecay g) : Continuous g := by
  let q : (Fin m → ℝ) × ((Fin n → ℝ) × ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))) →
      ElemGroup m n r s d :=
    Prod.map id (Prod.map (Pi.map fun _ (t : ℝ) => (t : UnitAddCircle)) id)
  have hqc : Continuous q := by
    refine continuous_id.prodMap (Continuous.prodMap ?_ continuous_id)
    exact continuous_pi fun j => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply j)
  have hqo : IsOpenMap q := by
    refine IsOpenMap.id.prodMap (IsOpenMap.prodMap ?_ IsOpenMap.id)
    exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe) (Filter.Eventually.of_forall
      fun _ => QuotientAddGroup.mk_surjective)
  have hqs : Function.Surjective q := by
    refine Function.Surjective.prodMap Function.surjective_id
      (Function.Surjective.prodMap ?_ Function.surjective_id)
    intro z
    exact ⟨fun j => (QuotientAddGroup.mk_surjective (z j)).choose,
      funext fun j => (QuotientAddGroup.mk_surjective (z j)).choose_spec⟩
  have hq : Topology.IsQuotientMap q := hqo.isQuotientMap hqc hqs
  rw [hq.continuous_iff]
  let h : ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i))) × ((Fin m → ℝ) × (Fin n → ℝ)) → ℂ :=
    fun p => elemLift g p.1.1 p.1.2 p.2
  have hh : Continuous h := by
    rw [continuous_prod_of_discrete_left]
    intro ab
    exact (hg.1 ab.1 ab.2).continuous
  have : g ∘ q = h ∘ fun p => (p.2.2, (p.1, p.2.1)) := rfl
  rw [this]
  exact hh.comp (by fun_prop)

theorem continuous_elemSchwartz {m n r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m n r s d) :
    Continuous g.toFun := by
  obtain ⟨g, hg⟩ := g
  show Continuous g
  induction hg using Submodule.span_induction with
  | mem x hx => exact continuous_of_isRapidDecay x hx
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a


section group

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_extendPullback {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (hΓ : IsOpen (Γ : Set G)) (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπ : Continuous π)
    (g : ElemGroup m n r s d → ℂ) (hg : Continuous g) : Continuous (extendPullback Γ π g) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Γ
  · have hon : ContinuousOn (extendPullback Γ π g) (Γ : Set G) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Set.domRestrict (Γ : Set G) (extendPullback Γ π g)) =
          fun y : Γ => g (Multiplicative.toAdd (π y)) := by
        funext y
        simp [Set.domRestrict, extendPullback]
      rw [this]
      exact hg.comp (continuous_toAdd.comp hπ)
    exact hon.continuousAt (hΓ.mem_nhds hx)
  · have hcl : IsOpen ((Γ : Set G)ᶜ) := (Subgroup.isClosed_of_isOpen Γ hΓ).isOpen_compl
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hcl.mem_nhds hx] with y hy
    simp [extendPullback, show y ∉ Γ from hy]

theorem continuous_of_mem_schwartzBruhatSubmodule (f : G → ℂ)
    (hf : f ∈ schwartzBruhatSubmodule G) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hx
    exact continuous_extendPullback Γ hs.1 π hπ.2.1 _ (continuous_elemSchwartz g)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

/-! ### The normalized Haar measure of a compact subgroup -/

local instance instMeasurableSpaceSubgroup (k : Subgroup G) : MeasurableSpace k := borel k
local instance instBorelSpaceSubgroup (k : Subgroup G) : BorelSpace k := ⟨rfl⟩

theorem subgroupHaar_eq (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
    subgroupHaar k = Measure.haarMeasure ⊤ := by
  simp only [subgroupHaar, dif_pos hk]

theorem isProbabilityMeasure_subgroupHaar (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    IsProbabilityMeasure (subgroupHaar k) := by
  have : CompactSpace k := isCompact_iff_compactSpace.mp hk
  rw [subgroupHaar_eq k hk]
  constructor
  have := Measure.haarMeasure_self (G := k) (K₀ := ⊤)
  simpa using this

theorem isMulLeftInvariant_subgroupHaar (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    (subgroupHaar k).IsMulLeftInvariant := by
  have : CompactSpace k := isCompact_iff_compactSpace.mp hk
  rw [subgroupHaar_eq k hk]
  infer_instance

open Classical in
theorem average_apply (Γ k : Subgroup G) (f : G → ℂ) (x : G) :
    schwartzBruhatAverage Γ k f x =
      if x ∈ Γ then ∫ y : k, f (x * y) ∂subgroupHaar k else 0 := by
  classical
  simp only [schwartzBruhatAverage, Set.indicator_apply, SetLike.mem_coe]

theorem integrable_translate (k : Subgroup G) (hk : IsCompact (k : Set G)) (f : G → ℂ)
    (hf : Continuous f) (x : G) :
    Integrable (fun y : k => f (x * y)) (subgroupHaar k) := by
  have := isProbabilityMeasure_subgroupHaar k hk
  have : CompactSpace k := isCompact_iff_compactSpace.mp hk
  have hc : Continuous (fun y : k => f (x * y)) :=
    hf.comp (continuous_const.mul continuous_subtype_val)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem average_add (Γ k : Subgroup G) (hk : IsCompact (k : Set G)) (f g : G → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    schwartzBruhatAverage Γ k (f + g) =
      schwartzBruhatAverage Γ k f + schwartzBruhatAverage Γ k g := by
  funext x
  simp only [average_apply, Pi.add_apply]
  split_ifs
  · exact integral_add (integrable_translate k hk f hf x) (integrable_translate k hk g hg x)
  · simp

theorem average_smul (Γ k : Subgroup G) (c : ℂ) (f : G → ℂ) :
    schwartzBruhatAverage Γ k (c • f) = c • schwartzBruhatAverage Γ k f := by
  funext x
  simp only [average_apply, Pi.smul_apply]
  split_ifs
  · exact integral_smul c _
  · simp

theorem average_zero (Γ k : Subgroup G) :
    schwartzBruhatAverage Γ k (0 : G → ℂ) = 0 := by
  funext x
  simp [average_apply]

theorem extendPullback_zero {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) :
    extendPullback Γ π (0 : ElemGroup m n r s d → ℂ) = 0 := by
  funext x
  simp [extendPullback]

theorem extendPullback_add {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (g₁ g₂ : ElemGroup m n r s d → ℂ) :
    extendPullback Γ π (g₁ + g₂) = extendPullback Γ π g₁ + extendPullback Γ π g₂ := by
  funext x
  by_cases hx : x ∈ Γ <;> simp [extendPullback, hx]

theorem extendPullback_smul {m n r s : ℕ} {d : Fin s → ℕ} (Γ : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (c : ℂ) (g : ElemGroup m n r s d → ℂ) :
    extendPullback Γ π (c • g) = c • extendPullback Γ π g := by
  funext x
  by_cases hx : x ∈ Γ <;> simp [extendPullback, hx]

/-- Property 2 (first half): the average over a smaller compact subgroup, restricted to a larger
open subgroup, fixes a function supported on `Γ` and invariant under `k`. -/
theorem average_extendPullback_of_le {m n r s : ℕ} {d : Fin s → ℕ} (Γ k Γ' k' : Subgroup G)
    (hkΓ : k ≤ Γ) (hk'c : IsCompact (k' : Set G)) (hΓ : Γ ≤ Γ') (hk : k' ≤ k)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπ : ∀ x : Γ, π x = 1 ↔ (x : G) ∈ k)
    (g : ElemGroup m n r s d → ℂ) :
    schwartzBruhatAverage Γ' k' (extendPullback Γ π g) = extendPullback Γ π g := by
  have hinv : ∀ (x : G) (y : k'), extendPullback Γ π g (x * y) = extendPullback Γ π g x := by
    intro x y
    have hyΓ : (y : G) ∈ Γ := hkΓ (hk y.2)
    by_cases hx : x ∈ Γ
    · have hxy : x * y ∈ Γ := Γ.mul_mem hx hyΓ
      simp only [extendPullback, dif_pos hx, dif_pos hxy]
      have : (⟨x * y, hxy⟩ : Γ) = ⟨x, hx⟩ * ⟨y, hyΓ⟩ := rfl
      rw [this, map_mul, (hπ ⟨y, hyΓ⟩).2 (hk y.2), mul_one]
    · have hxy : x * y ∉ Γ := fun h => hx (by simpa using Γ.mul_mem h (Γ.inv_mem hyΓ))
      simp only [extendPullback, dif_neg hx, dif_neg hxy]
  have := isProbabilityMeasure_subgroupHaar k' hk'c
  funext x
  rw [average_apply]
  split_ifs with hx
  · simp_rw [hinv x]
    simp
  · have : x ∉ Γ := fun h => hx (hΓ h)
    simp [extendPullback, this]

/-- Property 2 (second half): `A_{Γ,k} ∘ A_{Γ',k'} = A_{Γ,k}` when `Γ ⊆ Γ'` and `k' ⊆ k`. -/
theorem average_average (Γ k Γ' k' : Subgroup G) (hkΓ : k ≤ Γ) (hkc : IsCompact (k : Set G))
    (hk'c : IsCompact (k' : Set G)) (hΓ : Γ ≤ Γ') (hk : k' ≤ k) (f : G → ℂ)
    (hf : Continuous f) :
    schwartzBruhatAverage Γ k (schwartzBruhatAverage Γ' k' f) =
      schwartzBruhatAverage Γ k f := by
  funext x
  rw [average_apply, average_apply]
  split_ifs with hx
  · have h1 : ∀ y : k, schwartzBruhatAverage Γ' k' f (x * y) =
        ∫ z : k', f (x * y * z) ∂subgroupHaar k' := by
      intro y
      rw [average_apply, if_pos (hΓ (Γ.mul_mem hx (hkΓ y.2)))]
    simp_rw [h1]
    have := isProbabilityMeasure_subgroupHaar k hkc
    have := isProbabilityMeasure_subgroupHaar k' hk'c
    have : CompactSpace k := isCompact_iff_compactSpace.mp hkc
    have : CompactSpace k' := isCompact_iff_compactSpace.mp hk'c
    have := isMulLeftInvariant_subgroupHaar k hkc
    have hcont : Continuous (Function.uncurry fun (y : k) (z : k') => f (x * y * z)) :=
      hf.comp (by fun_prop)
    rw [integral_integral_swap_of_hasCompactSupport hcont (HasCompactSupport.of_compactSpace _)]
    have h2 : ∀ z : k', ∫ y : k, f (x * y * z) ∂subgroupHaar k =
        ∫ y : k, f (x * y) ∂subgroupHaar k := by
      intro z
      rw [← integral_mul_left_eq_self (fun y : k => f (x * y)) (⟨z, hk z.2⟩ : k)]
      congr 1 with y
      simp only [Subgroup.coe_mul]
      rw [mul_comm (z : G) (y : G), mul_assoc]
    simp_rw [h2]
    simp
  · rfl

end group

section structural

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- Property 1: for a structural pair with a presentation, the average of a Schwartz–Bruhat
function is the pull-back of an element of `S(Γ/k)`. -/
theorem average_mem_range (Γ k : Subgroup G) {m n r s : ℕ} {d : Fin s → ℕ}
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    ∃ g : ElemSchwartz m n r s d, schwartzBruhatAverage Γ k f = extendPullback Γ π g.toFun := by
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hs.2.2.1
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Γ'', k'', m'', n'', r'', s'', d'', π'', g'', hs'', hπ'', rfl⟩ := hx
    obtain ⟨T, -, hT⟩ := schwartzBruhatAverage_transfer G Γ'' k'' m'' n'' r'' s'' d'' π'' hs''
      hπ'' Γ k m n r s d π hs hπ
    exact ⟨T g'', hT g''⟩
  | zero =>
    refine ⟨0, ?_⟩
    rw [average_zero]
    exact (extendPullback_zero Γ π).symm
  | add x y hx hy ihx ihy =>
    obtain ⟨g₁, h₁⟩ := ihx
    obtain ⟨g₂, h₂⟩ := ihy
    refine ⟨g₁ + g₂, ?_⟩
    rw [average_add Γ k hkc x y (continuous_of_mem_schwartzBruhatSubmodule x hx)
      (continuous_of_mem_schwartzBruhatSubmodule y hy), h₁, h₂]
    exact (extendPullback_add Γ π g₁.toFun g₂.toFun).symm
  | smul a x hx ihx =>
    obtain ⟨g₁, h₁⟩ := ihx
    refine ⟨a • g₁, ?_⟩
    rw [average_smul, h₁]
    exact (extendPullback_smul Γ π a g₁.toFun).symm

theorem average_mem (Γ k : Subgroup G) (hs : IsStructuralPair Γ k) (f : G → ℂ)
    (hf : f ∈ schwartzBruhatSubmodule G) :
    schwartzBruhatAverage Γ k f ∈ schwartzBruhatSubmodule G := by
  obtain ⟨m, n, r, s, d, π, hπ⟩ := exists_elemPresentation_of_isStructuralPair G Γ k hs
  obtain ⟨g, hg⟩ := average_mem_range Γ k π hs hπ f hf
  rw [hg]
  exact Submodule.subset_span ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩

open Classical in
/-- The averaging operator `A_{Γ,k}` on `S(G)` for a structural pair, and `0` otherwise. -/
noncomputable def averagingOp (Γ k : Subgroup G) : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G :=
  if h : IsStructuralPair Γ k then
    { toFun := fun f => ⟨schwartzBruhatAverage Γ k f.1, average_mem Γ k h f.1 f.2⟩
      map_add' := fun f g => Subtype.ext (average_add Γ k
        (isCompact_of_isGoodSubgroup G k h.2.2.1) f.1 g.1
        (continuous_of_mem_schwartzBruhatSubmodule f.1 f.2)
        (continuous_of_mem_schwartzBruhatSubmodule g.1 g.2))
      map_smul' := fun c f => Subtype.ext (average_smul Γ k c f.1) }
  else 0

theorem averagingOp_apply (Γ k : Subgroup G) (h : IsStructuralPair Γ k) (f : SchwartzBruhat G) :
    (averagingOp Γ k f).1 = schwartzBruhatAverage Γ k f.1 := by
  simp only [averagingOp, dif_pos h]
  rfl

end structural

end AveragingAux

end MasulloGRH

open MasulloGRH MasulloGRH.AveragingAux in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] :
    ∃ A : Subgroup G → Subgroup G → (SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G),
      (∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π) (f : SchwartzBruhat G),
        ∃ g, A Γ k f = SchwartzBruhat.ofElem Γ k π hs hπ g) ∧
      (∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π) (Γ' k' : Subgroup G), IsStructuralPair Γ' k' →
        Γ ≤ Γ' → k' ≤ k → ∀ g,
          A Γ' k' (SchwartzBruhat.ofElem Γ k π hs hπ g) = SchwartzBruhat.ofElem Γ k π hs hπ g) ∧
      (∀ Γ k Γ' k' : Subgroup G, IsStructuralPair Γ k → IsStructuralPair Γ' k' →
        Γ ≤ Γ' → k' ≤ k → ∀ f, A Γ k (A Γ' k' f) = A Γ k f) ∧
      (∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π)
        (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
        (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' k')
        (hπ' : IsElemPresentation Γ' k' π'),
        ∃ T : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m' n' r' s' d', Continuous T ∧
          ∀ g, A Γ' k' (SchwartzBruhat.ofElem Γ k π hs hπ g) =
            SchwartzBruhat.ofElem Γ' k' π' hs' hπ' (T g)) := by
  refine ⟨averagingOp, ?_, ?_, ?_, ?_⟩
  · intro Γ k m n r s d π hs hπ f
    obtain ⟨g, hg⟩ := average_mem_range Γ k π hs hπ f.1 f.2
    exact ⟨g, Subtype.ext (by rw [averagingOp_apply Γ k hs]; exact hg)⟩
  · intro Γ k m n r s d π hs hπ Γ' k' hs' hΓ hk g
    apply Subtype.ext
    rw [averagingOp_apply Γ' k' hs']
    exact average_extendPullback_of_le Γ k Γ' k' hs.2.2.2
      (isCompact_of_isGoodSubgroup G k' hs'.2.2.1) hΓ hk π hπ.2.2.2.2 g.toFun
  · intro Γ k Γ' k' hs hs' hΓ hk f
    apply Subtype.ext
    rw [averagingOp_apply Γ k hs, averagingOp_apply Γ' k' hs', averagingOp_apply Γ k hs]
    exact average_average Γ k Γ' k' hs.2.2.2 (isCompact_of_isGoodSubgroup G k hs.2.2.1)
      (isCompact_of_isGoodSubgroup G k' hs'.2.2.1) hΓ hk f.1
      (continuous_of_mem_schwartzBruhatSubmodule f.1 f.2)
  · intro Γ k m n r s d π hs hπ Γ' k' m' n' r' s' d' π' hs' hπ'
    obtain ⟨T, hTc, hT⟩ := schwartzBruhatAverage_transfer G Γ k m n r s d π hs hπ
      Γ' k' m' n' r' s' d' π' hs' hπ'
    exact ⟨T, hTc, fun g => Subtype.ext (by rw [averagingOp_apply Γ' k' hs']; exact hT g)⟩
