-- Prove2me | solution 1 for GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:27.857813+00:00
-- url     : https://prove2.me/submissions/1ab114be-2beb-43e9-9611-3621f72e042e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexInfConjEqFinprodRestrictedProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G)
    (hglue : ∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i)
    (hT : ∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i)
    (hC : ∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i)
    (hCT : ∀ i, CH i ≤ TH i)
    (_hloc : ∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧
      (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0)
    (hCK : ∀ᶠ i in cofinite, CH i ≤ KH i) :
    (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C =
      ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  have hfin : {i | ¬ (p i g ∈ KH i ∧ CH i ≤ KH i)}.Finite :=
    Filter.eventually_cofinite.1 ((hcof g).and hCK)
  set S : Finset ι := hfin.toFinset with hS
  have hSn : ∀ i, i ∉ S → p i g ∈ KH i ∧ CH i ≤ KH i := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have hmem : ∀ i (y : H i), y ∈ (KH i).map (MulAut.conj (p i g)).toMonoidHom ↔
      (p i g)⁻¹ * y * p i g ∈ KH i := by
    intro i y
    rw [Subgroup.mem_map_equiv]
    simp
  have hmemG : ∀ x : G, x ∈ K.map (MulAut.conj g).toMonoidHom ↔
      ∀ i, (p i g)⁻¹ * p i x * p i g ∈ KH i := by
    intro x
    rw [Subgroup.mem_map_equiv, hK]
    simp
  have hle : ∀ i, i ∉ S → CH i ≤ TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom := by
    intro i hi y hy
    obtain ⟨h1, h2⟩ := hSn i hi
    exact ⟨hCT i hy, (hmem i y).2 (mul_mem (mul_mem (inv_mem h1) (h2 hy)) h1)⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  swap
  · intro i hi
    by_contra h
    exact hi (Subgroup.relIndex_eq_one.2 (hle i h))
  let φ : C →* (∀ i : S, CH i) :=
    { toFun := fun x i => ⟨p i x, ((hC x).1 x.2).2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hglue (fun i => if h : i ∈ S then (y ⟨i, h⟩ : H i) else 1) (by
      refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
      intro i hi
      by_contra h
      apply hi
      have h' : i ∉ S := h
      simp [h'])
    have hxC : ∀ i, p i x ∈ CH i := by
      intro i
      rw [hx]
      split_ifs with h
      · exact (y ⟨i, h⟩).2
      · exact one_mem _
    refine ⟨⟨x, (hC x).2 ⟨(hT x).2 fun i => hCT i (hxC i), hxC⟩⟩, ?_⟩
    funext i
    apply Subtype.ext
    show p i x = _
    rw [hx]
    simp
  have hcomap : (T ⊓ K.map (MulAut.conj g).toMonoidHom).subgroupOf C =
      (Subgroup.pi Set.univ (fun i : S =>
        (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).subgroupOf (CH i))).comap φ := by
    ext x
    have hx := (hC x).1 x.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Subgroup.mem_inf, hmemG]
    constructor
    · rintro ⟨h1, h2⟩ i _
      exact ⟨(hT x).1 h1 i, (hmem i _).2 (h2 i)⟩
    · intro h
      refine ⟨hx.1, fun i => ?_⟩
      by_cases hi : i ∈ S
      · exact (hmem i _).1 (h ⟨i, hi⟩ trivial).2
      · exact (hmem i _).1 (hle i hi (hx.2 i)).2
  have hpi : ∀ L : ∀ i : S, Subgroup (CH i),
      (Subgroup.pi Set.univ L).index = ∏ i, (L i).index := by
    intro L
    simp_rw [Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr
      ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hφ, hpi,
    ← Finset.prod_coe_sort S]
  rfl
end GlobalTheory
