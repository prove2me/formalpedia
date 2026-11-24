-- Prove2me | solution 1 for GlobalTheory.exists_isSymplecticFamily_of_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:04:51.040487+00:00
-- url     : https://prove2.me/submissions/ea9fc8a0-97fc-4a80-9f9c-64c92d409f22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_dualRestrict_surjective_of_isTorsionFree_quotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk

set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
  [Module R M] [Module.Finite R M] {B : LinearMap.BilinForm R M} {I : Submodule R M}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Finite ι] (hB : B.IsAlt)
    (hp : Surjective B) (hI : IsTorsionFree R (M ⧸ I)) (hiso : I ≤ B.orthogonal I)
    (v : Basis ι R I) : ∃ f : ι → M, IsSymplecticFamily B (fun i => (v i : M)) f fun _ => 1 := by
  classical
  have := Fintype.ofFinite ι
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hvv : ∀ i j, B (v i) (v j) = 0 := fun i j => hiso (v j).2 _ (v i).2
  have : ∀ i, ∃ y : M, ∀ j, B (v j) y = if j = i then 1 else 0 := fun i => by
    obtain ⟨ψ, hψ⟩ := dualRestrict_surjective_of_isTorsionFree_quotient hI (v.coord i)
    obtain ⟨y, rfl⟩ := hp ψ
    refine ⟨-y, fun j => ?_⟩
    have := LinearMap.congr_fun hψ (v j)
    rw [Submodule.dualRestrict_apply] at this
    rw [map_neg, hB.neg_eq, this]
    simp [Finsupp.single_apply]
  choose y hy using this
  have hy' : ∀ i j, B (y i) (v j) = if j = i then -1 else 0 := fun i j => by
    rw [← hB.neg_eq, hy]; split_ifs <;> simp
  refine ⟨fun i => y i - ∑ j, (if i < j then B (y i) (y j) else 0) • (v j : M), hvv,
    fun i k => ?_, fun i => ?_, fun i k hik => ?_⟩
  · simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hvv, hy, hy', mul_zero, Finset.sum_const_zero, sub_zero,
      mul_ite, mul_one, mul_neg, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h, h.not_gt]
    · simp [hB.self_eq_zero]
    · simp [h, h.not_gt, ← hB.neg_eq (y i)]
  · simp [hvv, hy, -ite_smul]
  · simp [hvv, hy, hik, -ite_smul]
end GlobalTheory
