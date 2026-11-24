-- Prove2me | solution 1 for GlobalTheory.tprod_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:49.081525+00:00
-- url     : https://prove2.me/submissions/8ca5f19b-18c0-4497-a1f7-99fc7599a09b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_dual_apply_smul_comm
import Theorems.Thm_GlobalTheory_exists_sum_dual_apply_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution [Module.Invertible A M] {ι : Type*} [Finite ι] (x : ι → M)
    (σ : Equiv.Perm ι) :
    PiTensorProduct.tprod A (s := fun _ ↦ M) (fun i ↦ x (σ i))
      = PiTensorProduct.tprod A (s := fun _ ↦ M) x := by
  classical
  cases nonempty_fintype ι
  have key : ∀ (f : Module.Dual A M) (m : M) (x : ι → M),
      f m ^ Fintype.card ι • PiTensorProduct.tprod A (s := fun _ ↦ M) x =
        (∏ i, f (x i)) • PiTensorProduct.tprod A (s := fun _ ↦ M) (fun _ ↦ m) := by
    intro f m x
    rw [← MultilinearMap.map_smul_univ, ← Finset.card_univ, ← Finset.prod_const,
      ← MultilinearMap.map_smul_univ]
    simp only [dual_apply_smul_comm f m]
  rw [← sub_eq_zero]
  set d := PiTensorProduct.tprod A (s := fun _ ↦ M) (fun i ↦ x (σ i))
      - PiTensorProduct.tprod A (s := fun _ ↦ M) x with hd
  let I : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A _ d)
  have hI : I.radical = ⊤ := by
    obtain ⟨s, hs⟩ := exists_sum_dual_apply_eq_one A M
    rw [Ideal.eq_top_iff_one, ← hs]
    refine sum_mem fun p _ ↦ ⟨Fintype.card ι, ?_⟩
    change p.1 p.2 ^ Fintype.card ι • d = 0
    rw [hd, smul_sub, key, key, Equiv.prod_comp σ (fun i ↦ p.1 (x i)), sub_self]
  rw [Ideal.radical_eq_top, Ideal.eq_top_iff_one] at hI
  simpa [I] using hI
end GlobalTheory
