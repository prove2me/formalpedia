-- Prove2me | solution 1 for GlobalTheory.FiniteAbelianWeights.baseChange_avg_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:07:57.333414+00:00
-- url     : https://prove2.me/submissions/16fec481-ecaa-4f02-92f4-0396653d7d57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open TensorProduct
open GlobalTheory
open GlobalTheory.FiniteAbelianWeights
variable {o : Type} [CommRing o] {T : Type} [CommGroup T]
  {M : Type} [AddCommGroup M] [Module o M]
variable [Fintype T] (ρ : Representation o T M) (u : o)
namespace GlobalTheory.FiniteAbelianWeights
theorem _root_.solution (hu : u * (Fintype.card T : o) = 1) (A : Type) [CommRing A]
    [Algebra o A] (c : T →* oˣ) (x : A ⊗[o] M)
    (hx : ∀ t, (ρ t).baseChange A x = algebraMap o A (c t) • x) :
    (avg ρ u c).baseChange A x = x := by
  have h : ∀ y : A ⊗[o] M, (avg ρ u c).baseChange A y
      = u • ∑ t : T, (((c t)⁻¹ : oˣ) : o) • (ρ t).baseChange A y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [avg_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    | add y z hy hz => simp only [map_add, hy, hz, smul_add, Finset.sum_add_distrib]
  rw [h]
  simp only [hx, algebraMap_smul, smul_smul, Units.inv_mul, one_smul, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul o, smul_smul, hu, one_smul]
end GlobalTheory.FiniteAbelianWeights
