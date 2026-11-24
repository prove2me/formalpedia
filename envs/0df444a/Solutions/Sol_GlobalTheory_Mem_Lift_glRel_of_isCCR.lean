-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.glRel_of_isCCR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:27.622403+00:00
-- url     : https://prove2.me/submissions/39a8978b-77a1-4167-9594-fc92d1075a10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlRelOfCanonicalCommutationRelations
import Theorems.Thm_GlobalTheory_Mem_Lift_IsCCR_comm_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift
namespace GlobalTheory.Mem.Lift
theorem _root_.solution (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A) (h : IsCCR x d) :
    Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧
      Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  refine ⟨fun i j k l => ?_, fun a b c e => ?_⟩
  · beta_reduce
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun s t => x (k, s) * d (l, s) * (x (i, t) * d (j, t))),
      ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    congr 1
    · by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    · by_cases hli : l = i
      · simp [hli]
      · simp [hli, Ne.symm hli]
  · beta_reduce
    rw [neg_mul_neg, neg_mul_neg, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun s t => x (s, e) * d (s, c) * (x (t, b) * d (t, a))), ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    by_cases hbc : b = c <;> by_cases hea : e = a <;> simp [hbc, hea, sub_eq_neg_add, add_comm]
end GlobalTheory.Mem.Lift
