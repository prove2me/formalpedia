-- Prove2me | solution 1 for GlobalTheory.wtdiag_pyth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:16.341935+00:00
-- url     : https://prove2.me/submissions/22c55ba0-322a-4889-ab2a-4dab1e226fdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WeightNearDiagonalOperatorsBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ι : Type} (T : Finset ι) (x : ι → M)
    (h : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ⟪x i, x j⟫_ℂ = 0) (c : ι → ℂ) :
    ‖∑ i ∈ T, c i • x i‖ ^ 2 = ∑ i ∈ T, ‖c i‖ ^ 2 * ‖x i‖ ^ 2 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ← ih (fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]
    have h0 : ⟪c a • x a, ∑ i ∈ s, c i • x i⟫_ℂ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [inner_smul_left, inner_smul_right, h a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun e => ha (e ▸ hi))]
      simp
    rw [@norm_add_sq ℂ, h0, norm_smul]
    simp [mul_pow]
end GlobalTheory
