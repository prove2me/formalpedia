-- Prove2me | solution 1 for GlobalTheory.FlagHook.Degree.eval_detE_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:58.774473+00:00
-- url     : https://prove2.me/submissions/9dbcc007-337f-4fc9-87ae-689d73162833

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde
import Theorems.Thm_GlobalTheory_FlagHook_Degree_prod_rho_factorial
import Theorems.Thm_GlobalTheory_FlagHook_Degree_signed_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset GlobalTheory.FlagHook Formalism.DegreeFormula
noncomputable section
open GlobalTheory GlobalTheory.FlagHook GlobalTheory.FlagHook.Degree
namespace GlobalTheory.FlagHook.Degree
theorem _root_.solution (N : ℕ) (v : Fin N → ℝ) :
    eval v (detE (rho N)) = (∏ a : Fin N, ∏ b ∈ Ioi a, (v a - v b)) / ∏ m ∈ range N, (m.factorial : ℝ) := by
  rw [← signed_sum, ← prod_rho_factorial, detE, ← Matrix.det_transpose, Matrix.det_apply', map_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_prod, mul_div_assoc,
    ← Equiv.prod_comp σ (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ)), ← Finset.prod_div_distrib]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [rho, div_eq_inv_mul]
end GlobalTheory.FlagHook.Degree
