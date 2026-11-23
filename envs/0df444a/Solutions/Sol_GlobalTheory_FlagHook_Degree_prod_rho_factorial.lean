-- Prove2me | solution 1 for GlobalTheory.FlagHook.Degree.prod_rho_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:51.381076+00:00
-- url     : https://prove2.me/submissions/4789db75-d794-426d-b8fe-83d02d0dc59b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_AltCoeffRho
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde

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
theorem _root_.solution (N : ℕ) :
    ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) = ∏ m ∈ range N, (m.factorial : ℝ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ((N - 1 - i).factorial : ℝ)) N,
    Finset.prod_range_reflect (fun i => (i.factorial : ℝ)) N]
end GlobalTheory.FlagHook.Degree
