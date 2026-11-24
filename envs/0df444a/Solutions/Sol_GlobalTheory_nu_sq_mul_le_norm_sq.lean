-- Prove2me | solution 1 for GlobalTheory.nu_sq_mul_le_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:14.296861+00:00
-- url     : https://prove2.me/submissions/074e2ffd-d009-4c4f-99de-23c44b07e1a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_sq_comb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module Matrix
open scoped InnerProductSpace TensorProduct MatrixOrder ComplexOrder
open GlobalTheory
open ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2 ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ)
    (j : Fin d) : nu b c j ^ 2 * ‖gs b j‖ ^ 2 ≤ ‖∑ l, c l • b l‖ ^ 2 := by
  rw [norm_sq_comb b hb c]
  exact single_le_sum (f := fun j => nu b c j ^ 2 * ‖gs b j‖ ^ 2)
    (fun k _ => by positivity) (mem_univ j)
end GlobalTheory
