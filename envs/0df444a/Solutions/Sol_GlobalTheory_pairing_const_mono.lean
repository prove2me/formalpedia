-- Prove2me | solution 1 for GlobalTheory.pairing_const_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:53.62257+00:00
-- url     : https://prove2.me/submissions/07078a7a-3e2e-452d-a0d4-1d906bf18957

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent

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
variable {X : Type*} [AddCommGroup X] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution {d g : ℕ} (h : d ≤ g) :
    (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) ≤ (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) := by
  have : (d : ℝ) ≤ g := by exact_mod_cast h
  gcongr; norm_num
end GlobalTheory
