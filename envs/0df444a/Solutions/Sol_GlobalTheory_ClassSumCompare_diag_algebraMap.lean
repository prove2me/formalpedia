-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.diag_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:26:42.729559+00:00
-- url     : https://prove2.me/submissions/5ba1069f-b0e7-44db-a66a-6e38cc86b7f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumCompare
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.ClassSumCompare
theorem _root_.solution (x : maximalRealSubfield E) :
    diagE E (algebraMap _ E x) = inclF E (algebraMap _ (AdF E) x) := by
  show (1 : AdF E) ⊗ₜ[maximalRealSubfield E] (algebraMap _ E x) = (algebraMap _ (AdF E) x) ⊗ₜ[maximalRealSubfield E] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
end GlobalTheory.ClassSumCompare
