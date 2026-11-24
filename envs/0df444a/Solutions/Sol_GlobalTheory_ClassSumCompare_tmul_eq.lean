-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.tmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:26:45.316496+00:00
-- url     : https://prove2.me/submissions/37ff632c-c35a-4783-9aef-70aaa66c9c4f

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
theorem _root_.solution (a : AdF E) (e : E) :
    (show AdE E from a ⊗ₜ[maximalRealSubfield E] e) = inclF E a * diagE E e := by
  show a ⊗ₜ[maximalRealSubfield E] e = (a ⊗ₜ[maximalRealSubfield E] (1 : E)) * ((1 : AdF E) ⊗ₜ[maximalRealSubfield E] e)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
end GlobalTheory.ClassSumCompare
