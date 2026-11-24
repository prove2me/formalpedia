-- Prove2me | solution 1 for GlobalTheory.KerPerp.nil_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:52.463554+00:00
-- url     : https://prove2.me/submissions/be0624a0-70a0-43d4-bbfb-5888e663379a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.KerPerp
variable {O L Y : Type*} [Ring O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {bar : O → O} {EF : LinearMap.BilinForm ℤ L}
variable {hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')} {y : L →ₗ[O] Y}
variable (hadj)
variable {be : LinearMap.BilinForm ℤ Y}
variable {hadj}
variable {nn : L → L}
namespace GlobalTheory.KerPerp
theorem _root_.solution (hi : Function.Injective EF) (h : ∀ a b, -EF (nn a) b = be (y a) (y b)) {a : L}
    (ha : y a = 0) : nn a = 0 :=
  hi (LinearMap.ext fun b => by simpa [ha] using h a b)
end GlobalTheory.KerPerp
