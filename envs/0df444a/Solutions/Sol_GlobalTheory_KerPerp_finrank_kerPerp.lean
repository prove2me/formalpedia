-- Prove2me | solution 1 for GlobalTheory.KerPerp.finrank_kerPerp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:08:25.877795+00:00
-- url     : https://prove2.me/submissions/2368e671-b70b-4acd-80ee-683ee32d261d

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
namespace GlobalTheory.KerPerp
theorem _root_.solution [Module.Free ℤ Y] [Module.Finite ℤ Y] (hb : Function.Bijective EF)
    (hy : Function.Surjective y) : Module.finrank ℤ (kerPerp hadj y) = Module.finrank ℤ Y := by
  rw [(equivDual hadj hb hy).finrank_eq, Module.finrank_linearMap_self]
end GlobalTheory.KerPerp
