-- Prove2me | solution 1 for GlobalTheory.KerPerp.mem_kerPerp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:57.256576+00:00
-- url     : https://prove2.me/submissions/85304cea-f04e-4fb5-b31c-e652cc51ed5a

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
namespace GlobalTheory.KerPerp
theorem _root_.solution {t : L} : t ∈ kerPerp hadj y ↔ ∀ v, y v = 0 → EF t v = 0 := Iff.rfl
end GlobalTheory.KerPerp
