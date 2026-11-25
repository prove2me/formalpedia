-- Prove2me | solution 1 for GlobalTheory.KerPerp.ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:40.323679+00:00
-- url     : https://prove2.me/submissions/dacccd39-6c9a-4a2f-b269-2cf6f300ed44

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
theorem _root_.solution [Module.Projective ℤ Y] (hs : Function.Surjective EF) (v : L) :
    y v = 0 ↔ ∀ t ∈ kerPerp hadj y, EF t v = 0 := by
  refine ⟨fun hv t ht => ht v hv, fun h => (Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => ?_⟩
  obtain ⟨t, ht, hφ⟩ := exists_of_dual (hadj := hadj) (y := y) hs φ
  rw [← hφ, h t ht, neg_zero]
end GlobalTheory.KerPerp
