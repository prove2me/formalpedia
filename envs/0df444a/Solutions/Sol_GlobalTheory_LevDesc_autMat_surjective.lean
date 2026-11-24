-- Prove2me | solution 1 for GlobalTheory.LevDesc.autMat_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:21.725674+00:00
-- url     : https://prove2.me/submissions/c32378c6-3f1c-4eee-a2c7-d3886f394f6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
import Theorems.Thm_GlobalTheory_LevDesc_autMat_mulVec

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
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] {r p : ℕ} (e : M ≃+ (Fin r → ZMod p))
namespace GlobalTheory.LevDesc
theorem _root_.solution (hO : ∀ a : O, ∃ n : ℤ, ∀ x : M, a • x = n • x) :
    Function.Surjective (autMat (O := O) e) := fun g => by
  let f : M ≃+ M := e.trans ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toAddEquiv.trans e.symm)
  refine ⟨f.toLinearEquiv fun a x => ?_, Units.ext (Matrix.ext_of_mulVec_single fun i => ?_)⟩
  · obtain ⟨n, hn⟩ := hO a
    rw [hn, hn, map_zsmul]
  · rw [← e.apply_symm_apply (Pi.single i 1), autMat_mulVec]
    simp [f]
end GlobalTheory.LevDesc
