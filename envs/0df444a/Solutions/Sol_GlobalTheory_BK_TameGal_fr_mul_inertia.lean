-- Prove2me | solution 1 for GlobalTheory.BK.TameGal.fr_mul_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:54.687233+00:00
-- url     : https://prove2.me/submissions/2e5ef35d-9d62-4a8a-9bdb-9276c6742183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]
open GlobalTheory.BK.TameGal
variable {l}
namespace GlobalTheory.BK.TameGal
theorem _root_.solution (ζ : rootsOfUnity e K) :
    (fr : TameGal K l e a) * inertia ζ = inertia (ζ ^ l) * fr := by
  ext1
  · simpa [-map_pow, frobAut] using powL_one (a := a) l ζ
  · simp [-map_pow]
end GlobalTheory.BK.TameGal
