-- Prove2me | solution 1 for GlobalTheory.BK.TameGal.norm_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:42.09617+00:00
-- url     : https://prove2.me/submissions/6021c1bc-bdfb-4d5f-bf38-13753e3d868b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]
open GlobalTheory.BK.TameGal
variable {l}
variable [NeZero e]
namespace GlobalTheory.BK.TameGal
theorem _root_.solution (g : TameGal K l e a) (τ : ZMod a) : ‖root g τ‖ = 1 := by
  have h := congrArg norm (g.root_pow τ)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne e)).1 h
end GlobalTheory.BK.TameGal
