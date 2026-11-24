-- Prove2me | solution 1 for GlobalTheory.PMonE.norm_one_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:47.307325+00:00
-- url     : https://prove2.me/submissions/a1507636-4ce3-4837-8b33-a534c206fc7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix
variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
omit [Fintype m]
namespace GlobalTheory.PMonE
theorem _root_.solution (i j : m) : ‖(1 : Matrix m m F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp
end GlobalTheory.PMonE
