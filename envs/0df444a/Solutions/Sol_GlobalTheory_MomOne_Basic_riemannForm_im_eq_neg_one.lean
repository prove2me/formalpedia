-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.riemannForm_im_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:02:28.334556+00:00
-- url     : https://prove2.me/submissions/10c62a99-cdba-4ca4-abc9-bda38919bfa0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
namespace GlobalTheory.MomOne.Basic
theorem _root_.solution {d : ℕ} (hd : 0 < d) : (h1 d 1 (wK d)).im = -1 := by
  have hs : Real.sqrt d ≠ 0 := by positivity
  rw [h1, Complex.im_ofReal_mul, one_mul, Complex.conj_im]
  have : (wK d).im = Real.sqrt d / 2 := by simp [wK]
  rw [this]
  field_simp
end GlobalTheory.MomOne.Basic
