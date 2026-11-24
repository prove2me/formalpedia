-- Prove2me | solution 1 for GlobalTheory.im_latticeForm_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:00:16.887167+00:00
-- url     : https://prove2.me/submissions/01756a21-9727-4137-8e39-db4c566be710

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution (m n m' n' : ℤ) :
    (latticeForm L (m * L.ω₁ + n * L.ω₂) (m' * L.ω₁ + n' * L.ω₂)).im =
      (n * m' - m * n' : ℤ) * (latticeForm L L.ω₂ L.ω₁).im := by
  simp only [latticeForm, div_ofReal_im]
  simp
  ring
end GlobalTheory
