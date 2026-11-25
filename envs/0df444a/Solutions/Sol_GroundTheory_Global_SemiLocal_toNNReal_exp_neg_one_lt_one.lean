-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.toNNReal_exp_neg_one_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:00.767229+00:00
-- url     : https://prove2.me/submissions/09587f76-cde9-4ad0-8e90-dd886dd0df05

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter
noncomputable section
open GroundTheory.Global.SemiLocal
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) :
    ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) < 1 := by
  rw [← NNReal.coe_one, NNReal.coe_lt_coe,
    toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)]
  rw [← exp_zero, exp_lt_exp]
  norm_num
end GroundTheory.Global.SemiLocal
