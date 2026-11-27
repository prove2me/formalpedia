-- Prove2me | solution 1 for GlobalTheory.hasProd_sigmaProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:27.477932+00:00
-- url     : https://prove2.me/submissions/6d8f8495-04b7-45d9-bf6e-fd0e5c202bd9

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
theorem _root_.solution (z : ℂ) :
    HasProd (fun l : L.lattice => sigmaFactor l z) (sigmaProd L z) :=
  (hasProdLocallyUniformlyOn_sigmaProd L).hasProd (Set.mem_univ z)
end GlobalTheory
