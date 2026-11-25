-- Prove2me | solution 1 for GlobalTheory.UpqExpChart.mat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:45.344558+00:00
-- url     : https://prove2.me/submissions/83e4a68e-66fc-4f83-bdd3-c1e94fdb140f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.UpqExpChart
namespace GlobalTheory.UpqExpChart
theorem _root_.solution {P Q : ℕ} (g : UpqT P Q) :
    (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2
end GlobalTheory.UpqExpChart
