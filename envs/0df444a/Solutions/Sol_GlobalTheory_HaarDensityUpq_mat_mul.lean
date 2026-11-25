-- Prove2me | solution 1 for GlobalTheory.HaarDensityUpq.mat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:54:23.033623+00:00
-- url     : https://prove2.me/submissions/7723d55c-6eb9-4dda-ad80-9bee6508cda1

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDensityOriginOfAlmostHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsOmegaLebesgueMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HaarUpqHasOmegaDensity
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
open GlobalTheory GlobalTheory.HaarDensityUpq
namespace GlobalTheory.HaarDensityUpq
theorem _root_.solution {P Q : ℕ} (g h : UpqT P Q) : (g * h).mat = g.mat * h.mat := rfl
end GlobalTheory.HaarDensityUpq
