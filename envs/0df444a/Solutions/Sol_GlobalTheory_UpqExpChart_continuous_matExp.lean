-- Prove2me | solution 1 for GlobalTheory.UpqExpChart.continuous_matExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:27:47.508557+00:00
-- url     : https://prove2.me/submissions/5863406e-0a98-4444-a48e-3b1b0ad0ee6a

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
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.UpqExpChart
theorem _root_.solution : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous
end GlobalTheory.UpqExpChart
