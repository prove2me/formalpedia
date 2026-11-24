-- Prove2me | solution 1 for GlobalTheory.UpqTopology.left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:01.365339+00:00
-- url     : https://prove2.me/submissions/418ccf03-6eae-40e6-95b2-7889dc323fc4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Theorems.Thm_GlobalTheory_UpqTopology_jpq_sq
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.UpqTopology
variable {P Q : ℕ}
namespace GlobalTheory.UpqTopology
theorem _root_.solution {u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) : Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, jpq_sq]
end GlobalTheory.UpqTopology
