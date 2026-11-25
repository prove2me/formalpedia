-- Prove2me | solution 1 for GlobalTheory.OmegaLebExists.J_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:05:05.940474+00:00
-- url     : https://prove2.me/submissions/5265f729-21e1-4dba-85bb-01c5e9f7f74a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsOmegaLebesgueMeasure
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.OmegaLebExists
namespace GlobalTheory.OmegaLebExists
theorem _root_.solution (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp
end GlobalTheory.OmegaLebExists
