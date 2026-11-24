-- Prove2me | solution 1 for GlobalTheory.UpqTopology.range_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:03.57631+00:00
-- url     : https://prove2.me/submissions/8944df1c-6cbf-4fc3-a45c-c3c01af95750

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Theorems.Thm_GlobalTheory_UpqTopology_left_inv
import Theorems.Thm_GlobalTheory_UpqTopology_mat_unitary
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
theorem _root_.solution : Set.range (UpqT.mat (P := P) (Q := Q)) =
    {u | uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q} := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact mat_unitary b
  · intro h
    exact ⟨(⟨⟨u, Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q, mul_eq_one_comm.1 (left_inv h), left_inv h⟩, h⟩ :
      Formalism.UG.Upq P Q), rfl⟩
end GlobalTheory.UpqTopology
