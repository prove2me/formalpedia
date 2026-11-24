-- Prove2me | solution 1 for GlobalTheory.UpqTopology.upq_lcsc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:01.485886+00:00
-- url     : https://prove2.me/submissions/6c1ba11b-43c6-49b9-90f0-4a8b31fb847f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Theorems.Thm_GlobalTheory_UpqTopology_isClosedEmbedding_mat
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
theorem _root_.solution : ∀ P Q : ℕ, IsTopologicalGroup (UpqT P Q) ∧ T2Space (UpqT P Q) ∧
    LocallyCompactSpace (UpqT P Q) ∧ SecondCountableTopology (UpqT P Q) ∧ BorelSpace (UpqT P Q) ∧
    Topology.IsClosedEmbedding (UpqT.mat : UpqT P Q → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
  intro P Q
  have : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact ⟨inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q)), isClosedEmbedding_mat.isEmbedding.t2Space,
    isClosedEmbedding_mat.locallyCompactSpace, isClosedEmbedding_mat.isEmbedding.secondCountableTopology,
    ⟨rfl⟩, isClosedEmbedding_mat⟩
end GlobalTheory.UpqTopology
