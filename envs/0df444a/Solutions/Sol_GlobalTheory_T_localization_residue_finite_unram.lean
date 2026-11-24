-- Prove2me | solution 1 for GlobalTheory.T.localization_residue_finite_unram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:25.634797+00:00
-- url     : https://prove2.me/submissions/d4dca893-106d-4ce4-aa7d-fb457eb8ffec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationResidueFiniteUnram
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationResidueFiniteUnramStatement
import Theorems.Thm_GlobalTheory_residue_atMaximal_finite_formallyUnramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).Finite ∧ ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).FormallyUnramified := by
  first | exact @GlobalTheory.residue_atMaximal_finite_formallyUnramified | exact GlobalTheory.residue_atMaximal_finite_formallyUnramified | (intros; apply GlobalTheory.residue_atMaximal_finite_formallyUnramified <;> assumption)
end _root_.GlobalTheory.T
