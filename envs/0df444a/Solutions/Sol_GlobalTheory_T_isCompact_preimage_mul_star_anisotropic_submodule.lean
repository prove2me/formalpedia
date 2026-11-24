-- Prove2me | solution 1 for GlobalTheory.T.isCompact_preimage_mul_star_anisotropic_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:06.086154+00:00
-- url     : https://prove2.me/submissions/bc02a634-e81e-4f34-a888-44aad402dcd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactPreimageMulStarAnisotropicSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactPreimageMulStarAnisotropicSubmoduleStatement
import Theorems.Thm_GlobalTheory_mul_star_anisotropic_proper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  first | exact @GlobalTheory.mul_star_anisotropic_proper | exact GlobalTheory.mul_star_anisotropic_proper | (intros; apply GlobalTheory.mul_star_anisotropic_proper <;> assumption)
end _root_.GlobalTheory.T
