-- Prove2me | solution 1 for GlobalTheory.T.exists_compact_preimage_norm_centralizer_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:31.755072+00:00
-- url     : https://prove2.me/submissions/04f88187-2bb9-4e73-aea5-32b856eaeb14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Theorems.Thm_GlobalTheory_NormSec_normsec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  first | exact @GlobalTheory.NormSec.normsec | exact GlobalTheory.NormSec.normsec | (intros; apply GlobalTheory.NormSec.normsec <;> assumption)
end _root_.GlobalTheory.T
