-- Prove2me | solution 1 for GlobalTheory.T.exists_split_etaleHermitianPair_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:11.098828+00:00
-- url     : https://prove2.me/submissions/8950bd5a-df4e-41fb-b465-cdf62f43a4c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSplitEtaleHermitianPairIsometryStatement
import Theorems.Thm_GlobalTheory_JR_exists_split_et


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  first | exact @GlobalTheory.JR.exists_split_et | exact GlobalTheory.JR.exists_split_et | (intros; apply GlobalTheory.JR.exists_split_et <;> assumption)
end _root_.GlobalTheory.T
