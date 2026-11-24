-- Prove2me | solution 1 for GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:08:11.284981+00:00
-- url     : https://prove2.me/submissions/c4bf9b20-d08a-4194-aece-1cffb7b5daac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsOneEtaleAlgebraMulInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsOneEtaleAlgebraMulInvariantStatement
import Theorems.Thm_GlobalTheory_JR_MulInv_exists_nhds_one_mul_invariant


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ : A.L → ℂ), IsTest φ → ∃ U ∈ 𝓝 (1 : A.K), ∀ s ∈ U, ∀ s' ∈ U, s * s' = 1 → ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
  first | exact @GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant | exact GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant | (intros; apply GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant <;> assumption)
end _root_.GlobalTheory.T
