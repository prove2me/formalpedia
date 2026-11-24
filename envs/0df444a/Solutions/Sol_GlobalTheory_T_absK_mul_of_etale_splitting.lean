-- Prove2me | solution 1 for GlobalTheory.T.absK_mul_of_etale_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:44.85253+00:00
-- url     : https://prove2.me/submissions/2ad0dc84-0d3c-493a-932a-6a08e990aefe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplitting
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Theorems.Thm_GlobalTheory_JR_EtProdAbs_absK_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K), A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  first | exact @GlobalTheory.JR.EtProdAbs.absK_prod | exact GlobalTheory.JR.EtProdAbs.absK_prod | (intros; apply GlobalTheory.JR.EtProdAbs.absK_prod <;> assumption)
end _root_.GlobalTheory.T
