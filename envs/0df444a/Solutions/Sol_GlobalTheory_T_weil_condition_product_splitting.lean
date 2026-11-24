-- Prove2me | solution 1 for GlobalTheory.T.weil_condition_product_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:04.383155+00:00
-- url     : https://prove2.me/submissions/131258ed-6e0e-4c28-ab05-7b475155f227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplittingStatement
import Theorems.Thm_GlobalTheory_JR_WeilProd_weilAt_prod


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L), IsSplitting A A₁ A₂ eK eL → WeilAt A₁ → WeilAt A₂ → WeilAt A := by
  first | exact @GlobalTheory.JR.WeilProd.weilAt_prod | exact GlobalTheory.JR.WeilProd.weilAt_prod | (intros; apply GlobalTheory.JR.WeilProd.weilAt_prod <;> assumption)
end _root_.GlobalTheory.T
