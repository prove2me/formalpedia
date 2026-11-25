-- Prove2me | solution 1 for GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:16.435823+00:00
-- url     : https://prove2.me/submissions/ffb800a1-c534-4c5b-8c19-12cb74b8ce29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RamificationIndexEqOneOfAdjoinRangeEqTop
import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RamificationIndexEqOneOfAdjoinRangeEqTopStatement
import Theorems.Thm_GlobalTheory_ramificationIndex_eq_one_of_adjoin_range_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E K L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L] [FiniteDimensional F E] [FiniteDimensional K L], GroundTheory.LocalField.ramificationIndex F E = 1 → Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ → GroundTheory.LocalField.ramificationIndex K L = 1 := by
  first | exact @GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top | exact GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top | (intros; apply GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top <;> assumption)
end _root_.GlobalTheory.T
