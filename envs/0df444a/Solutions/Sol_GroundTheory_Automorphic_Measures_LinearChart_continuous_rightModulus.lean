-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.LinearChart.continuous_rightModulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:27.676179+00:00
-- url     : https://prove2.me/submissions/098202a4-0234-4f18-b3fb-43c077578198

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Theorems.Thm_GroundTheory_Automorphic_exists_compactOpenSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
open GroundTheory.Automorphic.Measures.LinearChart
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] (C : LinearChart F ι G)
variable (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]
variable [LocallyCompactSpace G]
variable [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic.Measures.LinearChart
theorem _root_.solution : Continuous C.rightModulus := by
  obtain ⟨V, hV⟩ := exists_compactOpenSubgroup (G := G)
  exact continuous_of_eq_one_on_openSubgroup C.rightModulusHom V fun v hv =>
    (C.modulus_eq_one_of_mem hV hv).2
end GroundTheory.Automorphic.Measures.LinearChart
