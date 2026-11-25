-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.transvection_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:28.150832+00:00
-- url     : https://prove2.me/submissions/d31ff3f3-a4bf-45e9-be0d-adf79160c614

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus

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
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {i j : ι} {c : F} (hc : c ∈ 𝒪[F]) (a b : ι) :
    Matrix.transvection i j c a b ∈ 𝒪[F] := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  refine Subring.add_mem _ ?_ ?_
  · split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · split_ifs
    · exact hc
    · exact Subring.zero_mem _
end GroundTheory.Automorphic.Measures
