-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.mulVec_mem_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:46.019914+00:00
-- url     : https://prove2.me/submissions/93652f38-c7b6-4c6d-83f2-1883a3cab02e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Theorems.Thm_GroundTheory_Automorphic_Measures_mem_box

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
theorem _root_.solution {A : Matrix ι ι F} (hA : ∀ i j, A i j ∈ 𝒪[F]) {x : ι → F}
    (hx : x ∈ box F ι) : A.mulVec x ∈ box F ι :=
  mem_box.2 fun i => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (mem_box.1 hx j)
end GroundTheory.Automorphic.Measures
