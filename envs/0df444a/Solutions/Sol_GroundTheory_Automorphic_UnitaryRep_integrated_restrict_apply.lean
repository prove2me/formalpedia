-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.integrated_restrict_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:26.270363+00:00
-- url     : https://prove2.me/submissions/36712922-ee9b-4c02-97ac-36bd98119648

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_integrated_of_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_subtypeL_mem_intertwiners


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (j : J) (v : V j) :
    (((π.restrict (V j) (hinv j)).integrated μ f v : V j) : H) = π.integrated μ f (v : H) := by
  have := comp_integrated_of_mem_intertwiners (π.restrict (V j) (hinv j)) μ
    (subtypeL_mem_intertwiners π (V j) (hinv j)) f
  exact congrArg (fun T : V j →L[ℂ] H => T v) this
end GroundTheory.Automorphic.UnitaryRep
