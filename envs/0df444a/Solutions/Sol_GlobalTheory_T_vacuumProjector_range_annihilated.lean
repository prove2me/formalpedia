-- Prove2me | solution 1 for GlobalTheory.T.vacuumProjector_range_annihilated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:53.49381+00:00
-- url     : https://prove2.me/submissions/9fdcf521-4351-410d-969f-6d18ab2f861c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VacuumProjectorRangeAnnihilated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VacuumProjectorRangeAnnihilatedStatement
import Theorems.Thm_GlobalTheory_Mem_Lift_VacAnn_proj_annihilated


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ (h : IsHeis (omJ J) ρ) (x : B) (z : V), dH ρ z (proj h x) + I • dH ρ (J z) (proj h x) = 0 := by
  first | exact @GlobalTheory.Mem.Lift.VacAnn.proj_annihilated | exact GlobalTheory.Mem.Lift.VacAnn.proj_annihilated | (intros; apply GlobalTheory.Mem.Lift.VacAnn.proj_annihilated <;> assumption)
end _root_.GlobalTheory.T
