-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.map_comp_integrated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:30.132469+00:00
-- url     : https://prove2.me/submissions/f54b47d9-e89c-4d43-bd33-7d13eb9b2b2a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coeFn_leftTranslate
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_map_left
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_map_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable [IsTopologicalGroup G] [BorelSpace G]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [μ.IsMulLeftInvariant] (h : G) (f : G →₁[μ] ℂ) :
    π h ∘L π.integrated μ f = π.integrated μ (leftTranslate μ h f) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [comp_apply, inner_map_right, inner_integrated, inner_integrated]
  rw [integral_congr_ae ((coeFn_leftTranslate μ h f).mono fun g hg =>
    show (leftTranslate μ h f) g * ⟪w, π g v⟫_ℂ = f (h⁻¹ * g) * ⟪w, π g v⟫_ℂ by rw [hg])]
  rw [← integral_mul_left_eq_self (fun g => f (h⁻¹ * g) * ⟪w, π g v⟫_ℂ) h]
  congr 1; ext g
  rw [inv_mul_cancel_left, inner_map_left, inv_inv, map_mul_apply]
end GroundTheory.Automorphic.UnitaryRep
