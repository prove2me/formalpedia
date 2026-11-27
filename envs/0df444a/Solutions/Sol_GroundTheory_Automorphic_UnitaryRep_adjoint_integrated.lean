-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.adjoint_integrated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:42.215802+00:00
-- url     : https://prove2.me/submissions/fa4b625a-7d81-4b4c-b0cb-8d9c5b139f7a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_adjoint_integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coeFn_involution
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply



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
theorem _root_.solution [μ.IsInvInvariant] (f : G →₁[μ] ℂ) :
    adjoint (π.integrated μ f) = π.integrated μ (involution μ f) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [inner_adjoint_integrated, inner_integrated]
  rw [integral_congr_ae ((coeFn_involution μ f).mono fun g hg =>
    show (involution μ f) g * ⟪w, π g v⟫_ℂ = conj (f g⁻¹) * ⟪w, π g v⟫_ℂ by rw [hg])]
  rw [← integral_inv_eq_self (fun g => conj (f g⁻¹) * ⟪w, π g v⟫_ℂ) μ]
  simp only [inv_inv]
end GroundTheory.Automorphic.UnitaryRep
