-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.coeFn_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:15.450803+00:00
-- url     : https://prove2.me/submissions/4e6ae5a5-3c23-49bf-ab7a-680c4d6bec09

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated

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
omit [OpensMeasurableSpace G]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [μ.IsInvInvariant] (f : G →₁[μ] ℂ) :
    (involution μ f : G → ℂ) =ᵐ[μ] fun g => conj (f g⁻¹) := by
  have h1 := (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp
    (Lp.compMeasurePreserving (fun g => g⁻¹) (Measure.measurePreserving_inv μ) f)
  have h2 := Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_inv μ)
  filter_upwards [h1, h2] with g hg1 hg2
  rw [involution, hg1, hg2]
  rfl
end GroundTheory.Automorphic.UnitaryRep
