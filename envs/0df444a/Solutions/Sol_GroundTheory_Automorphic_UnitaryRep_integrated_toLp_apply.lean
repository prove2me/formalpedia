-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.integrated_toLp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:21.875974+00:00
-- url     : https://prove2.me/submissions/059831b1-cc9c-46c6-9647-01da65f34db0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_apply_eq_integral
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
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [IsFiniteMeasureOnCompacts μ]
    (f : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π.integrated μ ((f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1)
      f.hasCompactSupport).toLp f) v = ∫ g, f g • π g v ∂μ := by
  set hmem := f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1) f.hasCompactSupport
  have hae : ((hmem.toLp f : G →₁[μ] ℂ) : G → ℂ) =ᵐ[μ] f := hmem.coeFn_toLp
  have hint : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      (f.hasCompactSupport.smul_right)
  have hint' : Integrable (fun g => (hmem.toLp f : G →₁[μ] ℂ) g • π g v) μ :=
    hint.congr (hae.mono fun g hg => by simp only [hg])
  rw [π.integrated_apply_eq_integral μ _ v hint']
  exact integral_congr_ae (hae.mono fun g hg => by simp only [hg])
end GroundTheory.Automorphic.UnitaryRep
