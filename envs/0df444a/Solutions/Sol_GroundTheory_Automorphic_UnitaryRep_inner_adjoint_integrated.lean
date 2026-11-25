-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.inner_adjoint_integrated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:20.264716+00:00
-- url     : https://prove2.me/submissions/a21446a7-23ca-4d98-bd97-4d6d223c4413

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_map_left


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
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (f : G →₁[μ] ℂ) (w v : H) :
    ⟪w, adjoint (π.integrated μ f) v⟫_ℂ = ∫ g, conj (f g) * ⟪w, π g⁻¹ v⟫_ℂ ∂μ := by
  rw [adjoint_inner_right, ← inner_conj_symm, inner_integrated, ← integral_conj]
  congr 1; ext g
  rw [_root_.map_mul, inner_conj_symm, inner_map_left]
end GroundTheory.Automorphic.UnitaryRep
