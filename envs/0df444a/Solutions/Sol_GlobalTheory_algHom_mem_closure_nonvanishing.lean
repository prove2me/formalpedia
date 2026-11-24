-- Prove2me | solution 1 for GlobalTheory.algHom_mem_closure_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:15.051814+00:00
-- url     : https://prove2.me/submissions/e5a36ff9-e986-421b-af38-efee4b30e04d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PrincipalOpenDenseComplexPoints
import Theorems.Thm_GlobalTheory_AffinePoints_dense_nonvanishing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open AffinePoints
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (f : A) (hf : f ≠ 0) :
    {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆
      closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0} := by
  rintro _ ⟨φ, rfl, -⟩
  have h := image_closure_subset_closure_image (isEmbedding_coe (R := ℂ) (A := A) (C := ℂ)).continuous
    ⟨φ, dense_nonvanishing hf φ, rfl⟩
  refine closure_mono ?_ h
  rintro _ ⟨ψ, hψ, rfl⟩
  exact ⟨ψ, rfl, hψ⟩
end GlobalTheory
