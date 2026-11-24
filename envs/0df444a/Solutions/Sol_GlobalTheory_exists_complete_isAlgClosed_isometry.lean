-- Prove2me | solution 1 for GlobalTheory.exists_complete_isAlgClosed_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:09.133435+00:00
-- url     : https://prove2.me/submissions/a3c54f91-a871-424f-ad01-053f7396f962

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_isAlgClosed_of_denseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (i : K →+* C), ∀ x, ‖i x‖ = ‖x‖ := by
  let K₁ := UniformSpace.Completion K
  letI : NontriviallyNormedField K₁ := completionNontriviallyNormedField K
  haveI : IsUltrametricDist K₁ := IsUltrametricDist.of_normedAlgebra K
  let K₂ := AlgebraicClosure K₁
  letI : NontriviallyNormedField K₂ := spectralNorm.nontriviallyNormedField K₁ K₂
  letI : NormedAlgebra K₁ K₂ := spectralNorm.normedAlgebra K₁ K₂
  haveI : IsUltrametricDist K₂ := IsUltrametricDist.of_normedAlgebra K₁
  let C := UniformSpace.Completion K₂
  letI : NontriviallyNormedField C := completionNontriviallyNormedField K₂
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra K₂
  haveI : IsAlgClosed C :=
    isAlgClosed_of_denseRange (K := K₂) UniformSpace.Completion.denseRange_coe
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap K₂ C).comp ((algebraMap K₁ K₂).comp (algebraMap K K₁)), fun x => ?_⟩
  have h₁ : ∀ y : K₂, ‖algebraMap K₂ C y‖ = ‖y‖ := fun y => UniformSpace.Completion.norm_coe y
  have h₂ : ∀ y : K₁, ‖algebraMap K₁ K₂ y‖ = ‖y‖ := fun y => spectralNorm_extends y
  have h₃ : ∀ y : K, ‖algebraMap K K₁ y‖ = ‖y‖ := fun y => UniformSpace.Completion.norm_coe y
  rw [RingHom.comp_apply, RingHom.comp_apply, h₁, h₂, h₃]
end GlobalTheory
