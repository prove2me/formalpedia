-- Prove2me | solution 1 for GlobalTheory.over_hom_eq_iff_forall_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:02.423026+00:00
-- url     : https://prove2.me/submissions/389c2c9e-f716-4c3c-942f-ab0da9e3bccc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_hom_eq_iff_forall_field
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
variable {T Y S : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution {T Y : Over S} [IsReduced T.left] [IsSeparated Y.hom]
    {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] (t : Spec (.of k) ⟶ S) (x : Over.mk t ⟶ T),
      x ≫ f = x ≫ g := by
  refine ⟨fun e _ _ _ _ => e ▸ rfl, fun H => Over.OverMorphism.ext ?_⟩
  refine (hom_eq_iff_forall_field Y.hom ((Over.w f).trans (Over.w g).symm)).mpr fun k _ x => ?_
  exact congrArg (·.left) (H k (x ≫ T.hom) (Over.homMk x rfl))
end GlobalTheory
