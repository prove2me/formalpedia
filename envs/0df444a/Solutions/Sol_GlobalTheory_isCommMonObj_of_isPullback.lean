-- Prove2me | solution 1 for GlobalTheory.isCommMonObj_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:51.99882+00:00
-- url     : https://prove2.me/submissions/44c23da2-2da4-4bb6-b067-7261122c05b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Theorems.Thm_GlobalTheory_pullbackPointEquiv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
variable {S S' : Scheme.{u}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
namespace GlobalTheory
theorem _root_.solution [GrpObj G] [IsCommMonObj G]
    (h : IsPullback φ G'.hom G.hom f) :
    letI := grpObjOfIsPullback h
    IsCommMonObj G' := by
  letI := grpObjOfIsPullback h
  letI : CommMonoid ((Over.map f).obj (G' ⊗ G') ⟶ G) := Hom.commMonoid
  refine ⟨(pullbackPointEquiv h _).injective ?_⟩
  have e1 : (β_ G' G').hom ≫ μ = snd G' G' * fst G' G' := by
    rw [Hom.mul_def]
    congr 1
  have e2 : (μ : G' ⊗ G' ⟶ G') = fst G' G' * snd G' G' := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [e1, e2, pullbackPointEquiv_mul, pullbackPointEquiv_mul, mul_comm]
end GlobalTheory
