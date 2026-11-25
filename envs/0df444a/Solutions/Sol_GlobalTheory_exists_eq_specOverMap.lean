-- Prove2me | solution 1 for GlobalTheory.exists_eq_specOverMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:51.464812+00:00
-- url     : https://prove2.me/submissions/50a38c21-94fa-448b-a37e-906f9df345b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
namespace GlobalTheory
theorem _root_.solution (x : specOver R B ⟶ specOver R A) :
    ∃ g : A →ₐ[R] B, x = specOverMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩
end GlobalTheory
