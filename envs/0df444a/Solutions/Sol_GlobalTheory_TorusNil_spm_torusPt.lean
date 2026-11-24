-- Prove2me | solution 1 for GlobalTheory.TorusNil.spm_torusPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:11.986905+00:00
-- url     : https://prove2.me/submissions/d9ed2988-593c-4c38-bbcb-ea208629022f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_torusPt_fst
import Theorems.Thm_GlobalTheory_TorusNil_ringHom_ext_int_torus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable (A) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusNil
theorem _root_.solution {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (ψ : C →ₐ[A] D) (χ : Multiplicative X →* C) :
    spm ψ ≫ torusPt A X χ = torusPt A X ((ψ : C →* D).comp χ) := by
  obtain ⟨φ, h1, h2⟩ := torusPt_fst A X χ
  obtain ⟨φ', h1', h2'⟩ := torusPt_fst A X ((ψ : C →* D).comp χ)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · refine Eq.trans ?_ h2'.symm
    refine (Category.assoc _ _ _).trans ((congrArg ((spm ψ).left ≫ ·) h2).trans ?_)
    refine (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ.toRingHom)).symm.trans ?_
    rw [← CommRingCat.ofHom_comp]
    congr 2
    apply ringHom_ext_int_torus
    intro y
    simp [h1, h1']
  · exact (Over.w _).trans (Over.w _).symm
end GlobalTheory.TorusNil
