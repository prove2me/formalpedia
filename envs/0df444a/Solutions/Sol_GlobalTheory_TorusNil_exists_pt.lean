-- Prove2me | solution 1 for GlobalTheory.TorusNil.exists_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:59.371042+00:00
-- url     : https://prove2.me/submissions/38ac4bf5-bb7e-480f-9fdd-03c62c94baaa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_spm_surjective
import Theorems.Thm_GlobalTheory_TorusNil_spm_left_surjective
import Theorems.Thm_GlobalTheory_TorusNil_pt_one

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
variable {B : Over (Spec (CommRingCat.of A))} [GrpObj B] {R : Type} [CommRing R] [Algebra A R]
  (j : sp A R ⟶ B) [IsOpenImmersion j.left] (ε : R →ₐ[A] A) (hε : spm ε ≫ j = 1)
include hε
namespace GlobalTheory.TorusNil
theorem _root_.solution {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (π : C →ₐ[A] D) (hs : Function.Surjective π) (hn : ∀ x, π x = 0 → IsNilpotent x)
    (g : sp A C ⟶ B) (hg : spm π ≫ g = 1) : ∃ φ : R →ₐ[A] C, spm φ ≫ j = g := by
  have hr : Set.range g.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := spm_left_surjective π hs hn x
    rw [← pt_one j ε hε D] at hg
    refine ⟨(spm ((Algebra.ofId A D).comp ε)).left y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, hg]
  obtain ⟨φ, hφ⟩ := spm_surjective (C := R) (D := C)
    (Over.homMk (IsOpenImmersion.lift j.left g.left hr) (by
      rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w g]))
  refine ⟨φ, ?_⟩
  rw [hφ]
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _
end GlobalTheory.TorusNil
