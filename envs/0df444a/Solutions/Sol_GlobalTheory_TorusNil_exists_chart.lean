-- Prove2me | solution 1 for GlobalTheory.TorusNil.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:13.619875+00:00
-- url     : https://prove2.me/submissions/e5eb3fa4-c4b0-4580-b1e7-c44d34f35e02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_spm_surjective

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
namespace GlobalTheory.TorusNil
theorem _root_.solution [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R) (j : sp A R ⟶ B) (_ : IsOpenImmersion j.left)
      (ε : R →ₐ[A] A), spm ε ≫ j = 1 := by
  let e : sp A A ⟶ B := 1
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := B.left) (x := e.left (IsLocalRing.closedPoint A)) (U := ⊤) trivial
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (i ≫ B.hom)
  letI : Algebra A R := ρ.hom.toAlgebra
  let j : sp A R ⟶ B := Over.homMk i hρ.symm
  have hr : Set.range e.left ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    have := Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) e.left (U := i.opensRange) hx
    have hx' : x ∈ e.left ⁻¹ᵁ i.opensRange := by rw [this]; trivial
    exact hx'
  obtain ⟨ε, hε⟩ := spm_surjective (A := A) (C := R) (D := A)
    (Over.homMk (IsOpenImmersion.lift i e.left hr) (by
      change _ ≫ Spec.map ρ = _
      rw [hρ, IsOpenImmersion.lift_fac_assoc, Over.w e]))
  refine ⟨R, inferInstance, inferInstance, j, hi, ε, ?_⟩
  rw [hε]
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _
end GlobalTheory.TorusNil
