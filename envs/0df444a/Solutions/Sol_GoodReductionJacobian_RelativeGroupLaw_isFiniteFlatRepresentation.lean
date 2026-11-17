-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isFiniteFlatRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:53.916422+00:00
-- url     : https://prove2.me/submissions/472667de-d7f7-41c4-9ceb-5430ef55c462

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_flat_of_grpObj_over_spec
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_of_ratLocalizedAt
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

open scoped CategoryTheory.MonObj

namespace GoodReductionJacobian.RelativeGroupLaw

/-- A finite-flat commutative relative group law with the prescribed geometric
point identification supplies a finite-flat model of the restricted action. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {W : Type} [AddCommGroup W]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → W → W)
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of (GaloisRep.ratLocalizedAt p)))
    [IsFinite f] [Flat f]
    (L : GoodReductionJacobian.RelativeGroupLaw (GaloisRep.ratLocalizedAt p) f)
    (hc : L.IsCommutative)
    (e : W ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) f)
    (he_add : ∀ x y, e (x + y) = L.mul _ (e x) (e y))
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : W),
      (e (act σ x)).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (e x).1) :
    groupCohomology.IsFiniteFlatRepresentation p
      (fun σ => act (localGaloisToGlobal p σ)) := by
  letI := L.grpObjOverMk
  letI : IsCommMonObj (Over.mk f) :=
    L.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr hc
  letI : IsFinite (Over.mk f).hom := ‹IsFinite f›
  letI : Flat (Over.mk f).hom := ‹Flat f›
  obtain ⟨H, hH, hHopf, hfinite, hflat, hcocomm, E, hE_mul, hE_nat⟩ :=
    AlgebraicGeometry.exists_hopfAlgebra_flat_of_grpObj_over_spec
      (GaloisRep.ratLocalizedAt p) (Over.mk f)
  letI := hH
  letI := hHopf
  letI := hfinite
  letI := hflat
  letI := hcocomm
  let e0 : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ W :=
    ((E (AlgebraicClosure ℚ)).trans
      (GoodReductionJacobian.overHomEquivSchemeHomOver _ f)).trans e.symm
  have he0 (q : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :
      e (e0 q) = overHomToSchemeHomOver (E (AlgebraicClosure ℚ) q) := by
    exact e.apply_symm_apply _
  apply HopfAlgebra.exists_finiteFlat_padicInt_of_ratLocalizedAt p act H e0
  · intro a b
    apply e.injective
    rw [he0, he_add, he0, he0]
    rw [hE_mul]
    exact L.overHomToSchemeHomOver_mul _ _ _
  · intro σ a b hab
    let σR : AlgebraicClosure ℚ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ :=
      { toRingHom := σ.toRingHom
        commutes' := fun r => by
          change σ (algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ)) =
            algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ)
          exact σ.commutes (r : ℚ) }
    have hb : b = WithConv.toConv (σR.comp a.ofConv) := by
      apply WithConv.ofConv_injective
      ext h
      exact hab h
    apply e.injective
    apply Subtype.ext
    rw [he0, he_act, he0]
    change (E (AlgebraicClosure ℚ) b).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (E (AlgebraicClosure ℚ) a).left
    rw [hb]
    exact hE_nat (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) σR a

end GoodReductionJacobian.RelativeGroupLaw
