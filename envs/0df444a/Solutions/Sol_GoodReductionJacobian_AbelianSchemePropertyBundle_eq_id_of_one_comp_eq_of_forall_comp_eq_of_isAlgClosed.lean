-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3d311166-df62-53b2-885b-cf7e21b94f30

import Mathlib
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app
import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace RigidBaseBody

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (schemeHomOverComp ψ hψ (L.inv t x)) (schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left h

theorem geometricallyReduced (hA : AbelianSchemePropertyBundle R f) : GeometricallyReduced f := by
  refine ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun y => ?_⟩
  haveI := (abelianSchemePropertyBundle_fibreStr hA y).geometricallyIntegral
  exact GeometricallyReduced.geometrically_isReduced (f := RelativeGroupLaw.fibreStr f y)

theorem geometricallyConnected (hA : AbelianSchemePropertyBundle R f) : GeometricallyConnected f := by
  refine ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun y => ?_⟩
  haveI := (abelianSchemePropertyBundle_fibreStr hA y).geometricallyIntegral
  intro K _ z Z fst snd h
  haveI : IrreducibleSpace Z :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := RelativeGroupLaw.fibreStr f y) z fst snd h
  infer_instance

theorem surjective_app (hA : AbelianSchemePropertyBundle R f) (U : (Spec (CommRingCat.of R)).Opens) :
    Function.Surjective (f.app U) := by
  haveI := hA.proper
  haveI := hA.smooth
  haveI := geometricallyReduced hA
  haveI := geometricallyConnected hA
  exact (bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected f U).2

theorem comp_diff (L : RelativeGroupLaw R f) (e : A ⟶ A) (he : e ≫ f = f)
    {T : Scheme.{u}} (ψ : T ⟶ A) (t : T ⟶ Spec (CommRingCat.of R)) (hψ : ψ ≫ f = t) :
    schemeHomOverComp ψ hψ (L.mul f ⟨e, he⟩ (L.inv f ⟨𝟙 A, Category.id_comp f⟩)) =
      L.mul t ⟨ψ ≫ e, by rw [Category.assoc, he, hψ]⟩ (L.inv t ⟨ψ, hψ⟩) := by
  have h1 : schemeHomOverComp ψ hψ ⟨𝟙 A, Category.id_comp f⟩ = ⟨ψ, hψ⟩ :=
    Subtype.ext (Category.comp_id ψ)
  have h2 : schemeHomOverComp ψ hψ ⟨e, he⟩ = ⟨ψ ≫ e, by rw [Category.assoc, he, hψ]⟩ := rfl
  rw [L.mul_natural f t ψ hψ, inv_natural L f t ψ hψ, h1, h2]

end RigidBaseBody

open RigidBaseBody in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    (e : A ⟶ A) (he : e ≫ f = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ e = (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
    (hfix : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ A), x ≫ e = x) :
    e = 𝟙 A := by
  haveI := hA.proper

  set ε : Spec (CommRingCat.of R) ⟶ A := (L.one (𝟙 (Spec (CommRingCat.of R)))).1 with hε_def
  have hε : ε ≫ f = 𝟙 _ := (L.one (𝟙 (Spec (CommRingCat.of R)))).2
  set F : SchemeHomOver f f := L.mul f ⟨e, he⟩ (L.inv f ⟨𝟙 A, Category.id_comp f⟩) with hF_def

  have hgeom : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ A),
      x ≫ F.1 = (L.one (x ≫ f)).1 := by
    intro k _ _ x
    have h := congrArg Subtype.val (comp_diff L e he x (x ≫ f) rfl)
    rw [schemeHomOverComp_coe] at h
    rw [h]
    have hx : (⟨x ≫ e, by rw [Category.assoc, he]⟩ : SchemeHomOver (x ≫ f) f) = ⟨x, rfl⟩ :=
      Subtype.ext (hfix k x)
    rw [hx, L.mul_inv_cancel]

  have hgeom' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ A),
      (x ≫ f ≫ ε) ≫ F.1 = (L.one (x ≫ f)).1 := by
    intro k _ _ x
    have hψ : (x ≫ f ≫ ε) ≫ f = x ≫ f := by
      rw [Category.assoc, Category.assoc, hε, Category.comp_id]
    have h := congrArg Subtype.val (comp_diff L e he (x ≫ f ≫ ε) (x ≫ f) hψ)
    rw [schemeHomOverComp_coe] at h
    rw [h]
    have hx : (⟨(x ≫ f ≫ ε) ≫ e, by rw [Category.assoc, he, hψ]⟩ : SchemeHomOver (x ≫ f) f) =
        ⟨x ≫ f ≫ ε, hψ⟩ := by
      apply Subtype.ext
      show (x ≫ f ≫ ε) ≫ e = x ≫ f ≫ ε
      rw [Category.assoc, Category.assoc, hone]
    rw [hx, L.mul_inv_cancel]

  have hcollapse : ∀ x : A, F.1 (ε (f x)) = F.1 x := by
    intro x
    let k : Type u := AlgebraicClosure (A.residueField x)
    let xbar : Spec (CommRingCat.of k) ⟶ A :=
      Spec.map (CommRingCat.ofHom (algebraMap (A.residueField x) k)) ≫ A.fromSpecResidueField x
    have hxbar : xbar (IsLocalRing.closedPoint k) = x := by
      show (Spec.map _ ≫ A.fromSpecResidueField x) _ = x
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    have h1 := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ A => φ (IsLocalRing.closedPoint k)) (hgeom k xbar)
    have h2 := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ A => φ (IsLocalRing.closedPoint k)) (hgeom' k xbar)
    simp only [Scheme.Hom.comp_apply] at h1 h2
    rw [hxbar] at h1 h2
    rw [h1, h2]

  have hrig := AlgebraicGeometry.comp_section_comp_eq_of_isClosedMap_of_surjective_app f ε hε
    f.isClosedMap (fun U _ => surjective_app hA U) F.1 hcollapse

  have hεF : ε ≫ F.1 = ε := by
    have h := congrArg Subtype.val (comp_diff L e he ε (𝟙 _) hε)
    rw [schemeHomOverComp_coe] at h
    rw [h]
    have h1 : (⟨ε ≫ e, by rw [Category.assoc, he, hε]⟩ : SchemeHomOver (𝟙 _) f) = ⟨ε, hε⟩ :=
      Subtype.ext hone
    rw [h1, L.mul_inv_cancel]
  have hfε : f ≫ ε = (L.one f).1 := by
    have h := congrArg Subtype.val (L.one_natural (𝟙 _) f f (Category.comp_id f))
    rw [schemeHomOverComp_coe] at h
    exact h
  rw [hεF, hfε] at hrig
  have hF1 : F = L.one f := Subtype.ext hrig.symm

  letI := L.pointGroup f
  have hE : (⟨e, he⟩ : SchemeHomOver f f) = ⟨𝟙 A, Category.id_comp f⟩ := mul_inv_eq_one.mp hF1
  exact congrArg Subtype.val hE

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed (solution)
