-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ddde7431-7996-5934-a25a-531cd07c6737

import Mathlib
import Definitions.Def_JacJ1Iface
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mKcHomRigidBase

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left h

noncomputable def diffPt (L : RelativeGroupLaw R f) (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) :
    SchemeHomOver f f :=
  L.mul f (L.mul f ⟨φ, hφ⟩ (L.inv f ⟨ψ, hψ⟩)) ⟨𝟙 A, Category.id_comp f⟩

theorem comp_diffPt (L : RelativeGroupLaw R f) (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    {T : Scheme.{u}} (x : T ⟶ A) (t : T ⟶ Spec (CommRingCat.of R)) (hx : x ≫ f = t) :
    GoodReductionJacobian.schemeHomOverComp x hx (diffPt L φ ψ hφ hψ) =
      L.mul t (L.mul t ⟨x ≫ φ, by rw [Category.assoc, hφ, hx]⟩ (L.inv t ⟨x ≫ ψ, by rw [Category.assoc, hψ, hx]⟩))
        ⟨x, hx⟩ := by
  have h1 : GoodReductionJacobian.schemeHomOverComp x hx ⟨𝟙 A, Category.id_comp f⟩ = ⟨x, hx⟩ :=
    Subtype.ext (Category.comp_id x)
  have hφ' : GoodReductionJacobian.schemeHomOverComp x hx ⟨φ, hφ⟩ = ⟨x ≫ φ, by rw [Category.assoc, hφ, hx]⟩ := rfl
  have hψ' : GoodReductionJacobian.schemeHomOverComp x hx ⟨ψ, hψ⟩ = ⟨x ≫ ψ, by rw [Category.assoc, hψ, hx]⟩ := rfl
  unfold diffPt
  rw [L.mul_natural f t x hx, L.mul_natural f t x hx, inv_natural L f t x hx, h1, hφ', hψ']

theorem comp_diffPt_of_eq (L : RelativeGroupLaw R f) (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    {T : Scheme.{u}} (x : T ⟶ A) (hagree : x ≫ φ = x ≫ ψ) :
    x ≫ (diffPt L φ ψ hφ hψ).1 = x := by
  have h := congrArg Subtype.val (comp_diffPt L φ ψ hφ hψ x (x ≫ f) rfl)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [h]
  have hx : (⟨x ≫ φ, by rw [Category.assoc, hφ]⟩ : SchemeHomOver (x ≫ f) f) =
      ⟨x ≫ ψ, by rw [Category.assoc, hψ]⟩ := Subtype.ext hagree
  rw [hx, L.mul_inv_cancel, L.one_mul]

end P2mKcHomRigidBase

open P2mKcHomRigidBase in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ = (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ ψ)
    (hfix : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ A), x ≫ φ = x ≫ ψ) :
    φ = ψ := by

  set F : SchemeHomOver f f := diffPt L φ ψ hφ hψ with hF_def

  have he : F.1 = 𝟙 A :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.eq_id_of_one_comp_eq_of_forall_comp_eq_of_isAlgClosed
      hA L F.1 F.2 (comp_diffPt_of_eq L φ ψ hφ hψ _ hone) (fun k _ _ x => comp_diffPt_of_eq L φ ψ hφ hψ x (hfix k x))

  have hF1 : F = ⟨𝟙 A, Category.id_comp f⟩ := Subtype.ext he
  letI := L.pointGroup f
  have hgrp : ((⟨φ, hφ⟩ : SchemeHomOver f f) * (⟨ψ, hψ⟩ : SchemeHomOver f f)⁻¹) *
      (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = ⟨𝟙 A, Category.id_comp f⟩ := hF1
  have h2 : (⟨φ, hφ⟩ : SchemeHomOver f f) * (⟨ψ, hψ⟩ : SchemeHomOver f f)⁻¹ = 1 :=
    mul_right_cancel (hgrp.trans (one_mul _).symm)
  have h3 : (⟨φ, hφ⟩ : SchemeHomOver f f) = ⟨ψ, hψ⟩ := mul_inv_eq_one.mp h2
  exact congrArg Subtype.val h3

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed (solution)
