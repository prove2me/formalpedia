-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/75df3602-ea91-5233-9976-4f379bc36029

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal_of_smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid CerednikDrinfeld.ShimuraCurveModel.instFieldFc CerednikDrinfeld.ShimuraCurveModel.isCurveOverC CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeF CerednikDrinfeld.ShimuraCurveModel.instFieldF CerednikDrinfeld.ShimuraCurveModel.instAlgebraFbar CerednikDrinfeld.ShimuraCurveModel.instAlgebraFc CerednikDrinfeld.ShimuraCurveModel.instFieldFbar CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeC CerednikDrinfeld.ShimuraCurveModel.instFiniteTors CerednikDrinfeld.ShimuraCurveModel.isCurveOverF CerednikDrinfeld.ShimuraCurveModel.essFiniteTypeBar CerednikDrinfeld.ShimuraCurveModel.isCurveOverBar CerednikDrinfeld.ShimuraCurveModel.instAlgebraF IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue CerednikDrinfeld.TwoPlaceTorsionDatum.instAddCommGroup CerednikDrinfeld.TwoPlaceTorsionDatum.instFinite CerednikDrinfeld.JPrimeTorsionDatum.instAddCommGroup CerednikDrinfeld.JPrimeTorsionDatum.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.mk.injEq CerednikDrinfeld.ShimuraCurveModel.coe_torsionHecke_apply CerednikDrinfeld.ShimuraCurveModel.galJ_apply CerednikDrinfeld.ShimuraCurveModel.heckeGenJ_apply CerednikDrinfeld.ShimuraCurveModel.coe_torsionGal_apply CerednikDrinfeld.ShimuraCurveModel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.signTwist_heckeGen CerednikDrinfeld.ShimuraCurveModel.coe_restrictTors_apply Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg"
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star ModularCurve.UniformizedHeckeCurve.mk.sizeOf_spec ModularCurve.UniformizedHeckeCurve.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul CerednikDrinfeld.TwoPlaceTorsionDatum.snd_T CerednikDrinfeld.TwoPlaceTorsionDatum.snd_toric CerednikDrinfeld.TwoPlaceTorsionDatum.mk.injEq CerednikDrinfeld.TwoPlaceTorsionDatum.fst_T CerednikDrinfeld.TwoPlaceTorsionDatum.mk.sizeOf_spec CerednikDrinfeld.TwoPlaceTorsionDatum.fst_D CerednikDrinfeld.TwoPlaceTorsionDatum.snd_D CerednikDrinfeld.TwoPlaceTorsionDatum.fst_toric ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

namespace W1P
namespace KatzNTrick

section GroupLaw

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)

theorem nsmul_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = (letI := L.pointGroup t; x ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]
      rfl

theorem inv_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (t' : T' ⟶ Spec (CommRingCat.of B))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (schemeHomOverComp ψ hψ (L.inv t x)) (schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  have h' : (schemeHomOverComp ψ hψ (L.inv t x)) * (schemeHomOverComp ψ hψ x) = 1 := h
  exact eq_inv_of_mul_eq_one_left h'

theorem nsmul_val_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of B)} (e : t = t') {n : ℕ}
    {y : T ⟶ A} {hy : y ≫ f = t} :
    (L.nsmul t n ⟨y, hy⟩).1 = (L.nsmul t' n ⟨y, hy.trans e⟩).1 := by
  subst e; rfl

theorem nsmul_val_congr' {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (n : ℕ)
    (y y' : SchemeHomOver t f) (e : y.1 = y'.1) :
    (L.nsmul t n y).1 = (L.nsmul t n y').1 := by
  have : y = y' := Subtype.ext e
  subst this; rfl

theorem comp_nsmul_val {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (w : T' ⟶ T) (n : ℕ)
    (y : SchemeHomOver t f) :
    w ≫ (L.nsmul t n y).1 = (L.nsmul (w ≫ t) n ⟨w ≫ y.1, by rw [Category.assoc, y.2]⟩).1 := by
  have := L.nsmul_natural t (w ≫ t) w rfl n y
  have h := congrArg Subtype.val this
  rw [schemeHomOverComp_coe] at h
  rw [h]
  rfl

theorem key (hc : L.IsCommutative) (hf : Smooth f) (N : ℕ) (hN : (N : B) = 0) (μ : ℕ)
    (D : Type) [CommRing D] [Algebra B D] (J : Ideal D) (hJ : J ^ (μ + 1) = ⊥)
    (y y' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B D))) f)
    (hyy' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ y'.1) :
    (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B D))) (N ^ μ) y).1 =
      (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B D))) (N ^ μ) y').1 := by

  letI inst : CommGroup (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B D))) f) :=
    { L.pointGroup _ with mul_comm := fun a b => hc.mul_comm _ a b }
  have hND : (N : D) = 0 := by
    rw [← map_natCast (algebraMap B D) N, hN, map_zero]

  set δ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B D))) f := y * y'⁻¹ with hδ
  have hred : schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
      (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) y =
      schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
      (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) y' := by
    apply Subtype.ext
    simp only [schemeHomOverComp_coe]
    exact hyy'
  have hinf : L.IsInfinitesimal J δ := by
    unfold RelativeGroupLaw.IsInfinitesimal
    letI instq := L.pointGroup (Scheme.specOver (𝒪 := B) (D ⧸ J))
    have e1 : schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
        (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) δ =
        L.mul _ (schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
          (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) y)
        (L.inv _ (schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
          (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) y')) := by
      rw [hδ]
      show schemeHomOverComp _ _ (L.mul _ y (L.inv _ y')) = _
      rw [L.mul_natural, inv_natural]
    rw [e1, hred]
    exact L.mul_inv_cancel _ _
  have hkill := GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal_of_smooth L hc hf N hND J μ hJ δ hinf

  have hk : δ ^ (N ^ μ) = 1 := by
    have := (nsmul_eq_pow L _ (N ^ μ) δ).symm.trans hkill
    exact this
  have hy : y = δ * y' := by rw [hδ, inv_mul_cancel_right]
  congr 1
  rw [nsmul_eq_pow, nsmul_eq_pow]
  show y ^ (N ^ μ) = y' ^ (N ^ μ)
  rw [hy, mul_pow, hk, one_mul]

end GroupLaw

section Plumbing

theorem red_comp {E D : Type} [CommRing E] [CommRing D] (ρ : E →+* D) (JE : Ideal E) (JD : Ideal D)
    (hle : JE ≤ JD.comap ρ) {T : Scheme.{0}} (y : Spec (CommRingCat.of E) ⟶ T)
    (z : Spec (CommRingCat.of (E ⧸ JE)) ⟶ T) (hy : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ y = z) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JD)) ≫ (Spec.map (CommRingCat.ofHom ρ) ≫ y) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap JD ρ hle)) ≫ z := by
  rw [← hy, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem specMap_cancel_of_surjective {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) {E : Type} [CommRing E]
    (σ σ' : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of B₀))
    (h : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) = σ' ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) :
    σ = σ' := by
  rw [← Spec.map_preimage σ, ← Spec.map_preimage σ'] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  congr 1
  ext x
  obtain ⟨b, rfl⟩ := hπ x
  have := congrArg (fun χ => (CommRingCat.Hom.hom χ) b) h
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this

theorem fold {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : S →+* T) (b : R →+* S) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = Spec.map (CommRingCat.ofHom (a.comp b)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem fold_assoc {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : S →+* T) (b : R →+* S)
    {X : Scheme.{0}} (h : Spec (CommRingCat.of R) ⟶ X) :
    Spec.map (CommRingCat.ofHom a) ≫ (Spec.map (CommRingCat.ofHom b) ≫ h) =
      Spec.map (CommRingCat.ofHom (a.comp b)) ≫ h := by
  rw [← Category.assoc, fold]

end Plumbing

section Engine

variable {B : Type} [CommRing B] {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} (L' : RelativeGroupLaw B f')

theorem specMap_ofHom_preimage {R S : Type} [CommRing R] [CommRing S]
    (w : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (Spec.preimage w).hom) = w := by
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem ringHom_eq_of_specMap_eq {R S : Type} [CommRing R] [CommRing S] (φ ψ : R →+* S)
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ := by
  have h2 := Spec.map_inj.mp h
  have h3 := congrArg CommRingCat.Hom.hom h2
  simpa only [CommRingCat.hom_ofHom] using h3

theorem engine (hc : L'.IsCommutative) (hf : Smooth f') (N : ℕ) (hN : (N : B) = 0) (μ : ℕ)
    {C : Type} [CommRing C] (tC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B)) (JC : Ideal C)
    (x0 : Spec (CommRingCat.of (C ⧸ JC)) ⟶ A')
    (a : C) (xa : Spec (CommRingCat.of (Localization.Away a)) ⟶ A')
    (hxa : xa ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ tC)
    (hreda : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JC.map (algebraMap C (Localization.Away a))))) ≫ xa =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (JC.map (algebraMap C (Localization.Away a)))
        (algebraMap C (Localization.Away a)) Ideal.le_comap_map)) ≫ x0)
    {E : Type} [CommRing E] (tE : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of C))
    (y : Spec (CommRingCat.of E) ⟶ A') (hy : y ≫ f' = tE ≫ tC) (JE : Ideal E) (hJE : JE ^ (μ + 1) = ⊥)
    (q : C ⧸ JC →+* E ⧸ JE)
    (hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ tE =
      Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JC)))
    (hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ y = Spec.map (CommRingCat.ofHom q) ≫ x0)
    {D : Type} [CommRing D] (w : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of (Localization.Away a)))
    (u : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of E))
    (hwu : w ≫ Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) = u ≫ tE) :
    w ≫ (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ tC) (N ^ μ) ⟨xa, hxa⟩).1 =
      u ≫ (L'.nsmul (tE ≫ tC) (N ^ μ) ⟨y, hy⟩).1 := by
  classical

  obtain ⟨ρw, hw⟩ : ∃ ρ : Localization.Away a →+* D, Spec.map (CommRingCat.ofHom ρ) = w :=
    ⟨_, specMap_ofHom_preimage w⟩
  obtain ⟨ρu, hu⟩ : ∃ ρ : E →+* D, Spec.map (CommRingCat.ofHom ρ) = u := ⟨_, specMap_ofHom_preimage u⟩
  obtain ⟨αE, htE⟩ : ∃ ρ : C →+* E, Spec.map (CommRingCat.ofHom ρ) = tE := ⟨_, specMap_ofHom_preimage tE⟩

  have hχ : ρw.comp (algebraMap C (Localization.Away a)) = ρu.comp αE := by
    apply ringHom_eq_of_specMap_eq
    conv_lhs => rw [CommRingCat.ofHom_comp, Spec.map_comp, hw]
    conv_rhs => rw [CommRingCat.ofHom_comp, Spec.map_comp, hu, htE]
    exact hwu

  have hqE : (Ideal.Quotient.mk JE).comp αE = q.comp (Ideal.Quotient.mk JC) := by
    apply ringHom_eq_of_specMap_eq
    conv_lhs => rw [CommRingCat.ofHom_comp, Spec.map_comp, htE]
    conv_rhs => rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact hq
  have hJCE : JC.map αE ≤ JE := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hcJ
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.comp_apply, hqE, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hcJ, map_zero]

  obtain ⟨β, hβ⟩ : ∃ β : B →+* D, Spec.map (CommRingCat.ofHom β) =
      w ≫ (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ tC) :=
    ⟨_, specMap_ofHom_preimage _⟩
  letI : Algebra B D := β.toAlgebra
  have hbase : w ≫ (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ tC) =
      Spec.map (CommRingCat.ofHom (algebraMap B D)) := hβ.symm
  have hbase' : u ≫ (tE ≫ tC) = Spec.map (CommRingCat.ofHom (algebraMap B D)) := by
    rw [← hbase, ← Category.assoc, ← Category.assoc, ← hwu]
  rw [comp_nsmul_val, comp_nsmul_val, nsmul_val_congr L' hbase, nsmul_val_congr L' hbase']
  have hJ : JE.map ρu ^ (μ + 1) = ⊥ := by rw [← Ideal.map_pow, hJE, Ideal.map_bot]
  refine key L' hc hf N hN μ D (JE.map ρu) hJ _ _ ?_

  show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JE.map ρu))) ≫ (w ≫ xa) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JE.map ρu))) ≫ (u ≫ y)
  have hle_w : JC.map (algebraMap C (Localization.Away a)) ≤ (JE.map ρu).comap ρw := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hχ, ← Ideal.map_map]
    exact Ideal.map_mono hJCE
  have hle_u : JE ≤ (JE.map ρu).comap ρu := Ideal.le_comap_map
  rw [← hw, ← hu, red_comp ρw _ _ hle_w xa _ hreda, red_comp ρu _ _ hle_u y _ hred, ← Category.assoc,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  have hr : (Ideal.quotientMap (JE.map ρu) ρw hle_w).comp
        (Ideal.quotientMap (JC.map (algebraMap C (Localization.Away a))) (algebraMap C (Localization.Away a))
          Ideal.le_comap_map) =
      (Ideal.quotientMap (JE.map ρu) ρu hle_u).comp q := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro c
    have hqc : q (Ideal.Quotient.mk JC c) = Ideal.Quotient.mk JE (αE c) := by
      have := congrArg (fun χ : C →+* E ⧸ JE => χ c) hqE
      simpa only [RingHom.comp_apply] using this.symm
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk, hqc]
    have := congrArg (fun χ : C →+* D => χ c) hχ
    simp only [RingHom.comp_apply] at this
    rw [this]
  rw [hr]

end Engine

section Main

variable {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
  (hπ : Function.Surjective (algebraMap B B₀))
  (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (N : ℕ) (hN : (N : B) = 0)
  {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} [Smooth f'] (L' : RelativeGroupLaw B f')
  (hc : L'.IsCommutative)
  {Z Z₀ : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of B)) (fZ₀ : Z₀ ⟶ Spec (CommRingCat.of B₀)) (g : Z₀ ⟶ Z)
  (hg : CategoryTheory.IsPullback g fZ₀ fZ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
  (ψ : Z₀ ⟶ A') (hψ : ψ ≫ f' = fZ₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))

abbrev JJ (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀] (C : Type) [CommRing C] [Algebra B C] : Ideal C :=
  (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)

include hμ in
theorem JJ_pow (C : Type) [CommRing C] [Algebra B C] : JJ B B₀ C ^ (μ + 1) = ⊥ := by
  rw [JJ, ← Ideal.map_pow, hμ, Ideal.map_bot]

noncomputable def toQuot (C : Type) [CommRing C] [Algebra B C] : B₀ →+* C ⧸ JJ B B₀ C :=
  (algebraMap B B₀).liftOfSurjective hπ
    ⟨(Ideal.Quotient.mk (JJ B B₀ C)).comp (algebraMap B C), fun b hb => by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hb⟩

theorem toQuot_comp (C : Type) [CommRing C] [Algebra B C] :
    (toQuot hπ C).comp (algebraMap B B₀) = (Ideal.Quotient.mk (JJ B B₀ C)).comp (algebraMap B C) :=
  RingHom.liftOfSurjective_comp _ _ _

noncomputable def red₀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    Spec (CommRingCat.of (C ⧸ JJ B B₀ C)) ⟶ Z₀ :=
  hg.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ P)
    (Spec.map (CommRingCat.ofHom (toQuot hπ C))) (by
      rw [Category.assoc, hP, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        toQuot_comp])

theorem red₀_fst (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    red₀ hπ fZ fZ₀ g hg C P hP ≫ g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ P :=
  hg.lift_fst _ _ _

theorem red₀_snd (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    red₀ hπ fZ fZ₀ g hg C P hP ≫ fZ₀ = Spec.map (CommRingCat.ofHom (toQuot hπ C)) :=
  hg.lift_snd _ _ _

include hπ in

theorem hom_ext_Z₀ (hg : CategoryTheory.IsPullback g fZ₀ fZ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    {E : Type} [CommRing E] (Q Q' : Spec (CommRingCat.of E) ⟶ Z₀) (h : Q ≫ g = Q' ≫ g) :
    Q = Q' := by
  apply hg.hom_ext h
  apply specMap_cancel_of_surjective hπ
  rw [Category.assoc, Category.assoc, ← hg.w, ← Category.assoc, h, Category.assoc]

noncomputable def x₀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    Spec (CommRingCat.of (C ⧸ JJ B B₀ C)) ⟶ A' :=
  red₀ hπ fZ fZ₀ g hg C P hP ≫ ψ

include hψ in
theorem x₀_over (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    x₀ hπ fZ fZ₀ g hg ψ C P hP ≫ f' =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
  rw [x₀, Category.assoc, hψ, ← Category.assoc, red₀_snd, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, toQuot_comp]

include hπ in

theorem x₀_nat (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C'] (φ : C →+* C')
    (P : Spec (CommRingCat.of C) ⟶ Z) (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
    (hP' : (Spec.map (CommRingCat.ofHom φ) ≫ P) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C')))
    (hle : JJ B B₀ C ≤ (JJ B B₀ C').comap φ) :
    x₀ hπ fZ fZ₀ g hg ψ C' (Spec.map (CommRingCat.ofHom φ) ≫ P) hP' =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (JJ B B₀ C') φ hle)) ≫ x₀ hπ fZ fZ₀ g hg ψ C P hP := by
  unfold x₀
  rw [← Category.assoc]
  congr 1
  apply hom_ext_Z₀ hπ fZ fZ₀ g hg
  rw [red₀_fst, Category.assoc, red₀_fst, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

end Main

structure LiftCover {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀] {A' : Scheme.{0}}
    (f' : A' ⟶ Spec (CommRingCat.of B)) (C : Type) [CommRing C] [Algebra B C]
    (z : Spec (CommRingCat.of (C ⧸ JJ B B₀ C)) ⟶ A') where
  ι : Type
  a : ι → C
  hspan : Ideal.span (Set.range a) = ⊤
  x : ∀ i, Spec (CommRingCat.of (Localization.Away (a i))) ⟶ A'
  hx : ∀ i, x i ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (a i)))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B C))
  hred : ∀ i, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((JJ B B₀ C).map (algebraMap C (Localization.Away (a i)))))) ≫ x i =
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((JJ B B₀ C).map (algebraMap C (Localization.Away (a i))))
      (algebraMap C (Localization.Away (a i))) Ideal.le_comap_map)) ≫ z

theorem nonempty_liftCover {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of B)) [Smooth f'] (C : Type) [CommRing C] [Algebra B C]
    (z : Spec (CommRingCat.of (C ⧸ JJ B B₀ C)) ⟶ A')
    (hz : z ≫ f' = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    Nonempty (LiftCover f' C z) := by
  have hnil : IsNilpotent (JJ B B₀ C) := ⟨μ + 1, by rw [JJ_pow μ hμ C]; exact Submodule.zero_eq_bot.symm⟩
  obtain ⟨ι, a, hspan, h⟩ :=
    AlgebraicGeometry.Smooth.exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent f' (JJ B B₀ C) hnil
      (Spec.map (CommRingCat.ofHom (algebraMap B C))) z hz
  choose x hx hred using h
  exact ⟨⟨ι, a, hspan, x, hx, hred⟩⟩

end W1P.KatzNTrick

open W1P.KatzNTrick in
theorem W1P.natural_family
    {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀))
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (N : ℕ) (hN : (N : B) = 0)
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} [Smooth f'] (L' : RelativeGroupLaw B f')
    (hc : L'.IsCommutative)
    {Z Z₀ : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of B)) (fZ₀ : Z₀ ⟶ Spec (CommRingCat.of B₀)) (g : Z₀ ⟶ Z)
    (hg : CategoryTheory.IsPullback g fZ₀ fZ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (ψ : Z₀ ⟶ A') (hψ : ψ ≫ f' = fZ₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) :
    ∃ Ñ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z),
        P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)) → (Spec (CommRingCat.of C) ⟶ A'),
      (∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
        (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))),
        Ñ C P hP ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B C))) ∧
      (∀ (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C'] (φ : C →ₐ[B] C')
        (P : Spec (CommRingCat.of C) ⟶ Z) (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (hP' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P) ≫ fZ =
          Spec.map (CommRingCat.ofHom (algebraMap B C'))),
        Ñ C' (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P) hP' =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Ñ C P hP) ∧
      (∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
        (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (P₀ : Spec (CommRingCat.of (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C))) ⟶ Z₀)
        (hP₀ : P₀ ≫ g =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ P)
        (x : Spec (CommRingCat.of C) ⟶ A') (hx : x ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (hlift : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ x =
          P₀ ≫ ψ),
        Ñ C P hP = (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B C))) (N ^ μ) ⟨x, hx⟩).1) := by
  classical

  let Λ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))),
      LiftCover (B₀ := B₀) f' C (x₀ hπ fZ fZ₀ g hg ψ C P hP) :=
    fun C _ _ P hP => Classical.choice (nonempty_liftCover μ hμ f' C _ (x₀_over hπ fZ fZ₀ g hg ψ hψ C P hP))

  let 𝒰 : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))), (Spec (CommRingCat.of C)).OpenCover :=
    fun C _ _ P hP =>
      (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of C) (Λ C P hP).a (Λ C P hP).hspan).openCover
  let v : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) (i : (Λ C P hP).ι),
      Spec (CommRingCat.of (Localization.Away ((Λ C P hP).a i))) ⟶ A' :=
    fun C _ _ P hP i =>
      (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away ((Λ C P hP).a i)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B C))) (N ^ μ) ⟨(Λ C P hP).x i, (Λ C P hP).hx i⟩).1

  have hJi : ∀ (C : Type) [CommRing C] [Algebra B C] (c : C),
      (JJ B B₀ C).map (algebraMap C (Localization.Away c)) ^ (μ + 1) = ⊥ := by
    intro C _ _ c
    rw [← Ideal.map_pow, JJ_pow μ hμ C, Ideal.map_bot]
  have hqi : ∀ (C : Type) [CommRing C] [Algebra B C] (c : C),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((JJ B B₀ C).map (algebraMap C (Localization.Away c))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away c))) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((JJ B B₀ C).map (algebraMap C (Localization.Away c)))
        (algebraMap C (Localization.Away c)) Ideal.le_comap_map)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) := by
    intro C _ _ c
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]

  have compat : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) (i j : (Λ C P hP).ι),
      pullback.fst ((𝒰 C P hP).f i) ((𝒰 C P hP).f j) ≫ v C P hP i =
        pullback.snd ((𝒰 C P hP).f i) ((𝒰 C P hP).f j) ≫ v C P hP j := by
    intro C _ _ P hP i j
    let 𝒱 := (pullback ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)).affineOpenCover
    refine 𝒱.openCover.hom_ext _ _ fun k => ?_
    change (𝒱.f k ≫ pullback.fst ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)) ≫ v C P hP i =
      (𝒱.f k ≫ pullback.snd ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)) ≫ v C P hP j
    have hwu : (𝒱.f k ≫ pullback.fst ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)) ≫ (𝒰 C P hP).f i =
        (𝒱.f k ≫ pullback.snd ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)) ≫ (𝒰 C P hP).f j := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    exact engine L' hc inferInstance N hN μ (Spec.map (CommRingCat.ofHom (algebraMap B C))) (JJ B B₀ C)
      (x₀ hπ fZ fZ₀ g hg ψ C P hP) ((Λ C P hP).a i) ((Λ C P hP).x i) ((Λ C P hP).hx i) ((Λ C P hP).hred i)
      ((𝒰 C P hP).f j) ((Λ C P hP).x j) ((Λ C P hP).hx j)
      ((JJ B B₀ C).map (algebraMap C (Localization.Away ((Λ C P hP).a j)))) (hJi C _)
      (Ideal.quotientMap _ (algebraMap C _) Ideal.le_comap_map) (hqi C _) ((Λ C P hP).hred j)
      (𝒱.f k ≫ pullback.fst _ _) (𝒱.f k ≫ pullback.snd _ _) hwu

  let Ñ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z),
      P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)) → (Spec (CommRingCat.of C) ⟶ A') :=
    fun C _ _ P hP => (𝒰 C P hP).glueMorphisms (v C P hP) (compat C P hP)
  have hÑ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) (i : (Λ C P hP).ι),
      (𝒰 C P hP).f i ≫ Ñ C P hP = v C P hP i :=
    fun C _ _ P hP i => (𝒰 C P hP).ι_glueMorphisms _ _ i

  have det : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) {E : Type} [CommRing E]
      (tE : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of C)) (y : Spec (CommRingCat.of E) ⟶ A')
      (hy : y ≫ f' = tE ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (JE : Ideal E) (hJE : JE ^ (μ + 1) = ⊥)
      (q : C ⧸ JJ B B₀ C →+* E ⧸ JE)
      (hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ tE =
        Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))))
      (hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ y =
        Spec.map (CommRingCat.ofHom q) ≫ x₀ hπ fZ fZ₀ g hg ψ C P hP),
      tE ≫ Ñ C P hP = (L'.nsmul (tE ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (N ^ μ) ⟨y, hy⟩).1 := by
    intro C _ _ P hP E _ tE y hy JE hJE q hq hred
    refine Scheme.Cover.hom_ext ((𝒰 C P hP).pullback₁ tE) _ _ fun i => ?_
    change pullback.fst tE ((𝒰 C P hP).f i) ≫ tE ≫ Ñ C P hP =
      pullback.fst tE ((𝒰 C P hP).f i) ≫ (L'.nsmul _ (N ^ μ) ⟨y, hy⟩).1
    let 𝒲 := (pullback tE ((𝒰 C P hP).f i)).affineOpenCover
    refine 𝒲.openCover.hom_ext _ _ fun k => ?_
    change 𝒲.f k ≫ pullback.fst tE ((𝒰 C P hP).f i) ≫ tE ≫ Ñ C P hP =
      𝒲.f k ≫ pullback.fst tE ((𝒰 C P hP).f i) ≫ (L'.nsmul _ (N ^ μ) ⟨y, hy⟩).1
    have hcond : (𝒲.f k ≫ pullback.snd tE ((𝒰 C P hP).f i)) ≫ (𝒰 C P hP).f i =
        (𝒲.f k ≫ pullback.fst tE ((𝒰 C P hP).f i)) ≫ tE := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have e1 : 𝒲.f k ≫ pullback.fst tE ((𝒰 C P hP).f i) ≫ tE ≫ Ñ C P hP =
        (𝒲.f k ≫ pullback.snd tE ((𝒰 C P hP).f i)) ≫ v C P hP i := by
      rw [← hÑ C P hP i, Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
        Category.assoc]
    rw [e1, ← Category.assoc (𝒲.f k)]
    exact engine L' hc inferInstance N hN μ _ (JJ B B₀ C) (x₀ hπ fZ fZ₀ g hg ψ C P hP) ((Λ C P hP).a i)
      ((Λ C P hP).x i) ((Λ C P hP).hx i) ((Λ C P hP).hred i) tE y hy JE hJE q hq hred _ _ hcond
  refine ⟨Ñ, ?_, ?_, ?_⟩
  ·
    intro C _ _ P hP
    refine (𝒰 C P hP).hom_ext _ _ fun i => ?_
    rw [← Category.assoc, hÑ]
    exact (L'.nsmul _ (N ^ μ) ⟨(Λ C P hP).x i, (Λ C P hP).hx i⟩).2
  ·
    intro C C' _ _ _ _ φ P hP hP'
    refine (𝒰 C' _ hP').hom_ext _ _ fun k => ?_
    rw [hÑ, ← Category.assoc]
    have hφ : φ.toRingHom.comp (algebraMap B C) = algebraMap B C' := φ.comp_algebraMap
    have hle : JJ B B₀ C ≤ (JJ B B₀ C').comap φ.toRingHom := by
      rw [← Ideal.map_le_iff_le_comap, JJ, Ideal.map_map, hφ]

    change _ = (Spec.map (CommRingCat.ofHom (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫ Ñ C P hP
    rw [fold]
    have hbase : Spec.map (CommRingCat.ofHom (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B C')) =
        Spec.map (CommRingCat.ofHom ((algebraMap C' (Localization.Away ((Λ C' _ hP').a k))).comp φ.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [fold, fold, RingHom.comp_assoc, hφ]
    have hy : (Λ C' _ hP').x k ≫ f' =
        Spec.map (CommRingCat.ofHom ((algebraMap C' (Localization.Away ((Λ C' _ hP').a k))).comp φ.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [← hbase]; exact (Λ C' _ hP').hx k
    have hring : (Ideal.Quotient.mk ((JJ B B₀ C').map (algebraMap C' (Localization.Away ((Λ C' _ hP').a k))))).comp
          ((algebraMap C' (Localization.Away ((Λ C' _ hP').a k))).comp φ.toRingHom) =
        ((Ideal.quotientMap _ (algebraMap C' (Localization.Away ((Λ C' _ hP').a k))) Ideal.le_comap_map).comp
          (Ideal.quotientMap (JJ B B₀ C') φ.toRingHom hle)).comp (Ideal.Quotient.mk (JJ B B₀ C)) := by
      ext c
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          ((JJ B B₀ C').map (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))))) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap C' (Localization.Away ((Λ C' _ hP').a k))).comp φ.toRingHom)) =
        Spec.map (CommRingCat.ofHom ((Ideal.quotientMap _ (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))
          Ideal.le_comap_map).comp (Ideal.quotientMap (JJ B B₀ C') φ.toRingHom hle))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) := by
      rw [fold, fold, hring]
    have hx₀ := x₀_nat hπ fZ fZ₀ g hg ψ C C' φ.toRingHom P hP hP' hle
    have hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          ((JJ B B₀ C').map (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))))) ≫ (Λ C' _ hP').x k =
        Spec.map (CommRingCat.ofHom ((Ideal.quotientMap _ (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))
          Ideal.le_comap_map).comp (Ideal.quotientMap (JJ B B₀ C') φ.toRingHom hle))) ≫
        x₀ hπ fZ fZ₀ g hg ψ C P hP := by
      refine ((Λ C' _ hP').hred k).trans ?_
      refine (congrArg (fun t => Spec.map (CommRingCat.ofHom (Ideal.quotientMap _
        (algebraMap C' (Localization.Away ((Λ C' _ hP').a k))) Ideal.le_comap_map)) ≫ t) hx₀).trans ?_
      exact fold_assoc _ _ _
    rw [det C P hP _ ((Λ C' _ hP').x k) hy _ (hJi C' _) _ hq hred]
    exact nsmul_val_congr L' hbase
  ·
    intro C _ _ P hP P₀ hP₀ x hx hlift
    refine (𝒰 C P hP).hom_ext _ _ fun i => ?_
    rw [hÑ]
    have hP₀' : P₀ = red₀ hπ fZ fZ₀ g hg C P hP :=
      hom_ext_Z₀ hπ fZ fZ₀ g hg _ _ (by rw [hP₀, red₀_fst])
    have hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ x =
        Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ x₀ hπ fZ fZ₀ g hg ψ C P hP := by
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      show _ = red₀ hπ fZ fZ₀ g hg C P hP ≫ ψ
      rw [← hP₀']
      exact hlift
    have hy : x ≫ f' = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [Category.id_comp]; exact hx
    have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ 𝟙 (Spec (CommRingCat.of C)) =
        Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) := by
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
    have hwu : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away ((Λ C P hP).a i)))) =
        (𝒰 C P hP).f i ≫ 𝟙 _ := by
      rw [Category.id_comp, Category.comp_id]; rfl
    have key₁ := engine L' hc inferInstance N hN μ _ (JJ B B₀ C) (x₀ hπ fZ fZ₀ g hg ψ C P hP) ((Λ C P hP).a i)
      ((Λ C P hP).x i) ((Λ C P hP).hx i) ((Λ C P hP).hred i) (𝟙 _) x hy (JJ B B₀ C) (JJ_pow μ hμ C)
      (RingHom.id _) hq hred (𝟙 _) ((𝒰 C P hP).f i) hwu
    rw [Category.id_comp] at key₁
    refine key₁.trans ?_
    rw [comp_nsmul_val, comp_nsmul_val]
    exact nsmul_val_congr L' (by rw [Category.id_comp]; rfl)

namespace W1P
namespace K2Aux

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

def mapPt {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩

@[scoped simp] theorem mapPt_coe {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : (mapPt φ hφ P).1 = P.1 ≫ φ := rfl

def nsmulPt (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ℕ → SchemeHomOver t f → SchemeHomOver t f
  | 0, _ => L.one t
  | n + 1, P => L.mul t (nsmulPt L t n P) P

theorem nsmul_val (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem nsmulPt_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (nsmulPt L t n P) = nsmulPt L t' n (schemeHomOverComp ψ hψ P) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih =>
      change schemeHomOverComp ψ hψ (L.mul t (nsmulPt L t n P) P) =
        L.mul t' (nsmulPt L t' n (schemeHomOverComp ψ hψ P)) (schemeHomOverComp ψ hψ P)
      rw [L.mul_natural, ih]

theorem mapPt_schemeHomOverComp {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T T' : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f) :
    mapPt φ hφ (schemeHomOverComp ψ hψ P) = schemeHomOverComp ψ hψ (mapPt φ hφ P) :=
  Subtype.ext (Category.assoc _ _ _)

theorem SchemeHomOver.ext_of_cover {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (𝒰 : T.OpenCover)
    (P Q : SchemeHomOver t f)
    (h : ∀ i, schemeHomOverComp (𝒰.f i) rfl P = schemeHomOverComp (𝒰.f i) (rfl : 𝒰.f i ≫ t = 𝒰.f i ≫ t) Q) :
    P = Q :=
  Subtype.ext (𝒰.hom_ext _ _ fun i => by simpa only [schemeHomOverComp_coe] using congrArg Subtype.val (h i))

theorem exists_algebra_eq_specOver (S : CommRingCat.{0}) (t : Spec S ⟶ Spec (CommRingCat.of R)) :
    ∃ inst : Algebra R S, t = @Scheme.specOver R _ S _ inst := by
  refine ⟨(Spec.preimage t).hom.toAlgebra, ?_⟩
  change t = Spec.map (CommRingCat.ofHom (Spec.preimage t).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem mapPt_mul_of_affine {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (u : A ⟶ A') (hu : u ≫ f' = f)
    (h : ∀ (C : Type) [CommRing C] [Algebra R C] (P Q : SchemeHomOver (Scheme.specOver (𝒪 := R) C) f),
      mapPt u hu (L.mul _ P Q) = L'.mul _ (mapPt u hu P) (mapPt u hu Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    mapPt u hu (L.mul t P Q) = L'.mul t (mapPt u hu P) (mapPt u hu Q) := by

  have key : ∀ (S : CommRingCat.{0}) (t' : Spec S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' f),
      mapPt u hu (L.mul t' P Q) = L'.mul t' (mapPt u hu P) (mapPt u hu Q) := by
    intro S t' P Q
    obtain ⟨inst, ht'⟩ := exists_algebra_eq_specOver S t'
    subst ht'
    exact @h S _ inst P Q
  refine SchemeHomOver.ext_of_cover T.affineOpenCover.openCover _ _ fun i => ?_
  change schemeHomOverComp (T.affineOpenCover.f i) rfl (mapPt u hu (L.mul t P Q)) =
    schemeHomOverComp (T.affineOpenCover.f i) rfl (L'.mul t (mapPt u hu P) (mapPt u hu Q))
  rw [← mapPt_schemeHomOverComp, L.mul_natural, L'.mul_natural, key, mapPt_schemeHomOverComp,
    mapPt_schemeHomOverComp]

theorem hom_eq_of_affine {Y : Scheme.{0}} (u v : A ⟶ Y)
    (h : ∀ (C : Type) [CommRing C] [Algebra R C] (P : SchemeHomOver (Scheme.specOver (𝒪 := R) C) f),
      P.1 ≫ u = P.1 ≫ v) : u = v := by
  refine A.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
  change A.affineOpenCover.f i ≫ u = A.affineOpenCover.f i ≫ v
  obtain ⟨inst, ht⟩ := exists_algebra_eq_specOver (A.affineOpenCover.X i) (A.affineOpenCover.f i ≫ f)
  exact @h _ _ inst ⟨A.affineOpenCover.f i, ht⟩

theorem RelativeGroupLaw.eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem nsmulPt_comp_of_mul_comp {R₀ : Type} [CommRing R₀] (φ : R →+* R₀)
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)}
    (L : RelativeGroupLaw R f) (L₀ : RelativeGroupLaw R₀ f₀) (g : A₀ ⟶ A)
    (hg : g ≫ f = f₀ ≫ Spec.map (CommRingCat.ofHom φ))
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (k : ℕ) (Q : SchemeHomOver t f₀) :
    (nsmulPt L₀ t k Q).1 ≫ g =
      (nsmulPt L (t ≫ Spec.map (CommRingCat.ofHom φ)) k
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, Q.2]⟩).1 := by

  let gpt : SchemeHomOver t f₀ → SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) f :=
    fun P => ⟨P.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, P.2]⟩
  have hone : gpt (L₀.one t) = L.one _ := by
    apply RelativeGroupLaw.eq_one_of_mul_self
    apply Subtype.ext
    have := hmul t (L₀.one t) (L₀.one t)
    rw [L₀.one_mul] at this
    exact this.symm
  suffices H : ∀ k, gpt (nsmulPt L₀ t k Q) = nsmulPt L (t ≫ Spec.map (CommRingCat.ofHom φ)) k (gpt Q) from
    congrArg Subtype.val (H k)
  intro k
  induction k with
  | zero => exact hone
  | succ k ih =>
      change gpt (L₀.mul t (nsmulPt L₀ t k Q) Q) =
        L.mul _ (nsmulPt L (t ≫ Spec.map (CommRingCat.ofHom φ)) k (gpt Q)) (gpt Q)
      rw [← ih]
      exact Subtype.ext (hmul t _ _)

theorem nsmulPt_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (e : t₁ = t₂) (k : ℕ) (x₁ : SchemeHomOver t₁ f) (x₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) :
    (nsmulPt L t₁ k x₁).1 = (nsmulPt L t₂ k x₂).1 := by
  subst e
  have : x₁ = x₂ := Subtype.ext hx
  subst this
  rfl

section reductionHelpers

theorem exists_algebra_quotient_isScalarTower {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (C : Type) [CommRing C] [Algebra B C] :
    ∃ inst : Algebra B₀ (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)),
      @IsScalarTower B B₀ (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)) _ inst.toSMul _ := by
  let I : Ideal B := RingHom.ker (algebraMap B B₀)
  let I' : Ideal C := I.map (algebraMap B C)
  let e : (B ⧸ I) ≃+* B₀ := RingHom.quotientKerEquivOfSurjective hπ
  let χ : B₀ →+* C ⧸ I' := (Ideal.quotientMap I' (algebraMap B C) Ideal.le_comap_map).comp e.symm.toRingHom
  refine ⟨χ.toAlgebra, ?_⟩
  letI : Algebra B₀ (C ⧸ I') := χ.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change Ideal.Quotient.mk I' (algebraMap B C x) =
    Ideal.quotientMap I' (algebraMap B C) Ideal.le_comap_map (e.symm (algebraMap B B₀ x))
  have : e.symm (algebraMap B B₀ x) = Ideal.Quotient.mk I x := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hπ x).symm
  rw [this, Ideal.quotientMap_mk]

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

end reductionHelpers

section homHelpers
variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (e : t₁ = t₂) (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst e
  have h1 : x₁ = x₂ := Subtype.ext hx
  have h2 : y₁ = y₂ := Subtype.ext hy
  subst h1 h2
  rfl

theorem nsmulPt_mul (L : RelativeGroupLaw R f) (hc : L.IsCommutative) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (m : ℕ) (x y : SchemeHomOver t f) :
    nsmulPt L t m (L.mul t x y) = L.mul t (nsmulPt L t m x) (nsmulPt L t m y) := by
  induction m with
  | zero => change L.one t = L.mul t (L.one t) (L.one t); rw [L.one_mul]
  | succ m ih =>
      change L.mul t (nsmulPt L t m (L.mul t x y)) (L.mul t x y) =
        L.mul t (L.mul t (nsmulPt L t m x) x) (L.mul t (nsmulPt L t m y) y)
      rw [ih, L.mul_assoc, L.mul_assoc, ← L.mul_assoc t (nsmulPt L t m y) x y, hc t (nsmulPt L t m y) x,
        L.mul_assoc]

end homHelpers

end W1P.K2Aux
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero.W1P P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero.W1P.K2Aux"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero.W1P"

open W1P.K2Aux

theorem solution
    (S S₀ : Type) [CommRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀))
    (N : ℕ) (hN : (N : S) = 0) (μ : ℕ) (hμ : RingHom.ker (algebraMap S S₀) ^ (μ + 1) = ⊥)

    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
    (hc' : L'.IsCommutative) (hA' : AbelianSchemePropertyBundle S f')

    {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)) (L₀ : RelativeGroupLaw S₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap S S₀))))
    (hgL : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {A'₀ : Scheme.{0}} (f'₀ : A'₀ ⟶ Spec (CommRingCat.of S₀)) (L'₀ : RelativeGroupLaw S₀ f'₀)
    (g' : A'₀ ⟶ A') (hg' : IsPullback g' f'₀ f' (Spec.map (CommRingCat.ofHom (algebraMap S S₀))))
    (hg'L : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f'₀),
      (L'₀.mul t P Q).1 ≫ g' =
        (L'.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))
          ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1)

    (u₀ : A₀ ⟶ A'₀) (hu₀ : u₀ ≫ f'₀ = f₀)
    (hu₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ u₀ =
        (L'₀.mul t ⟨P.1 ≫ u₀, by rw [Category.assoc, hu₀]; exact P.2⟩
          ⟨Q.1 ≫ u₀, by rw [Category.assoc, hu₀]; exact Q.2⟩).1) :
    ∃ (F : A ⟶ A') (hF : F ≫ f' = f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ F =
          (L'.mul t ⟨P.1 ≫ F, by rw [Category.assoc, hF]; exact P.2⟩
            ⟨Q.1 ≫ F, by rw [Category.assoc, hF]; exact Q.2⟩).1) ∧
      g ≫ F = u₀ ≫ L'₀.schemeNsmul (N ^ μ) ≫ g'  := by
  classical
  haveI hsm : Smooth f' := hA'.smooth

  have hψ' : (u₀ ≫ g') ≫ f' = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)) := by
    rw [Category.assoc, hg'.w, ← Category.assoc, hu₀]
  obtain ⟨Ñf, hover, hnat, hchar⟩ :=
    W1P.natural_family
      hπ μ hμ N hN L' hc' f f₀ g hg (u₀ ≫ g') hψ'
  obtain ⟨Ñ, hÑf, hÑpt, -⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural f f' Ñf hover hnat

  have hIC : ∀ (C : Type) [CommRing C] [Algebra S C] (C' : Type) [CommRing C'] [Algebra C C'] [Algebra S C']
      [IsScalarTower S C C'],
      ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)).map (algebraMap C C') =
        (RingHom.ker (algebraMap S S₀)).map (algebraMap S C') := by
    intro C _ _ C' _ _ _ _
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hInil : ∀ (C : Type) [CommRing C] [Algebra S C],
      IsNilpotent ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)) := by
    intro C _ _
    exact ⟨μ + 1, by rw [← Ideal.map_pow, hμ]; simp⟩

  have red : ∀ (C : Type) [CommRing C] [Algebra S C]
      [Algebra S₀ (C ⧸ (RingHom.ker (algebraMap S S₀)).map (algebraMap S C))]
      [IsScalarTower S S₀ (C ⧸ (RingHom.ker (algebraMap S S₀)).map (algebraMap S C))]
      (P : Spec (CommRingCat.of C) ⟶ A)
      (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S C))),
      ∃ P₀ : Spec (CommRingCat.of (C ⧸ (RingHom.ker (algebraMap S S₀)).map (algebraMap S C))) ⟶ A₀,
        P₀ ≫ g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P ∧
        P₀ ≫ f₀ = Scheme.specOver (𝒪 := S₀) (C ⧸ (RingHom.ker (algebraMap S S₀)).map (algebraMap S C)) ∧
        (P₀ ≫ u₀ ≫ g') ≫ f' = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
    intro C _ _ _ _ P hP
    have hcomm : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P) ≫ f =
        Scheme.specOver (𝒪 := S₀) (C ⧸ (RingHom.ker (algebraMap S S₀)).map (algebraMap S C)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S S₀)) := by
      rw [Category.assoc, hP, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
    refine ⟨hg.lift _ _ hcomm, hg.lift_fst _ _ hcomm, hg.lift_snd _ _ hcomm, ?_⟩
    rw [Category.assoc, hψ', ← Category.assoc, hg.lift_snd _ _ hcomm]
    change Spec.map (CommRingCat.ofHom (algebraMap S₀ _)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]

  have pieceChar : ∀ (C : Type) [CommRing C] [Algebra S C] (P : Spec (CommRingCat.of C) ⟶ A)
      (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S C)))
      (P₀ : Spec (CommRingCat.of (C ⧸ (RingHom.ker (algebraMap S S₀)).map (algebraMap S C))) ⟶ A₀)
      (hP₀ : P₀ ≫ g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P)
      (a : C) (x : Spec (CommRingCat.of (Localization.Away a)) ⟶ A')
      (hx : x ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away a))))
      (hxl : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)).map (algebraMap C (Localization.Away a))))) ≫ x =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap
          (((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)).map (algebraMap C (Localization.Away a)))
          (algebraMap C (Localization.Away a)) Ideal.le_comap_map)) ≫ P₀ ≫ u₀ ≫ g'),
      Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ Ñf C P hP =
        (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away a)))) (N ^ μ) ⟨x, hx⟩).1 := by
    intro C _ _ P hP P₀ hP₀ a x hx hxl
    let Ca := Localization.Away a
    let loc : C →+* Ca := algebraMap C Ca
    let IC : Ideal C := (RingHom.ker (algebraMap S S₀)).map (algebraMap S C)
    let ICa : Ideal Ca := (RingHom.ker (algebraMap S S₀)).map (algebraMap S Ca)
    have hIeq : IC.map loc = ICa := hIC C Ca
    have hPa : (Spec.map (CommRingCat.ofHom loc) ≫ P) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S Ca)) := by
      rw [Category.assoc, hP, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    have hn : Ñf Ca (Spec.map (CommRingCat.ofHom loc) ≫ P) hPa = Spec.map (CommRingCat.ofHom loc) ≫ Ñf C P hP :=
      hnat C Ca (IsScalarTower.toAlgHom S C Ca) P hP hPa
    change Spec.map (CommRingCat.ofHom loc) ≫ Ñf C P hP = _
    rw [← hn]
    let ρ : C ⧸ IC →+* Ca ⧸ ICa := Ideal.quotientMap ICa loc (by rw [← hIeq]; exact Ideal.le_comap_map)
    let σ : Ca ⧸ IC.map loc →+* Ca ⧸ ICa := Ideal.quotientMap ICa (RingHom.id Ca) (by rw [hIeq]; exact le_of_eq (Ideal.comap_id _).symm)
    have hσ : (Ideal.Quotient.mk ICa) = σ.comp (Ideal.Quotient.mk (IC.map loc)) := by
      ext c; rfl
    have hρ : ρ = σ.comp (Ideal.quotientMap (IC.map loc) loc Ideal.le_comap_map) :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    refine hchar Ca (Spec.map (CommRingCat.ofHom loc) ≫ P) hPa (Spec.map (CommRingCat.ofHom ρ) ≫ P₀) ?_ x hx ?_
    · rw [Category.assoc, hP₀, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    · rw [hσ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hxl, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← hρ]
      exact rfl
  refine ⟨Ñ, hÑf, ?_, ?_⟩
  ·
    have hom_affine : ∀ (C : Type) [CommRing C] [Algebra S C]
        (P Q : SchemeHomOver (Scheme.specOver (𝒪 := S) C) f),
        mapPt Ñ hÑf (L.mul _ P Q) = L'.mul _ (mapPt Ñ hÑf P) (mapPt Ñ hÑf Q) := by
      intro C _ _ P Q
      obtain ⟨instq, hst⟩ := exists_algebra_quotient_isScalarTower hπ C
      letI := instq; haveI := hst
      have hP : P.1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S C)) := P.2
      have hQ : Q.1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S C)) := Q.2
      have hPQ : (L.mul _ P Q).1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S C)) := (L.mul _ P Q).2
      obtain ⟨P₀, hP₀, hP₀f, hxP⟩ := red C P.1 hP
      obtain ⟨Q₀, hQ₀, hQ₀f, hxQ⟩ := red C Q.1 hQ
      let Cq := C ⧸ ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C))
      let t₀ : Spec (CommRingCat.of Cq) ⟶ Spec (CommRingCat.of S₀) := Scheme.specOver (𝒪 := S₀) Cq
      let p₀ : SchemeHomOver t₀ f₀ := ⟨P₀, hP₀f⟩
      let q₀ : SchemeHomOver t₀ f₀ := ⟨Q₀, hQ₀f⟩
      have ht₀ : t₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
        change Spec.map (CommRingCat.ofHom (algebraMap S₀ Cq)) ≫ _ = _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq]

      let z₀ : Spec (CommRingCat.of Cq) ⟶ pullback f' f' := pullback.lift (P₀ ≫ u₀ ≫ g') (Q₀ ≫ u₀ ≫ g') (hxP.trans hxQ.symm)
      have hz₀ : z₀ ≫ (pullback.fst f' f' ≫ f') =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
        rw [← Category.assoc, pullback.lift_fst]; exact hxP
      obtain ⟨ι, a, hspan, hlifts⟩ :=
        AlgebraicGeometry.Smooth.exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
          (pullback.fst f' f' ≫ f') ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)) (hInil C)
          (Spec.map (CommRingCat.ofHom (algebraMap S C))) z₀ hz₀
      apply Subtype.ext
      refine (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of C) a hspan).openCover.hom_ext _ _
        fun i => ?_
      change Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (a i)))) ≫ (L.mul _ P Q).1 ≫ Ñ =
        Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (a i)))) ≫
          (L'.mul _ (mapPt Ñ hÑf P) (mapPt Ñ hÑf Q)).1
      let Ci := Localization.Away (a i)
      let loc : C →+* Ci := algebraMap C Ci
      let mki := Ideal.Quotient.mk (((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)).map loc)
      let qmi := Ideal.quotientMap (((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)).map loc) loc Ideal.le_comap_map
      obtain ⟨zi, hzi₀, hzil⟩ := hlifts i
      have hloc : Spec.map (CommRingCat.ofHom loc) ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)) =
          Spec.map (CommRingCat.ofHom (algebraMap S Ci)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
      have hxi : (zi ≫ pullback.fst f' f') ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap S Ci)) := by
        rw [Category.assoc, hzi₀]; exact hloc
      have hyi : (zi ≫ pullback.snd f' f') ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap S Ci)) := by
        rw [Category.assoc, ← pullback.condition, hzi₀]; exact hloc
      have hxil : Spec.map (CommRingCat.ofHom mki) ≫ (zi ≫ pullback.fst f' f') =
          Spec.map (CommRingCat.ofHom qmi) ≫ P₀ ≫ u₀ ≫ g' := by
        rw [← Category.assoc, hzil, Category.assoc, pullback.lift_fst]
      have hyil : Spec.map (CommRingCat.ofHom mki) ≫ (zi ≫ pullback.snd f' f') =
          Spec.map (CommRingCat.ofHom qmi) ≫ Q₀ ≫ u₀ ≫ g' := by
        rw [← Category.assoc, hzil, Category.assoc, pullback.lift_snd]
      let xi : SchemeHomOver (Scheme.specOver (𝒪 := S) Ci) f' := ⟨zi ≫ pullback.fst f' f', hxi⟩
      let yi : SchemeHomOver (Scheme.specOver (𝒪 := S) Ci) f' := ⟨zi ≫ pullback.snd f' f', hyi⟩
      have h1 := pieceChar C P.1 hP P₀ hP₀ (a i) xi.1 hxi hxil
      have h2 := pieceChar C Q.1 hQ Q₀ hQ₀ (a i) yi.1 hyi hyil

      have hPQ₀ : (L₀.mul t₀ p₀ q₀).1 ≫ g =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)))) ≫ (L.mul _ P Q).1 := by
        rw [hgL]
        have hn := congrArg Subtype.val (L.mul_natural (Scheme.specOver (𝒪 := S) C)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)))) ≫ Scheme.specOver (𝒪 := S) C)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C))))) rfl P Q)
        rw [schemeHomOverComp_coe] at hn
        rw [hn]
        exact mul_val_congr L ht₀ _ _ _ _ (by rw [schemeHomOverComp_coe]; exact hP₀)
          (by rw [schemeHomOverComp_coe]; exact hQ₀)

      let w : SchemeHomOver (Scheme.specOver (𝒪 := S) Ci) f' := L'.mul _ xi yi
      have hwl : Spec.map (CommRingCat.ofHom mki) ≫ w.1 =
          Spec.map (CommRingCat.ofHom qmi) ≫ (L₀.mul t₀ p₀ q₀).1 ≫ u₀ ≫ g' := by
        have hl := congrArg Subtype.val (L'.mul_natural (Scheme.specOver (𝒪 := S) Ci)
          (Spec.map (CommRingCat.ofHom mki) ≫ Scheme.specOver (𝒪 := S) Ci) (Spec.map (CommRingCat.ofHom mki)) rfl xi yi)
        rw [schemeHomOverComp_coe] at hl
        rw [hl]
        have hr1 := hu₀hom t₀ p₀ q₀
        rw [← Category.assoc ((L₀.mul t₀ p₀ q₀).1), hr1, hg'L]
        have hr2 := congrArg Subtype.val (L'.mul_natural (t₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))
          (Spec.map (CommRingCat.ofHom qmi) ≫ t₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))
          (Spec.map (CommRingCat.ofHom qmi)) rfl
          ⟨(⟨p₀.1 ≫ u₀, by rw [Category.assoc, hu₀]; exact p₀.2⟩ : SchemeHomOver t₀ f'₀).1 ≫ g',
            by rw [Category.assoc, hg'.w, ← Category.assoc,
              (show (⟨p₀.1 ≫ u₀, by rw [Category.assoc, hu₀]; exact p₀.2⟩ : SchemeHomOver t₀ f'₀).1 ≫ f'₀ = t₀ from
                by rw [Category.assoc, hu₀]; exact p₀.2)]⟩
          ⟨(⟨q₀.1 ≫ u₀, by rw [Category.assoc, hu₀]; exact q₀.2⟩ : SchemeHomOver t₀ f'₀).1 ≫ g',
            by rw [Category.assoc, hg'.w, ← Category.assoc,
              (show (⟨q₀.1 ≫ u₀, by rw [Category.assoc, hu₀]; exact q₀.2⟩ : SchemeHomOver t₀ f'₀).1 ≫ f'₀ = t₀ from
                by rw [Category.assoc, hu₀]; exact q₀.2)]⟩)
        rw [schemeHomOverComp_coe] at hr2
        rw [hr2]
        refine mul_val_congr L' ?_ _ _ _ _ ?_ ?_
        · rw [ht₀]
          change Spec.map (CommRingCat.ofHom mki) ≫ Spec.map (CommRingCat.ofHom (algebraMap S Ci)) =
            Spec.map (CommRingCat.ofHom qmi) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap S S₀)).map (algebraMap S C)))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap S C))
          simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rfl
        · rw [schemeHomOverComp_coe, schemeHomOverComp_coe]; exact hxil
        · rw [schemeHomOverComp_coe, schemeHomOverComp_coe]; exact hyil
      have h3 := pieceChar C (L.mul _ P Q).1 hPQ (L₀.mul t₀ p₀ q₀).1 hPQ₀ (a i) w.1 w.2 hwl
      rw [hÑpt C _ hPQ, h3]
      have hr := congrArg Subtype.val (L'.mul_natural (Scheme.specOver (𝒪 := S) C)
        (Spec.map (CommRingCat.ofHom loc) ≫ Scheme.specOver (𝒪 := S) C) (Spec.map (CommRingCat.ofHom loc)) rfl
        (mapPt Ñ hÑf P) (mapPt Ñ hÑf Q))
      rw [schemeHomOverComp_coe] at hr
      change _ = Spec.map (CommRingCat.ofHom loc) ≫ (L'.mul _ (mapPt Ñ hÑf P) (mapPt Ñ hÑf Q)).1
      rw [hr, Subtype.coe_eta, ← nsmulPt_eq_nsmul, nsmulPt_mul L' hc']
      refine mul_val_congr L' hloc.symm _ _ _ _ ?_ ?_
      · rw [schemeHomOverComp_coe, mapPt_coe, hÑpt C _ hP, h1, nsmulPt_eq_nsmul]
      · rw [schemeHomOverComp_coe, mapPt_coe, hÑpt C _ hQ, h2, nsmulPt_eq_nsmul]
    intro T t P Q
    exact congrArg Subtype.val (mapPt_mul_of_affine L L' Ñ hÑf hom_affine t P Q)
  ·
    have key : ∀ (C : CommRingCat.{0}) (t' : Spec C ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t' f₀),
        P.1 ≫ g ≫ Ñ = (nsmulPt L'₀ t' (N ^ μ) (mapPt u₀ hu₀ P)).1 ≫ g' := by
      intro C t' P
      obtain ⟨inst₀, ht'⟩ := exists_algebra_eq_specOver (R := S₀) C t'
      subst ht'
      letI instB : Algebra S C := ((algebraMap S₀ C).comp (algebraMap S S₀)).toAlgebra
      have halg : Spec.map (CommRingCat.ofHom (algebraMap S₀ C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)) =
          Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have hP : (P.1 ≫ g) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
        rw [Category.assoc, hg.w, ← Category.assoc, P.2]; exact halg
      let J : Ideal C := (RingHom.ker (algebraMap S S₀)).map (algebraMap S C)
      have hx : (P.1 ≫ u₀ ≫ g') ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
        rw [Category.assoc, Category.assoc, hg'.w, ← Category.assoc u₀, hu₀, ← Category.assoc, P.2]; exact halg
      have hc := hchar C (P.1 ≫ g) hP (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1)
        (by rw [Category.assoc]) (P.1 ≫ u₀ ≫ g') hx (by rw [Category.assoc])
      rw [← Category.assoc, hÑpt C (P.1 ≫ g) hP, hc, ← nsmulPt_eq_nsmul,
        nsmulPt_comp_of_mul_comp (algebraMap S S₀) L' L'₀ g' hg'.w hg'L]
      exact nsmulPt_val_congr L' halg.symm _ _ _ (by simp only [mapPt_coe, Category.assoc])

    refine A₀.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
    have hi := key (A₀.affineOpenCover.X i) (A₀.affineOpenCover.f i ≫ f₀) ⟨A₀.affineOpenCover.f i, rfl⟩
    change A₀.affineOpenCover.f i ≫ g ≫ Ñ = A₀.affineOpenCover.f i ≫ u₀ ≫ L'₀.schemeNsmul (N ^ μ) ≫ g'
    rw [hi, nsmulPt_eq_nsmul, nsmul_val, mapPt_coe, Category.assoc, Category.assoc]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero (solution)
