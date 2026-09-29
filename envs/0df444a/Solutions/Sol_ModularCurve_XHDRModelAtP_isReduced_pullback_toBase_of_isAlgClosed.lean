-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isReduced_pullback_toBase_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/07a788e2-eaf6-58d9-b7d2-30fb3a22a14a

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq
import Theorems.Thm_AlgebraicGeometry_isReduced_pullback_of_isReduced_pullback_of_perfectField
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isReduced_pullback_toBase_of_isAlgClosed
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_isReduced_pullback_toBase_of_isAlgClosed.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.R XHDRLevel.toBase XHDRLevel.ΓM XHDRModelAtP qExpFunctionFieldC jqModC DRLevel.exists_place_residueField_ringHom_comp_eq"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "fibre_reduced lfp smooth_generic comp"
namespace GredH
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

variable (p : ℕ) [Fact p.Prime]

theorem isUnit_natCast_R_of_prime_ne {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : IsUnit ((ℓ : ℤ) : R p) := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  have hmem : (ℓ : ℤ) ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
    intro h
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at h
    have : (p : ℤ).natAbs ∣ (ℓ : ℤ).natAbs := Int.natAbs_dvd_natAbs.mpr h
    simp only [Int.natAbs_natCast] at this
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp this).symm
  simpa using IsLocalization.map_units (R p) (⟨(ℓ : ℤ), hmem⟩ : (Ideal.span {(p : ℤ)}).primeCompl)

theorem charZero_of_ringHom_of_ne_zero {k : Type} [Field k] (toκ : R p →+* k) (hp : (p : k) ≠ 0) : CharZero k := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k ℓ with hℓℓ | rfl
  · exfalso
    by_cases hℓp : ℓ = p
    · subst hℓp; exact hp (CharP.cast_eq_zero k ℓ)
    · have hu := (isUnit_natCast_R_of_prime_ne p hℓℓ hℓp).map toκ
      rw [map_intCast, Int.cast_natCast, CharP.cast_eq_zero k ℓ] at hu
      exact not_isUnit_zero hu
  · exact CharP.charP_to_charZero k

theorem ringHom_eq_algebraMap_comp {k : Type} [Field k] [CharZero k] (toκ : R p →+* k) :
    toκ = (algebraMap ℚ k).comp (algebraMap (R p) ℚ) := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)

end ModularCurve.XHDRModelAtP.GredH

open ModularCurve.XHDRModelAtP.GredH

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (XHDRLevel.R p))) :
    IsReduced (pullback (XHDRLevel.toBase p (XHDRLevel.ΓM M H) hj) x) := by
  classical
  haveI : LocallyOfFinitePresentation (toBase p (ΓM M H) hj) := 𝔛.lfp
  haveI : LocallyOfFiniteType (toBase p (ΓM M H) hj) := inferInstance
  obtain ⟨toκ, rfl⟩ : ∃ toκ : R p →+* k, x = Spec.map (CommRingCat.ofHom toκ) :=
    ⟨(Spec.preimage x).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  by_cases hp : (p : k) = 0
  · haveI : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hp
    obtain ⟨A, hA, hch, hac, ρ, hρ, φ, hφ⟩ := ModularCurve.DRLevel.exists_place_residueField_ringHom_comp_eq p k toκ
    haveI := hch
    haveI := hac
    haveI : IsReduced (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) :=
      𝔛.fibre_reduced A hA ρ hρ
    obtain rfl : toκ = φ.comp ((residue ↥A).comp ρ) := hφ.symm
    refine AlgebraicGeometry.isReduced_pullback_of_isReduced_pullback_of_perfectField (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))) φ _ ?_
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  · haveI := charZero_of_ringHom_of_ne_zero p toκ hp
    obtain rfl := ringHom_eq_algebraMap_comp p toκ
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    set z := Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))
    set y := Spec.map (CommRingCat.ofHom (algebraMap ℚ k))
    haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) z) := 𝔛.smooth_generic
    haveI : Smooth (pullback.snd (toBase p (ΓM M H) hj) z) := SmoothOfRelativeDimension.smooth 1 _
    haveI : Smooth (pullback.snd (pullback.snd (toBase p (ΓM M H) hj) z) y) := inferInstance
    haveI : IsReduced (pullback (pullback.snd (toBase p (ΓM M H) hj) z) y) :=
      AlgebraicGeometry.isReduced_of_smooth_of_field (pullback.snd (pullback.snd (toBase p (ΓM M H) hj) z) y)
    exact isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) z y).inv

#print axioms solution

end S_ModularCurve_XHDRModelAtP_isReduced_pullback_toBase_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isReduced_pullback_toBase_of_isAlgClosed (solution)
