-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurveDegeneration_of_not_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e4ac1b29-a655-5a46-b707-fb971c7147d5

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_ModularCurve_finite_ssPlacesQExp
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurveDegeneration_of_not_smooth
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel"

open scoped MatrixGroups

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace HbadH

open IsLocalRing

theorem exists_ringHom_charP_of_not_smooth
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    {k : Type} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R p)))
    (hns : ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) s)) :
    ∃ (toκ : R p →+* k) (_ : CharP k p), s = Spec.map (CommRingCat.ofHom toκ) := by
  classical
  let toκ : R p →+* k := (Spec.preimage s).hom
  have hs : Spec.map (CommRingCat.ofHom toκ) = s := by
    simp only [toκ, CommRingCat.ofHom_hom, Spec.map_preimage]
  letI : Algebra (R p) k := toκ.toAlgebra
  have hpp : p.Prime := Fact.out
  rcases GaloisRep.charZero_or_charP_of_algebra_ratLocalizedAt p k with h0 | hq
  · exfalso
    apply hns
    haveI := h0
    haveI := GaloisRep.isFractionRing_ratLocalizedAt p
    haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
    haveI := GaloisRep.ratLocalizedAt.isLocalRing hpp
    have hinj : Function.Injective toκ := by
      rw [RingHom.injective_iff_ker_eq_bot]
      by_contra hne
      have hprime : (RingHom.ker toκ).IsPrime := RingHom.ker_isPrime toκ
      have hmax : (RingHom.ker toκ).IsMaximal := by
        haveI := hprime
        exact IsPrime.to_maximal_ideal hne
      have heq : RingHom.ker toκ = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal hmax
      have hqmem : ((p : ℕ) : R p) ∈ RingHom.ker toκ := by
        rw [heq, GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hpp]
        exact Ideal.subset_span rfl
      rw [RingHom.mem_ker, map_natCast] at hqmem
      exact hpp.ne_zero ((Nat.cast_eq_zero (R := k)).mp hqmem)
    let f : ℚ →+* k := IsFractionRing.lift hinj
    have hf : f.comp (algebraMap (R p) ℚ) = toκ :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    have hs' : s = Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)) := by
      rw [← hs, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
    rw [hs']
    haveI := 𝔛.smooth_generic
    have hsnd : pullback.snd (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))) =
        (pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))
          (Spec.map (CommRingCat.ofHom f))).inv ≫
        pullback.snd (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))
          (Spec.map (CommRingCat.ofHom f)) := by
      rw [← pullbackLeftPullbackSndIso_hom_snd, Iso.inv_hom_id_assoc]
    rw [hsnd]
    infer_instance
  · exact ⟨toκ, hq, hs.symm⟩

theorem ringHom_ext_charP (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] (f g : R p →+* k) : f = g := by
  apply RingHom.ext
  intro x
  have hx : (x : ℚ).den.Coprime p := x.2
  have hden : (((x : ℚ).den : ℕ) : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    intro h
    have := Nat.Coprime.eq_one_of_dvd (hx.symm) |> fun e => e h
    exact (Fact.out : p.Prime).one_lt.ne' this

  have hnum : (((x : ℚ).num : ℚ)).den.Coprime p := by simp
  have hden' : ((((x : ℚ).den : ℕ) : ℚ)).den.Coprime p := by simp
  have hmul : x * ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ⟨((x : ℚ).num : ℚ), hnum⟩ := by
    apply Subtype.ext
    show (x : ℚ) * ((x : ℚ).den : ℚ) = ((x : ℚ).num : ℚ)
    exact Rat.mul_den_eq_num (x : ℚ)
  have hf := congrArg f hmul
  have hg := congrArg g hmul
  rw [map_mul] at hf hg
  have hfd : f ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ((x : ℚ).den : k) := by
    rw [show (⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ : R p) = (((x : ℚ).den : ℕ) : R p) from Subtype.ext (by simp), map_natCast]
  have hgd : g ⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ = ((x : ℚ).den : k) := by
    rw [show (⟨(((x : ℚ).den : ℕ) : ℚ), hden'⟩ : R p) = (((x : ℚ).den : ℕ) : R p) from Subtype.ext (by simp), map_natCast]
  have hfn : f ⟨((x : ℚ).num : ℚ), hnum⟩ = ((x : ℚ).num : k) := by
    rw [show (⟨((x : ℚ).num : ℚ), hnum⟩ : R p) = (((x : ℚ).num : ℤ) : R p) from Subtype.ext (by simp), map_intCast]
  have hgn : g ⟨((x : ℚ).num : ℚ), hnum⟩ = ((x : ℚ).num : k) := by
    rw [show (⟨((x : ℚ).num : ℚ), hnum⟩ : R p) = (((x : ℚ).num : ℤ) : R p) from Subtype.ext (by simp), map_intCast]
  rw [hfd, hfn] at hf
  rw [hgd, hgn] at hg
  exact mul_right_cancel₀ hden (hf.trans hg.symm)

section ValRing

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

include hA in
theorem natCast_mem_maximalIdeal : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA

include hA in

theorem charP_residueField : CharP (ResidueField ↥A) p := by
  refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr ?_
  rw [← map_natCast (residue ↥A), residue_eq_zero_iff]
  exact natCast_mem_maximalIdeal p A hA

include hA in

theorem isUnit_natCast_of_coprime {n : ℕ} (hn : n.Coprime p) : IsUnit ((n : ℕ) : ↥A) := by
  by_contra hnu
  have hmem : ((n : ℕ) : ↥A) ∈ maximalIdeal ↥A := (mem_maximalIdeal _).mpr hnu
  have hp := natCast_mem_maximalIdeal p A hA
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (n : ℤ) + b * (p : ℤ) = 1 := by
    refine ⟨Int.gcdA n p, Int.gcdB n p, ?_⟩
    have := Int.gcd_eq_gcd_ab (n : ℤ) (p : ℤ)
    rw [Int.gcd_natCast_natCast, hn] at this
    push_cast at this
    linarith
  have h1 : (1 : ↥A) ∈ maximalIdeal ↥A := by
    have : (a : ↥A) * (n : ℕ) + (b : ↥A) * (p : ℕ) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ↥A)) hab
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp)
  exact (maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

include hA in

theorem mem_of_liesOverPrime (x : R p) : algebraMap ℚ (AlgebraicClosure ℚ) (x : ℚ) ∈ A := by
  have hx : (x : ℚ).den.Coprime p := x.2
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime p A hA hx
  have hq : (x : ℚ) = ((x : ℚ).num : ℚ) * (((x : ℚ).den : ℚ))⁻¹ := by
    rw [← div_eq_mul_inv, Rat.num_div_den]
  rw [hq, map_mul, map_inv₀, map_intCast, map_natCast]
  refine A.toSubring.mul_mem (intCast_mem A.toSubring _) ?_
  have : ((((x : ℚ).den : ℕ) : AlgebraicClosure ℚ))⁻¹ = ((↑(u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) := by
    apply inv_eq_of_mul_eq_one_right
    have h1 : (((x : ℚ).den : ℕ) : AlgebraicClosure ℚ) = ((↑u : ↥A) : AlgebraicClosure ℚ) := by
      rw [hu]; rfl
    rw [h1]
    show ((↑u : ↥A) : AlgebraicClosure ℚ) * ((↑u⁻¹ : ↥A) : AlgebraicClosure ℚ) = 1
    rw [← show (((↑u * ↑u⁻¹ : ↥A)) : AlgebraicClosure ℚ) = ((↑u : ↥A) : AlgebraicClosure ℚ) * ((↑u⁻¹ : ↥A) : AlgebraicClosure ℚ) from rfl,
      Units.mul_inv]
    rfl
  rw [this]
  exact SetLike.coe_mem _

end ValRing

section Embed

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

noncomputable def rho : R p →+* ↥A :=
  ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (GaloisRep.ratLocalizedAt p).subtype).codRestrict A.toSubring
    (fun x => mem_of_liesOverPrime p A hA x)

theorem rho_spec : A.subtype.comp (rho p A hA) = algebraMap (R p) (AlgebraicClosure ℚ) := by
  ext x
  rfl

include hA in

theorem isAlgebraic_residueField :
    letI := charP_residueField p A hA
    letI := ZMod.algebra (ResidueField ↥A) p
    Algebra.IsAlgebraic (ZMod p) (ResidueField ↥A) := by
  letI := charP_residueField p A hA
  letI := ZMod.algebra (ResidueField ↥A) p
  refine ⟨fun y => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective y

  have halgQ : IsAlgebraic ℚ ((x : ↥A) : AlgebraicClosure ℚ) := by
    have h := @Algebra.IsAlgebraic.isAlgebraic ℚ (AlgebraicClosure ℚ) _ _ _ (AlgebraicClosure.isAlgebraic ℚ)
      ((x : ↥A) : AlgebraicClosure ℚ)
    convert h
    rfl
    rfl
  have halgZ : IsAlgebraic ℤ ((x : ↥A) : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨f, hf0, hfx⟩ := halgZ
  set g := f.primPart with hg
  have hgprim : g.IsPrimitive := f.isPrimitive_primPart
  have hgx : Polynomial.aeval ((x : ↥A) : AlgebraicClosure ℚ) g = 0 := by
    have h := f.eq_C_content_mul_primPart
    rw [h, map_mul, Polynomial.aeval_C] at hfx
    rcases mul_eq_zero.mp hfx with h1 | h1
    · exfalso
      rw [eq_intCast, Int.cast_eq_zero, Polynomial.content_eq_zero_iff] at h1
      exact hf0 h1
    · exact h1

  have hgA : Polynomial.aeval x g = 0 := by
    apply A.subtype_injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int (A.subtype.comp (algebraMap ℤ ↥A)) (algebraMap ℤ (AlgebraicClosure ℚ)), ← Polynomial.aeval_def]
    exact hgx
  have hgres : Polynomial.eval₂ (algebraMap ℤ (ResidueField ↥A)) (residue ↥A x) g = 0 := by
    have := congrArg (residue ↥A) hgA
    rwa [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int ((residue ↥A).comp (algebraMap ℤ ↥A)) (algebraMap ℤ (ResidueField ↥A))] at this

  set gp : Polynomial (ZMod p) := g.map (Int.castRingHom (ZMod p)) with hgp
  have hgp0 : gp ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ g := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have : gp.coeff i = 0 := by rw [h0, Polynomial.coeff_zero]
      rw [hgp, Polynomial.coeff_map, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    have hu := (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hgprim) (p : ℤ) hdvd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact (Fact.out : p.Prime).one_lt.ne' hu
  refine ⟨gp, hgp0, ?_⟩
  rw [Polynomial.aeval_def, hgp, Polynomial.eval₂_map,
    RingHom.ext_int ((algebraMap (ZMod p) (ResidueField ↥A)).comp (Int.castRingHom (ZMod p))) (algebraMap ℤ (ResidueField ↥A))]
  exact hgres

include hA in

theorem exists_ringHom_residueField (k : Type) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ ι : ResidueField ↥A →+* k, True := by
  letI := charP_residueField p A hA
  letI := ZMod.algebra (ResidueField ↥A) p
  letI := ZMod.algebra k p
  haveI := isAlgebraic_residueField p A hA
  exact ⟨(IsAlgClosed.lift (R := ZMod p) (S := ResidueField ↥A) (M := k) : ResidueField ↥A →ₐ[ZMod p] k).toRingHom, trivial⟩

end Embed

theorem gamma1_le_gammaH (N : ℕ) (H' : Subgroup (ZMod N)ˣ) : CongruenceSubgroup.Gamma1 N ≤ CohCarrier.GammaH N H' := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨CongruenceSubgroup.Gamma1_in_Gamma0 N hA, ?_⟩
  have h1 : CohCarrier.gamma0Units N ⟨A, CongruenceSubgroup.Gamma1_in_Gamma0 N hA⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact ((CongruenceSubgroup.Gamma1_mem N A).mp hA).2.1
  rw [h1]
  exact one_mem H'

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

section Block

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) (𝔛 : XHDRModelAtP p M H hpM hj)

theorem sectionFibre_fst (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    sectionFibre ε toκ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) =
      Spec.map (CommRingCat.ofHom toκ) ≫ ε.1 :=
  pullback.lift_fst _ _ _

include hpM hpM2 in

theorem not_dvd_div : ¬ p ∣ M / p := by
  intro h
  apply hpM2
  obtain ⟨c, hc⟩ := h
  have : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
  rw [this, hc]
  exact ⟨c, by ring⟩

include hpM2 in

theorem block_residueField (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hns : ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))))) :
    letI k₀ := ResidueField ↥A
    letI s₀ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))
    ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k₀)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k₀))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (toBase p (ΓM M H) hj) s₀)) (i₂ : SchemeHomOver c₂ (pullback.snd (toBase p (ΓM M H) hj) s₀))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback (toBase p (ΓM M H) hj) s₀), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint 𝔛.εinf s₀).1).base (IsLocalRing.closedPoint k₀) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst (toBase p (ΓM M H) hj) s₀ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s₀).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s₀)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst (toBase p (ΓM M H) hj) s₀ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s₀).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s₀)) =
          connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) s₀ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s₀).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s₀))
            (((sectionFibrePoint 𝔛.εinf s₀).1).base (IsLocalRing.closedPoint k₀)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst (toBase p (ΓM M H) hj) s₀ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s₀).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s₀)) =
          ((pullback.fst (toBase p (ΓM M H) hj) s₀ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s₀).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s₀)) \
            connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) s₀ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s₀).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s₀))
              (((sectionFibrePoint 𝔛.εinf s₀).1).base (IsLocalRing.closedPoint k₀)) ∧
        (∃ W₁ : (pullback (toBase p (ΓM M H) hj) s₀).Opens, (W₁ : Set ↥(pullback (toBase p (ΓM M H) hj) s₀)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback (toBase p (ΓM M H) hj) s₀).Opens, (W₂ : Set ↥(pullback (toBase p (ΓM M H) hj) s₀)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by
  classical
  haveI := 𝔛.isProper0; haveI := 𝔛.smooth0; haveI := 𝔛.flat; haveI := 𝔛.lfp; haveI := 𝔛.isProper
  set toκ := (residue ↥A).comp ρ with htoκ

  let C₀ : Scheme.{0} := fibre (Γ := ΓN p M H hpM) (hj := hj) toκ
  let c₀ : C₀ ⟶ Spec (CommRingCat.of (ResidueField ↥A)) := pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom toκ))
  haveI hp0 : IsProper c₀ := inferInstance
  haveI hs0 : SmoothOfRelativeDimension 1 c₀ := inferInstance
  haveI : IsIntegral C₀ := by
    haveI := 𝔛.efib_iso A hA ρ hρ
    haveI : IsIntegral (𝔛.Mfib A hA ρ hρ).C := (𝔛.Mfib A hA ρ hρ).isIntegral
    exact IsIntegral.of_isIso (𝔛.efib A hA ρ hρ)
  haveI : LocallyOfFiniteType c₀ := inferInstance
  have hgi0 : GeometricallyIntegral c₀ := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed c₀

  let i₁ : SchemeHomOver c₀ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) :=
    ⟨𝔛.comp A hA ρ hρ 0, 𝔛.comp_over A hA ρ hρ 0⟩
  let i₂ : SchemeHomOver c₀ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) :=
    ⟨𝔛.comp A hA ρ hρ 1, 𝔛.comp_over A hA ρ hρ 1⟩
  haveI : IsClosedImmersion i₁.1 := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI : IsClosedImmersion i₂.1 := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  have hcr : IsReduced (pullback i₁.1 i₂.1) := 𝔛.crossing_reduced A hA ρ hρ
  have hred : IsReduced (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))) := 𝔛.fibre_reduced A hA ρ hρ

  have hsec : (sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom toκ))).1 = sectionFibre 𝔛.εinf toκ := rfl
  set q := ((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom toκ))).1).base (IsLocalRing.closedPoint (ResidueField ↥A)) with hqdef
  have hq1 : q ∈ Set.range (𝔛.comp A hA ρ hρ 0).base :=
    𝔛.εinf_mem_comp0 A hA ρ hρ ⟨IsLocalRing.closedPoint _, by rw [hqdef, hsec]⟩
  have hqU : q ∈ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔛.smoothLocus :
      (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))).Opens) : Set _) := by
    show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ))).base q ∈ (𝔛.smoothLocus : Set _)
    apply 𝔛.εinf_mem_smoothLocus
    refine ⟨(Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint _), ?_⟩
    rw [hqdef, hsec, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sectionFibre_fst]

  haveI : Smooth (𝔛.smoothLocus.ι ≫ toBase p (ΓM M H) hj) := by
    haveI := 𝔛.smoothLocus_relDim
    infer_instance

  have hnotiso : ∀ (i : Fin 2), ¬ Function.Surjective (𝔛.comp A hA ρ hρ i).base := by
    intro i hsurj
    haveI : Surjective (𝔛.comp A hA ρ hρ i) := ⟨hsurj⟩
    haveI : IsClosedImmersion (𝔛.comp A hA ρ hρ i) := 𝔛.comp_isClosedImmersion A hA ρ hρ i
    haveI := hred
    haveI : IsIso (𝔛.comp A hA ρ hρ i) := isIso_of_isClosedImmersion_of_surjective _
    apply hns
    have : pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom toκ)) =
        inv (𝔛.comp A hA ρ hρ i) ≫ c₀ := by
      rw [IsIso.eq_inv_comp, 𝔛.comp_over A hA ρ hρ i]
    rw [this]
    infer_instance
  have hne₁ : ¬ Set.range i₁.1.base ⊆ Set.range i₂.1.base := fun h => hnotiso 1 (by
    intro z
    rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with hz | hz
    · exact h hz
    · exact hz)
  have hne₂ : ¬ Set.range i₂.1.base ⊆ Set.range i₁.1.base := fun h => hnotiso 0 (by
    intro z
    rcases 𝔛.comp_jointly_surjective A hA ρ hρ z with hz | hz
    · exact hz
    · exact h hz)
  obtain ⟨hU, hU₁, hU₂, hW₁, hW₂⟩ :=
    AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
      (toBase p (ΓM M H) hj) 𝔛.smoothLocus 𝔛.smoothLocus_maximal (Spec.map (CommRingCat.ofHom toκ)) hred
      c₀ c₀ i₁ i₂ (𝔛.comp_jointly_surjective A hA ρ hρ) hne₁ hne₂ q hq1 hqU

  have hn : 0 < Nat.card ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := by
    haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos).ne'⟩
    haveI : (ΓN p M H hpM).FiniteIndex := Subgroup.finiteIndex_of_le (HbadH.gamma1_le_gammaH _ _)
    haveI : NeZero M := inferInstance
    haveI : Nonempty ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := by
      obtain ⟨P, hP⟩ := ModularCurve.nonempty_ssPlacesQExp (M / p) (ΓN p M H hpM)
        (HbadH.gamma1_le_gammaH _ _) (CohCarrier.GammaH_le_Gamma0 _) p (not_dvd_div p M hpM hpM2) (ResidueField ↥A)
      exact ⟨(𝔛.nodeEquiv A hA ρ hρ).symm ⟨P, hP⟩⟩
    haveI : Finite ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) :=
      (ModularCurve.finite_ssPlacesQExp (ResidueField ↥A) p (ΓN p M H hpM)
        (HbadH.gamma1_le_gammaH _ _ (HbadH.T_mem_Gamma1 _))).to_subtype
    haveI : Finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) :=
      Finite.of_equiv _ (𝔛.nodeEquiv A hA ρ hρ).symm
    exact Nat.card_pos

  have hq2 : q ∉ Set.range (𝔛.comp A hA ρ hρ 1).base := by
    intro h2
    have hqc : q ∈ Set.range (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base := by
      obtain ⟨a, ha⟩ := hq1
      obtain ⟨b, hb⟩ := h2
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
      exact ⟨z, by rw [Scheme.Hom.comp_apply, hz1, ha]⟩
    rw [hU] at hqU
    exact hqU hqc
  exact ⟨C₀, C₀, c₀, c₀, hp0, hs0, hgi0, hp0, hs0, hgi0, i₁, i₂, inferInstance, inferInstance,
    Nat.card ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
    𝔛.comp_jointly_surjective A hA ρ hρ, hcr, rfl, hn, ⟨hq1, hq2⟩, hU, hU₁, hU₂, hW₁, hW₂⟩

end Block

end HbadH

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R p))), ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) s) →
      ∃ (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (toBase p (ΓM M H) hj) s)) (i₂ : SchemeHomOver c₂ (pullback.snd (toBase p (ΓM M H) hj) s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback (toBase p (ΓM M H) hj) s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s)) =
          connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s))
            (((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s)) =
          ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s)) \
            connectedComponentIn ((pullback.fst (toBase p (ΓM M H) hj) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (toBase p (ΓM M H) hj) s).Opens) : Set ↥(pullback (toBase p (ΓM M H) hj) s))
              (((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback (toBase p (ΓM M H) hj) s).Opens, (W₁ : Set ↥(pullback (toBase p (ΓM M H) hj) s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback (toBase p (ΓM M H) hj) s).Opens, (W₂ : Set ↥(pullback (toBase p (ΓM M H) hj) s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by
  intro k _ _ s hns
  classical
  haveI := 𝔛.isProper0; haveI := 𝔛.smooth0; haveI := 𝔛.flat; haveI := 𝔛.lfp; haveI := 𝔛.isProper

  obtain ⟨toκ, hchar, rfl⟩ := HbadH.exists_ringHom_charP_of_not_smooth p M H hpM hj 𝔛 s hns
  haveI := hchar

  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p :=
    ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI : CharP (IsLocalRing.ResidueField ↥A) p := HbadH.charP_residueField p A hA
  let ρ := HbadH.rho p A hA
  have hρ := HbadH.rho_spec p A hA
  obtain ⟨ι, -⟩ := HbadH.exists_ringHom_residueField p A hA k

  have htoκ : toκ = ι.comp ((IsLocalRing.residue ↥A).comp ρ) := HbadH.ringHom_ext_charP p _ _
  have hs : Spec.map (CommRingCat.ofHom toκ) =
      Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← htoκ]

  have hns₀ : ¬ Smooth (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) := by
    intro hsm
    apply hns
    rw [hs]
    have hsnd : pullback.snd (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) =
        (pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))
          (Spec.map (CommRingCat.ofHom ι))).inv ≫
        pullback.snd (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
          (Spec.map (CommRingCat.ofHom ι)) := by
      rw [← pullbackLeftPullbackSndIso_hom_snd, Iso.inv_hom_id_assoc]
    rw [hsnd]
    haveI := hsm
    infer_instance

  have h₀ := HbadH.block_residueField p M H hpM hpM2 hj 𝔛 A hA ρ hρ hns₀
  exact AlgebraicGeometry.exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed
    (toBase p (ΓM M H) hj) 𝔛.smoothLocus 𝔛.εinf (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) h₀ ι
    (Spec.map (CommRingCat.ofHom toκ)) hs

end S_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurveDegeneration_of_not_smooth
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurveDegeneration_of_not_smooth (solution)
