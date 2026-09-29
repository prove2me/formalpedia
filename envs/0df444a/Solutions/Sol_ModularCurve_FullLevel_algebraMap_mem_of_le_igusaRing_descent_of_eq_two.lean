-- Prove2me | solution 1 for ModularCurve.FullLevel.algebraMap_mem_of_le_igusaRing_descent_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/fa34b565-b3a0-53bd-8572-e4ad5eb8ddc4

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent_of_eq_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E150C

p2m_open "Polynomial AlgebraicGeometry.Polynomial IsLocalRing"

theorem exists_pow_eq_one_of_isAlgebraic_of_finite {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (x : K) (hx : IsAlgebraic F x) (hx0 : x ≠ 0) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  classical
  have hint : IsIntegral F x := hx.isIntegral
  let S := Algebra.adjoin F ({x} : Set K)
  haveI : Module.Finite F ↥S := ⟨(Submodule.fg_top _).mpr hint.fg_adjoin_singleton⟩
  haveI : Finite ↥S := Module.finite_of_finite F
  let s : ↥S := ⟨x, Algebra.self_mem_adjoin_singleton F x⟩
  have hs0 : s ≠ 0 := fun h => hx0 (congrArg Subtype.val h)

  have hfield : IsField ↥S := Finite.isDomain_to_isField ↥S
  obtain ⟨t, ht⟩ := hfield.mul_inv_cancel hs0
  let u : (↥S)ˣ := ⟨s, t, ht, by rw [mul_comm]; exact ht⟩
  haveI : Finite (↥S)ˣ := inferInstance
  obtain ⟨n, hn, hun⟩ := (isOfFinOrder_of_finite u).exists_pow_eq_one
  refine ⟨n, hn, ?_⟩
  have : (u ^ n : (↥S)ˣ).val = 1 := by rw [hun]; rfl
  have : s ^ n = 1 := by simpa [Units.val_pow_eq_pow_val] using this
  simpa [s] using congrArg Subtype.val this

theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) (a : A) (p : ℤ[X]) :
    g (aeval a p) = aeval (g a) p := by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂, RingHom.ext_int (g.comp (algebraMap ℤ A)) (algebraMap ℤ B)]

theorem exists_pow_sub_one_mem_maximalIdeal (q : ℕ) [hq2 : Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hqA : (q : ↥A) ∈ maximalIdeal ↥A)
    (a : ↥A) (ha : IsUnit a) : ∃ n : ℕ, 0 < n ∧ a ^ n - 1 ∈ maximalIdeal ↥A := by
  classical
  let κ := ResidueField ↥A
  haveI hchar : CharP κ q := by
    rw [CharP.charP_iff_prime_eq_zero hq2.out]
    rw [← map_natCast (residue ↥A), residue_eq_zero_iff]
    exact (mem_maximalIdeal _).mp hqA
  letI : Algebra (ZMod q) κ := ZMod.algebra κ q
  have hab0 : residue ↥A a ≠ 0 := (residue_ne_zero_iff_isUnit a).mpr ha

  have halgQ : IsAlgebraic ℚ ((a : AlgebraicClosure ℚ)) := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic _
  have halgZ : IsAlgebraic ℤ ((a : AlgebraicClosure ℚ)) := (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨p, hp0, hpa⟩ := halgZ
  let pP : ℤ[X] := p.primPart
  have hprim : pP.IsPrimitive := isPrimitive_primPart p
  have hpPa : aeval (a : AlgebraicClosure ℚ) pP = 0 := by
    have h := p.eq_C_content_mul_primPart
    have : aeval (a : AlgebraicClosure ℚ) p = (p.content : AlgebraicClosure ℚ) * aeval (a : AlgebraicClosure ℚ) pP := by
      conv_lhs => rw [h]
      rw [map_mul, aeval_C]; rfl
    rw [hpa] at this
    have hc : (p.content : AlgebraicClosure ℚ) ≠ 0 := by
      rw [Int.cast_ne_zero]; exact (Polynomial.content_eq_zero_iff).not.mpr hp0
    exact (mul_eq_zero.mp this.symm).resolve_left hc

  have hpPa' : aeval a pP = 0 := by
    have : algebraMap ↥A (AlgebraicClosure ℚ) (aeval a pP) = 0 := by
      rw [map_aeval_int]; exact hpPa
    exact Subtype.ext this
  have hres : aeval (residue ↥A a) pP = 0 := by
    have h := map_aeval_int (residue ↥A) a pP
    rw [hpPa', map_zero] at h
    exact h.symm

  let pq : (ZMod q)[X] := pP.map (Int.castRingHom (ZMod q))
  have hpq0 : pq ≠ 0 := by
    intro h0
    apply hq2.out.ne_one
    have hdvd : C (q : ℤ) ∣ pP := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have : (pP.coeff i : ZMod q) = 0 := by
        have := congrArg (fun r => Polynomial.coeff r i) h0
        simpa [pq, Polynomial.coeff_map] using this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp this
    have hu := hprim (q : ℤ) hdvd
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact_mod_cast h1
    · exfalso; have := hq2.out.pos; omega
  have hres' : aeval (residue ↥A a) pq = 0 := by
    rw [aeval_def, Polynomial.eval₂_map, RingHom.ext_int ((algebraMap (ZMod q) κ).comp (Int.castRingHom (ZMod q))) (algebraMap ℤ κ),
      ← aeval_def]
    exact hres
  have halg : IsAlgebraic (ZMod q) (residue ↥A a) := ⟨pq, hpq0, hres'⟩
  obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_of_isAlgebraic_of_finite (residue ↥A a) halg hab0
  refine ⟨n, hn, ?_⟩
  rw [← residue_eq_zero_iff]
  · rw [map_sub, map_pow, hpow, map_one, sub_self]

end E150C

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    (ℓ : CuspidalType.ProjLine q) (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg ℓ) :
    ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ V := by
  intro a
  classical

  obtain ⟨γ, hγ, -, hOℓ⟩ := hIg ℓ
  have memℓ : ∀ g : ↥(fieldBar q M'), g ∈ OIg ℓ ↔ levelAutBar q M' ζ γ g ∈ OIg (lineInfty q) := by
    intro g; rw [hOℓ]; exact ValuationSubring.mem_comap
  obtain ⟨R, hR⟩ := ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr
  have constℓ : ∀ x : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x ∈ OIg ℓ ↔ x ∈ A := by
    intro x; rw [memℓ, AlgEquiv.commutes, ← hR]; exact R.algebraMap_mem_iff x
  have hcoe : ∀ b : A₀, ((algebraMap A₀ ↥F₀ b : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι b : ↥A) : AlgebraicClosure ℚ) := hj₀

  by_contra haV
  have hinvV : (algebraMap A₀ ↥F₀ a)⁻¹ ∈ V := (V.mem_or_inv_mem _).resolve_left haV
  have ha0 : (algebraMap A₀ ↥F₀ a : ↥F₀) ≠ 0 := fun h => haV (h.symm ▸ V.zero_mem)
  have hιa0 : ((ι a : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h; apply ha0; apply Subtype.ext; rw [hcoe, h, map_zero]; rfl
  have hιinv : (((ι a : ↥A) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
    have := hV _ hinvV
    rw [show (((algebraMap A₀ ↥F₀ a)⁻¹ : ↥F₀) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (((ι a : ↥A) : AlgebraicClosure ℚ))⁻¹ from by
          rw [map_inv₀, ← hcoe]; rfl, constℓ] at this
    exact this
  have hu : IsUnit (ι a) :=
    ⟨⟨ι a, ⟨_, hιinv⟩, Subtype.ext (mul_inv_cancel₀ hιa0), Subtype.ext (inv_mul_cancel₀ hιa0)⟩, rfl⟩

  have hqA : (q : ↥A) ∈ maximalIdeal ↥A := by
    obtain ⟨h, hm⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hA
    convert hm using 1
    rfl
  obtain ⟨n, hn, hpow⟩ := E150C.exists_pow_sub_one_mem_maximalIdeal q A hqA (ι a) hu

  set c : ↥F₀ := algebraMap A₀ ↥F₀ a with hc
  have hcn : ((c ^ n - 1 : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((((ι a) ^ n - 1 : ↥A)) : AlgebraicClosure ℚ) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, OneMemClass.coe_one, hc, hcoe,
      AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, OneMemClass.coe_one, map_sub, map_pow, map_one]
  have hnonunit : (c ^ n - 1 : ↥F₀) ∈ V.nonunits := by
    apply ValuationSubring.nonunits_le_nonunits.mpr (fun f hf => (ValuationSubring.mem_comap).mpr (hV f hf) :
      V ≤ (OIg ℓ).comap F₀.subtype)
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases h0 : ((ι a) ^ n - 1 : ↥A) = 0
    · left; apply Subtype.ext; change ((c ^ n - 1 : ↥F₀) : ↥(fieldBar q M')) = 0; rw [hcn, h0]; simp
    · right
      rw [ValuationSubring.mem_comap]
      intro hmem
      have : (((c ^ n - 1 : ↥F₀) : ↥(fieldBar q M')))⁻¹ ∈ OIg ℓ := by exact_mod_cast hmem
      rw [hcn, ← map_inv₀, constℓ] at this

      have h0' : ((((ι a) ^ n - 1 : ↥A)) : AlgebraicClosure ℚ) ≠ 0 := fun h => h0 (Subtype.ext h)
      have hunit : IsUnit (((ι a) ^ n - 1 : ↥A)) :=
        ⟨⟨_, ⟨_, this⟩, Subtype.ext (mul_inv_cancel₀ h0'), Subtype.ext (inv_mul_cancel₀ h0')⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mp hpow hunit

  have hvc : 1 < V.valuation c := by
    rw [lt_iff_not_ge]; intro h; exact haV ((V.valuation_le_one_iff _).mp h)
  have hvcn : 1 < V.valuation (c ^ n) := by
    rw [map_pow]; exact one_lt_pow₀ hvc hn.ne'
  have hv : V.valuation (c ^ n - 1) = V.valuation (c ^ n) := by
    rw [sub_eq_add_neg]
    apply Valuation.map_add_eq_of_lt_left
    rw [Valuation.map_neg, map_one]; exact hvcn
  have : (c ^ n - 1 : ↥F₀) ∈ V := V.nonunits_subset hnonunit
  rw [← V.valuation_le_one_iff, hv] at this
  exact (not_le.mpr hvcn) this

end S_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent_of_eq_two (solution)
