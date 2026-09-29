-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/81cef289-24ee-587b-a8e5-499dac902455

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_existsUnique_kroneckerRemainder
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section N1cE9Generic
open AlgebraicCurve IsLocalRing Polynomial

namespace N1cE9

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem HasValue.add (v : Place K F) {g g' : F} {a a' : K} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem HasValue.neg (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) :
    v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem HasValue.sub (v : Place K F) {g g' : F} {a a' : K} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g - g') (a - a') := by
  simpa only [sub_eq_add_neg] using HasValue.add v h (HasValue.neg v h')

theorem HasValue.pow (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using v.hasValue_one
  | succ n ih => simpa only [pow_succ] using ih.mul h

theorem hasValue_intCast (v : Place K F) (n : ℤ) : v.HasValue (n : F) (n : K) := by
  simpa only [map_intCast] using v.hasValue_algebraMap (n : K)

theorem hasValue_natCast (v : Place K F) (n : ℕ) : v.HasValue (n : F) (n : K) := by
  simpa only [map_natCast] using v.hasValue_algebraMap (n : K)

theorem hasValue_aeval (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) (p : Polynomial ℤ) :
    v.HasValue (aeval g p) (aeval a p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using HasValue.add v hp hq
  | monomial m z =>
    simp only [aeval_monomial, algebraMap_int_eq, eq_intCast]
    exact (hasValue_intCast v z).mul (HasValue.pow v h m)

theorem hasValue_eval₂ (v : Place K F) {g₁ g₂ : F} {a₁ a₂ : K} (h₁ : v.HasValue g₁ a₁)
    (h₂ : v.HasValue g₂ a₂) (P : Polynomial (Polynomial ℤ)) :
    v.HasValue (P.eval₂ (aeval g₁).toRingHom g₂) (P.eval₂ (aeval a₁).toRingHom a₂) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval₂_add] using HasValue.add v hp hq
  | monomial n p =>
    simp only [eval₂_monomial, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact (hasValue_aeval v h₁ p).mul (HasValue.pow v h₂ n)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem hasValue_of_ord_sub_pos (v : Place K F) {g : F} {c : K}
    (h : 0 < v.ord (g - algebraMap K F c)) : v.HasValue g c := by
  rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos]
  have hne : g - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  refine ⟨?_, Or.inr h⟩
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring := mem_of_ord_nonneg v hne h.le
  have hg : g = (g - algebraMap K F c) + algebraMap K F c := by ring
  rw [hg]
  exact add_mem hmem (v.algebraMap_mem' c)

theorem HasValue.sub_mem_maximalIdeal (v : Place K F) {g : F} {c : K} (h : v.HasValue g c)
    (hm : g - algebraMap K F c ∈ v.toValuationSubring) :
    (⟨g - algebraMap K F c, hm⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
  rw [← residue_eq_zero_iff]
  have hx : (⟨g - algebraMap K F c, hm⟩ : v.toValuationSubring)
      = ⟨g, h.mem⟩ - algebraMap K v.toValuationSubring c := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap]
  rw [hx, map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]

theorem adicValuation_eq_exp_neg_ord (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

theorem mem_maximalIdeal_pow_iff (v : Place K F) (x : v.toValuationSubring) (hx : (x : F) ≠ 0) (n : ℕ) :
    x ∈ maximalIdeal v.toValuationSubring ^ n ↔ (n : ℤ) ≤ v.ord (x : F) := by
  rw [← Ideal.dvd_span_singleton, ← Place.heightOneSpectrum_asIdeal,
    ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, ← Place.adicValuation_coe,
    adicValuation_eq_exp_neg_ord v hx, WithZero.exp_le_exp, neg_le_neg_iff]

theorem ord_algebraMap_mul (v : Place K F) {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (algebraMap K F c * f) = v.ord f := by
  rw [v.ord_mul ((_root_.map_ne_zero _).mpr hc) hf, (v.hasValue_algebraMap c).ord_eq_zero hc, zero_add]

end N1cE9
end N1cE9Generic

section N1cE9Taylor
open Polynomial

namespace N1cE9

variable {T : Type*} [CommRing T]

theorem evalEval_add_add (P : Polynomial (Polynomial T)) (a b s r : T) :
    ∃ k₁ k₂ k₃ : T,
      P.evalEval (a + s) (b + r) =
        P.evalEval a b + (derivative (P.eval (C b))).eval a * s + (derivative P).evalEval a b * r
          + (k₁ * s ^ 2 + k₂ * s * r + k₃ * r ^ 2) := by
  obtain ⟨K₁, hK₁⟩ := Polynomial.binomExpansion P (C b) (C r)
  obtain ⟨k₂, hk₂⟩ := Polynomial.binomExpansion (P.eval (C b)) a s
  obtain ⟨z, hz⟩ := Polynomial.evalSubFactor (P.derivative.eval (C b)) (a + s) a
  refine ⟨k₂, z, K₁.eval (a + s), ?_⟩
  have e1 : (P.eval (C (b + r))).eval (a + s) = (P.eval (C b)).eval (a + s)
      + (P.derivative.eval (C b)).eval (a + s) * r + K₁.eval (a + s) * r ^ 2 := by
    rw [C_add, hK₁]
    simp only [eval_add, eval_mul, eval_pow, eval_C]
  have hz' : (P.derivative.eval (C b)).eval (a + s) = (P.derivative.eval (C b)).eval a + z * s := by
    rw [add_sub_cancel_left] at hz
    linear_combination hz
  simp only [Polynomial.evalEval]
  rw [e1, hk₂, hz']
  ring

theorem evalEval_add_add_first (P : Polynomial (Polynomial T)) (a b s r : T) :
    ∃ l₁ l₂ : T, P.evalEval (a + s) (b + r) = P.evalEval a b + l₁ * s + l₂ * r := by
  obtain ⟨k₁, k₂, k₃, h⟩ := evalEval_add_add P a b s r
  exact ⟨(derivative (P.eval (C b))).eval a + k₁ * s + k₂ * r, (derivative P).evalEval a b + k₃ * r,
    by rw [h]; ring⟩

noncomputable def kroneckerForm (q : ℕ) (R : Polynomial (Polynomial T)) : Polynomial (Polynomial T) :=
  (C X ^ q - X) * (C X - X ^ q) + C (C (q : T)) * R

theorem evalEval_kroneckerForm (q : ℕ) (R : Polynomial (Polynomial T)) (a b : T) :
    (kroneckerForm q R).evalEval a b = (a ^ q - b) * (a - b ^ q) + q * R.evalEval a b := by
  simp only [kroneckerForm, Polynomial.evalEval, eval_add, eval_mul, eval_sub, eval_pow, eval_C,
    eval_X, eval_natCast]

theorem taylorCoeff_kroneckerForm (q : ℕ) (R : Polynomial (Polynomial T)) (a b : T) :
    ∃ ρ : T,
      (derivative ((kroneckerForm q R).eval (C b))).eval a
        + (q : T) * a ^ (q - 1) * (derivative (kroneckerForm q R)).evalEval a b
      = (a ^ q - b) + q * ρ := by
  refine ⟨a ^ (q - 1) * (a - b ^ q) + (derivative (R.eval (C b))).eval a
      + a ^ (q - 1) * ((a ^ q - b) * (-( (q : T) * b ^ (q - 1))) + q * (derivative R).evalEval a b)
      - a ^ (q - 1) * (a - b ^ q), ?_⟩
  simp only [kroneckerForm, Polynomial.evalEval, eval_add, eval_mul, eval_sub, eval_pow, eval_C,
    eval_X, eval_natCast, eval_zero, eval_one, derivative_add, derivative_mul, derivative_sub,
    derivative_pow, derivative_X_pow, derivative_C, derivative_X, derivative_natCast, derivative_one,
    map_natCast, mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_one, one_mul]
  ring

end N1cE9
end N1cE9Taylor

section N1cE9Modular
open AlgebraicCurve IsLocalRing ModularCurve Polynomial
set_option autoImplicit false

namespace N1cE9

noncomputable def twoVarEval (S : Type*) [CommRing S] (u v : S) (P : Polynomial (Polynomial ℤ)) : S :=
  ((P.map (mapRingHom (Int.castRingHom S))).eval (C v)).eval u

theorem twoVarEval_eq_evalEval (S : Type*) [CommRing S] (u v : S) (P : Polynomial (Polynomial ℤ)) :
    twoVarEval S u v P = (P.map (mapRingHom (Int.castRingHom S))).evalEval u v := rfl

theorem eval₂_aeval_eq_twoVarEval {S : Type*} [CommRing S] (u v : S) (P : Polynomial (Polynomial ℤ)) :
    P.eval₂ (aeval u).toRingHom v = twoVarEval S u v P := by
  induction P using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [eval₂_add, twoVarEval, Polynomial.map_add, eval_add] at hp hr ⊢
    rw [hp, hr]
  | monomial n p =>
    simp only [twoVarEval, eval₂_monomial, Polynomial.map_monomial, eval_monomial, eval_mul,
      eval_pow, eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_def, eval_map,
      algebraMap_int_eq, coe_mapRingHom]

theorem map_twoVarEval {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') (u v : S)
    (P : Polynomial (Polynomial ℤ)) : f (twoVarEval S u v P) = twoVarEval S' (f u) (f v) P := by
  rw [← eval₂_aeval_eq_twoVarEval, ← eval₂_aeval_eq_twoVarEval, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

theorem twoVarEval_add (S : Type*) [CommRing S] (u v : S) (P Q : Polynomial (Polynomial ℤ)) :
    twoVarEval S u v (P + Q) = twoVarEval S u v P + twoVarEval S u v Q := by
  simp only [twoVarEval, Polynomial.map_add, eval_add]

theorem twoVarEval_mul (S : Type*) [CommRing S] (u v : S) (P Q : Polynomial (Polynomial ℤ)) :
    twoVarEval S u v (P * Q) = twoVarEval S u v P * twoVarEval S u v Q := by
  simp only [twoVarEval, Polynomial.map_mul, eval_mul]

theorem map_eq_kroneckerForm {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R) (S : Type*) [CommRing S] :
    Φ.map (mapRingHom (Int.castRingHom S)) = kroneckerForm q (R.map (mapRingHom (Int.castRingHom S))) := by
  rw [hR]
  simp only [kroneckerForm, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_natCast, map_C, map_X, coe_mapRingHom, eq_intCast, Int.cast_natCast,
    map_natCast]

theorem twoVarEval_of_kronecker {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R) (S : Type*) [CommRing S] (u v : S) :
    twoVarEval S u v Φ = (u ^ q - v) * (u - v ^ q) + q * twoVarEval S u v R := by
  rw [twoVarEval_eq_evalEval, map_eq_kroneckerForm hR, evalEval_kroneckerForm, ← twoVarEval_eq_evalEval]

theorem hasValue_twoVarEval {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {g₁ g₂ : F} {a₁ a₂ : K} (h₁ : v.HasValue g₁ a₁) (h₂ : v.HasValue g₂ a₂)
    (P : Polynomial (Polynomial ℤ)) :
    v.HasValue (twoVarEval F g₁ g₂ P) (twoVarEval K a₁ a₂ P) := by
  rw [← eval₂_aeval_eq_twoVarEval, ← eval₂_aeval_eq_twoVarEval]
  exact hasValue_eval₂ v h₁ h₂ P

variable {q : ℕ} [Fact q.Prime]

variable (q) in

noncomputable abbrev J : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

variable (q) in

noncomputable abbrev Jq : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange
      (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

theorem coe_jFun : ((N1cE9.J q : modularFunctionFieldBar (1 * q)) :
    LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) 1 := by
  rw [jqNModC_one]
  show coeffEmb (AlgebraicClosure ℚ) jq = _
  exact coeffEmb_jq _

theorem coe_jqFun : ((N1cE9.Jq q : modularFunctionFieldBar (1 * q)) :
    LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) = _
  rw [coeffEmb_qExpand, coeffEmb_jq]
  rfl

theorem phi_eval₂_jFun_jqFun (data : ModularPolynomialData q) :
    data.Φ.eval₂ (aeval (N1cE9.J q)).toRingHom
      (N1cE9.Jq q) = 0 := by
  apply Subtype.ext
  have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero data (AlgebraicClosure ℚ) 1
  rw [ZeroMemClass.coe_zero, ← h, ← coe_jFun (q := q), ← coe_jqFun (q := q)]
  have hval : ∀ z : modularFunctionFieldBar (1 * q), (z : LaurentSeries (AlgebraicClosure ℚ))
      = (modularFunctionFieldBar (1 * q)).val.toRingHom z := fun z => rfl
  rw [hval, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem twoVarEval_jFun_jqFun (data : ModularPolynomialData q) :
    twoVarEval (modularFunctionFieldBar (1 * q)) (N1cE9.J q)
      (N1cE9.Jq q) data.Φ = 0 := by
  rw [← eval₂_aeval_eq_twoVarEval, phi_eval₂_jFun_jqFun]

theorem exists_data_kronecker : ∃ (data : ModularPolynomialData q) (R : Polynomial (Polynomial ℤ)),
    data.Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R := by
  obtain ⟨data, hK⟩ := exists_kroneckerCongruence_of_prime q
  obtain ⟨R, hR, -⟩ := existsUnique_kroneckerRemainder q data hK
  exact ⟨data, R, hR⟩

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem twoVarEval_values_eq_zero (data : ModularPolynomialData q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (x y : A)
    (hJ : W.HasValue (N1cE9.J q) (x : AlgebraicClosure ℚ))
    (hJq : W.HasValue (N1cE9.Jq q) (y : AlgebraicClosure ℚ)) :
    twoVarEval A x y data.Φ = 0 := by
  have hv := hasValue_twoVarEval W hJ hJq data.Φ
  rw [twoVarEval_jFun_jqFun] at hv
  have h0 : W.HasValue (0 : modularFunctionFieldBar (1 * q)) (0 : AlgebraicClosure ℚ) := by
    simpa only [map_zero] using W.hasValue_algebraMap (0 : AlgebraicClosure ℚ)
  have h := hv.unique h0
  apply Subtype.val_injective
  rw [show ((twoVarEval A x y data.Φ : A) : AlgebraicClosure ℚ) = A.subtype (twoVarEval A x y data.Φ)
    from rfl, map_twoVarEval]
  simpa using h

theorem kronecker_values {data : ModularPolynomialData q} {R : Polynomial (Polynomial ℤ)}
    (hR : data.Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (x y : A)
    (hJ : W.HasValue (N1cE9.J q) (x : AlgebraicClosure ℚ))
    (hJq : W.HasValue (N1cE9.Jq q) (y : AlgebraicClosure ℚ)) :
    (x ^ q - y) * (x - y ^ q) + q * twoVarEval A x y R = 0 := by
  rw [← twoVarEval_of_kronecker hR, twoVarEval_values_eq_zero data W x y hJ hJq]

theorem isUnit_twoVarEval_R {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) {a : k} (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    {data : ModularPolynomialData q} {R : Polynomial (Polynomial ℤ)}
    (hR : data.Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R)
    (x y : A) (hx : red x = a) (hy : red y = a ^ q) :
    IsUnit (twoVarEval A x y R) := by
  have hK2 := eval_kroneckerRemainder_ne_zero_of_mem_ssJSet hq data R hR a ha h0 h1728
  have hred : red (twoVarEval A x y R) ≠ 0 := by
    rw [map_twoVarEval, hx, hy]
    exact hK2
  by_contra hu
  exact hred ((hker _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu))

theorem values_of_centred {k : Type*} [Field k] (red : A →+* k) (a : k)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ x y : A, red x = a ∧ red y = a ^ q ∧
      W.HasValue (N1cE9.J q) (x : AlgebraicClosure ℚ) ∧
      W.HasValue (N1cE9.Jq q) (y : AlgebraicClosure ℚ) ∧
      W.ord (N1cE9.J q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) =
        W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) ∧
      0 < W.ord (N1cE9.J q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) := by
  obtain ⟨⟨x, hxa, hx⟩, ⟨y, hya, hy⟩⟩ := hW
  refine ⟨x, y, hxa, hya, ?_, ?_, rfl, hx⟩
  · exact hasValue_of_ord_sub_pos W hx
  · exact hasValue_of_ord_sub_pos W hy

end N1cE9
end N1cE9Modular

section N1cE9IIA
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve Polynomial

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ c : A, c ∈ IsLocalRing.maximalIdeal A ∧ (∃ d ∈ IsLocalRing.maximalIdeal A, c * d = ((q : ℕ) : A)) ∧
      W.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) (c : AlgebraicClosure ℚ) := by
  obtain ⟨data, R, hR⟩ := N1cE9.exists_data_kronecker (q := q)
  obtain ⟨x, y, hxa, hya, hJ, hJq, -, -⟩ := N1cE9.values_of_centred red a W hW
  have hunit := N1cE9.isUnit_twoVarEval_R red hker hq ha h0 h1728 hR x y hxa hya
  have hkr := N1cE9.kronecker_values hR W x y hJ hJq
  set ρ : A := N1cE9.twoVarEval A x y R with hρ
  obtain ⟨u, hu⟩ := hunit

  have hc : y - x ^ q ∈ IsLocalRing.maximalIdeal A := by
    rw [← hker, map_sub, map_pow, hxa, hya, sub_self]
  have hh : x - y ^ q ∈ IsLocalRing.maximalIdeal A := by
    rw [← hker, map_sub, map_pow, hxa, hya, ← pow_mul, ← sq, ha2, sub_self]
  refine ⟨y - x ^ q, hc, ⟨(x - y ^ q) * ↑u⁻¹, Ideal.mul_mem_right _ _ hh, ?_⟩, ?_⟩
  ·
    have h1 : (y - x ^ q) * (x - y ^ q) = (q : A) * ρ := by linear_combination (-1 : A) * hkr
    calc (y - x ^ q) * ((x - y ^ q) * ↑u⁻¹) = ((y - x ^ q) * (x - y ^ q)) * ↑u⁻¹ := by ring
      _ = (q : A) * (ρ * ↑u⁻¹) := by rw [h1, mul_assoc]
      _ = (q : A) := by rw [← hu, Units.mul_inv, mul_one]
  · have hv := N1cE9.HasValue.sub W hJq (N1cE9.HasValue.pow W hJ q)
    push_cast
    exact hv

end N1cE9IIA

end S_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred (solution)
