-- Prove2me | solution 1 for ModularCurve.NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/18da5408-193d-5191-b8cc-51ddb5a5dc28

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
import Theorems.Thm_ModularCurve_exists_place_of_modularPolynomial_eval_eq_zero
import Theorems.Thm_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

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

open Polynomial

namespace FltWs29
namespace N1c

section TwoVar

variable {S T : Type*} [CommRing S] [CommRing T]

noncomputable def twoVarEvalHom (u v : S) : Polynomial (Polynomial ℤ) →+* S :=
  (evalRingHom u).comp ((evalRingHom (C v)).comp (mapRingHom (mapRingHom (Int.castRingHom S))))

theorem twoVarEvalHom_apply (u v : S) (P : Polynomial (Polynomial ℤ)) :
    twoVarEvalHom u v P = ((P.map (mapRingHom (Int.castRingHom S))).eval (C v)).eval u := rfl

@[scoped simp] theorem twoVarEvalHom_X (u v : S) : twoVarEvalHom u v X = v := by
  simp [twoVarEvalHom_apply]

@[scoped simp] theorem twoVarEvalHom_C_X (u v : S) : twoVarEvalHom u v (C X) = u := by
  simp [twoVarEvalHom_apply]

@[scoped simp] theorem twoVarEvalHom_C_C (u v : S) (n : ℤ) : twoVarEvalHom u v (C (C n)) = n := by
  simp [twoVarEvalHom_apply]

theorem ringHom_ext_twoVar {f g : Polynomial (Polynomial ℤ) →+* S} (hCX : f (C X) = g (C X)) (hX : f X = g X) :
    f = g := by
  refine Polynomial.ringHom_ext (fun p => ?_) hX

  have h : f.comp C = g.comp C := by
    refine Polynomial.ringHom_ext (fun n => ?_) (by simpa using hCX)
    simp [eq_intCast]
  exact congrArg (fun φ : Polynomial ℤ →+* S => φ p) h

theorem map_twoVarEvalHom (φ : S →+* T) (u v : S) (P : Polynomial (Polynomial ℤ)) :
    φ (twoVarEvalHom u v P) = twoVarEvalHom (φ u) (φ v) P := by
  have h : φ.comp (twoVarEvalHom u v) = twoVarEvalHom (φ u) (φ v) :=
    ringHom_ext_twoVar (by simp) (by simp)
  exact congrArg (fun ψ : Polynomial (Polynomial ℤ) →+* T => ψ P) h

theorem eval₂_aeval_eq_twoVarEvalHom [Algebra ℤ S] (u v : S) (P : Polynomial (Polynomial ℤ)) :
    P.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom v = twoVarEvalHom u v P := by
  have h : (Polynomial.eval₂RingHom (Polynomial.aeval (R := ℤ) u).toRingHom v) = twoVarEvalHom u v :=
    ringHom_ext_twoVar (by simp) (by simp)
  exact congrArg (fun ψ : Polynomial (Polynomial ℤ) →+* S => ψ P) h

theorem eval_map_aeval_eq_twoVarEvalHom [Algebra ℤ S] (u v : S) (P : Polynomial (Polynomial ℤ)) :
    (P.map (Polynomial.aeval (R := ℤ) u).toRingHom).eval v = twoVarEvalHom u v P := by
  rw [eval_map]
  exact eval₂_aeval_eq_twoVarEvalHom u v P

theorem twoVarEvalHom_kronecker {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R) (u v : S) :
    twoVarEvalHom u v Φ = (u ^ q - v) * (u - v ^ q) + (q : S) * twoVarEvalHom u v R := by
  rw [hR, map_add, map_mul, map_mul, map_sub, map_sub, map_pow, map_pow, twoVarEvalHom_X, twoVarEvalHom_C_X,
    twoVarEvalHom_C_C]
  push_cast
  ring

end TwoVar

section Fc

variable {A : Type*} [CommRing A]

noncomputable def Rc (q : ℕ) (R : Polynomial (Polynomial ℤ)) (c : A) : Polynomial A :=
  twoVarEvalHom (S := Polynomial A) X (X ^ q + C c) R

noncomputable def fc (q : ℕ) (R : Polynomial (Polynomial ℤ)) (c d : A) : Polynomial A :=
  (X ^ q + C c) ^ q - X + C d * Rc q R c

theorem twoVarEvalHom_fcSubst {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R) {c d : A} (hcd : c * d = (q : A)) :
    twoVarEvalHom (S := Polynomial A) X (X ^ q + C c) Φ = C c * fc q R c d := by
  rw [twoVarEvalHom_kronecker hR, fc, Rc]
  have hq : ((q : ℕ) : Polynomial A) = C c * C d := by
    rw [← C_mul, hcd, map_natCast]
  rw [hq]
  ring

theorem twoVarEvalHom_eq_mul_eval_fc {B : Type*} [CommRing B] (φ : A →+* B)
    {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R) {c d : A} (hcd : c * d = (q : A)) (x : B) :
    twoVarEvalHom x (x ^ q + φ c) Φ = φ c * ((fc q R c d).map φ).eval x := by
  have h := congrArg (eval₂RingHom φ x) (twoVarEvalHom_fcSubst hR hcd)
  rw [map_twoVarEvalHom (eval₂RingHom φ x)] at h
  simp only [coe_eval₂RingHom, eval₂_X, eval₂_add, eval₂_pow, eval₂_C, eval₂_mul] at h
  rw [h, eval_map]

theorem map_fc_eq {κ : Type*} [CommRing κ] (φ : A →+* κ) {q : ℕ} (R : Polynomial (Polynomial ℤ))
    {c d : A} (hc : φ c = 0) (hd : φ d = 0) :
    (fc q R c d).map φ = X ^ (q ^ 2) - X := by
  simp only [fc, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    hc, hd, map_zero, add_zero, zero_mul, ← pow_mul, sq]

theorem rootMultiplicity_X_pow_sq_sub_X {κ : Type*} [Field κ] {q : ℕ} [Fact q.Prime] [CharP κ q]
    {b : κ} (hb : b ^ (q ^ 2) = b) :
    (X ^ (q ^ 2) - X : Polynomial κ).rootMultiplicity b = 1 := by
  have hq1 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
  have hne : (X ^ (q ^ 2) - X : Polynomial κ) ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq1), natDegree_X_pow, natDegree_zero] at this
    omega
  have hsep : (X ^ (q ^ 2) - X : Polynomial κ).Separable := by
    rw [separable_def, derivative_sub, derivative_X_pow, derivative_X]
    have h0 : (C ((q ^ 2 : ℕ) : κ) : Polynomial κ) = 0 := by
      rw [Nat.cast_pow, CharP.cast_eq_zero κ q, zero_pow two_ne_zero, map_zero]
    rw [h0, zero_mul, zero_sub]
    exact IsCoprime.neg_right isCoprime_one_right
  have hroot : (X ^ (q ^ 2) - X : Polynomial κ).IsRoot b := by
    simp [IsRoot, hb]
  have h1 := (rootMultiplicity_pos hne).mpr hroot
  have h2 := rootMultiplicity_le_one_of_separable hsep b
  omega

end Fc

section SimpleRoot

variable {S : Type*} [CommRing S] [IsDomain S] [CharZero S]

theorem rootMultiplicity_eq_one_of_eval_derivative_ne_zero {p : Polynomial S} {y : S}
    (hroot : p.IsRoot y) (hder : (derivative p).eval y ≠ 0) : p.rootMultiplicity y = 1 := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hder
  have h1 : 0 < p.rootMultiplicity y := (rootMultiplicity_pos hp).mpr hroot
  have h2 : (derivative p).rootMultiplicity y = 0 := rootMultiplicity_eq_zero hder
  have h3 := derivative_rootMultiplicity_of_root hroot
  omega

omit [IsDomain S] [CharZero S] in

theorem eval_derivative_map_kronecker [Algebra ℤ S] {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R) (u v : S) :
    (derivative (Φ.map (Polynomial.aeval (R := ℤ) u).toRingHom)).eval v
      = -(u - v ^ q) - (q : S) * (u ^ q - v) * v ^ (q - 1) + (q : S) * twoVarEvalHom u v (derivative R) := by
  have hmap : Φ.map (Polynomial.aeval (R := ℤ) u).toRingHom
      = (C (u ^ q) - X) * (C u - X ^ q) + C (q : S) * R.map (Polynomial.aeval (R := ℤ) u).toRingHom := by
    rw [hR]
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow]
  rw [hmap]
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_C, derivative_X, derivative_X_pow,
    derivative_natCast, zero_sub, zero_mul, eval_zero, add_zero, eval_add, eval_mul, eval_sub, eval_neg, eval_C,
    eval_X, eval_pow, eval_natCast, eval_one, derivative_map, eval_map_aeval_eq_twoVarEvalHom, map_natCast]
  ring

end SimpleRoot

end FltWs29.N1c
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29 P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29.N1c"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29"

namespace FltWs29
namespace N1c

open AlgebraicCurve IsLocalRing ModularCurve Polynomial

theorem twoVarEvalHom_eq {S : Type*} [CommRing S] (u v : S) (P : Polynomial (Polynomial ℤ)) :
    twoVarEvalHom u v P = N1cE9.twoVarEval S u v P := rfl

section RedBar

variable {K : Type*} [Field K] {A : ValuationSubring K} {k : Type*} [Field k]
  (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

noncomputable def redBar : IsLocalRing.ResidueField A →+* k :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) red fun a ha => (hker a).mpr ha

include hker in
theorem redBar_residue (a : A) : redBar red hker (IsLocalRing.residue A a) = red a :=
  Ideal.Quotient.lift_mk _ _ _

include hker in
theorem residue_eq_residue_iff (a b : A) :
    IsLocalRing.residue A a = IsLocalRing.residue A b ↔ red a = red b := by
  rw [← redBar_residue red hker a, ← redBar_residue red hker b]
  exact ((redBar red hker).injective.eq_iff).symm

include hker in

theorem charP_residueField' (p : ℕ) [CharP k p] : CharP (IsLocalRing.ResidueField A) p := by
  constructor
  intro n
  rw [← CharP.cast_eq_zero_iff k p n, ← map_natCast (redBar red hker) n,
    map_eq_zero_iff _ (redBar red hker).injective]

include hker in

theorem exists_red_eq_of_pow_eq [IsAlgClosed (IsLocalRing.ResidueField A)] {q : ℕ} (hq : 1 < q ^ 2) {a : k}
    (ha : a ^ (q ^ 2) = a) : ∃ x : A, red x = a := by
  classical
  set p : Polynomial (IsLocalRing.ResidueField A) := X ^ (q ^ 2) - X with hp
  have hpne : p ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [hp, natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), natDegree_X_pow, natDegree_zero] at this
    omega
  have hroots : p.roots.card = p.natDegree := splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hmap : p.map (redBar red hker) = X ^ (q ^ 2) - X := by
    simp [hp, Polynomial.map_sub, Polynomial.map_pow]
  have hmapne : p.map (redBar red hker) ≠ 0 := (Polynomial.map_ne_zero_iff (redBar red hker).injective).mpr hpne
  have ha' : a ∈ (p.map (redBar red hker)).roots := by
    rw [mem_roots hmapne, hmap, IsRoot, eval_sub, eval_pow, eval_X, ha, sub_self]
  rw [← roots_map_of_injective_of_card_eq_natDegree (redBar red hker).injective hroots, Multiset.mem_map] at ha'
  obtain ⟨b, -, hb⟩ := ha'
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective b
  exact ⟨x, by rw [← hb, redBar_residue]⟩

end RedBar
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29 P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29.N1c"

section Deriv

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem eval_derivative_ne_zero {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R)
    (c d : A) (hc : c ∈ IsLocalRing.maximalIdeal A) (hcd : c * d = (q : A)) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (x y : A) (hy : y = x ^ q + c)
    (hK : (x ^ q - y) * (x - y ^ q) + (q : A) * N1cE9.twoVarEval A x y R = 0)
    (hu : IsUnit (N1cE9.twoVarEval A x y R)) :
    (derivative (Φ.map (Polynomial.aeval (R := ℤ) (x : AlgebraicClosure ℚ)).toRingHom)).eval
      (y : AlgebraicClosure ℚ) ≠ 0 := by
  rw [eval_derivative_map_kronecker hR]
  set ρ : A := N1cE9.twoVarEval A x y R with hρ
  set σ : A := N1cE9.twoVarEval A x y (derivative R) with hσ
  have hσ' : twoVarEvalHom (x : AlgebraicClosure ℚ) (y : AlgebraicClosure ℚ) (derivative R)
      = (σ : AlgebraicClosure ℚ) := by
    rw [twoVarEvalHom_eq, hσ]
    exact (N1cE9.map_twoVarEval A.subtype x y (derivative R)).symm
  rw [hσ']

  have hcℚ : ((c : A) : AlgebraicClosure ℚ) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hdℚ : ((d : A) : AlgebraicClosure ℚ) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hqℚ : ((q : ℕ) : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ) * d := by
    have := congrArg (fun t : A => (t : AlgebraicClosure ℚ)) hcd
    push_cast at this
    exact this.symm
  have hyℚ : ((y : A) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) ^ q + c := by
    rw [hy]
    push_cast
    rfl
  have hKℚ : ((x : AlgebraicClosure ℚ) ^ q - y) * ((x : AlgebraicClosure ℚ) - (y : AlgebraicClosure ℚ) ^ q)
      + ((q : ℕ) : AlgebraicClosure ℚ) * ρ = 0 := by
    have := congrArg (fun t : A => (t : AlgebraicClosure ℚ)) hK
    push_cast at this
    exact this

  have hH : ((x : AlgebraicClosure ℚ) - (y : AlgebraicClosure ℚ) ^ q) = d * ρ := by
    have h1 : (c : AlgebraicClosure ℚ) * (d * ρ - ((x : AlgebraicClosure ℚ) - (y : AlgebraicClosure ℚ) ^ q)) = 0 := by
      rw [hqℚ, hyℚ] at hKℚ
      rw [hyℚ]
      linear_combination hKℚ
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hcℚ
    · linear_combination -h
  intro hder

  have h2 : (d : AlgebraicClosure ℚ) * (ρ - c * (c * (y : AlgebraicClosure ℚ) ^ (q - 1) + σ)) = 0 := by
    rw [hqℚ, hH] at hder
    have hxqy : (x : AlgebraicClosure ℚ) ^ q - y = -c := by rw [hyℚ]; ring
    rw [hxqy] at hder
    linear_combination -hder
  rcases mul_eq_zero.mp h2 with h | h
  · exact hdℚ h
  · have h3 : ρ = c * (c * y ^ (q - 1) + σ) := by
      apply Subtype.ext
      push_cast
      linear_combination h
    have hmem : ρ ∈ IsLocalRing.maximalIdeal A := by
      rw [h3]
      exact Ideal.mul_mem_right _ _ hc
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

end Deriv
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29 P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29.N1c"

section Core

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]

set_option maxHeartbeats 6400000 in
theorem iib_core (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (c : A) (hc : c ∈ IsLocalRing.maximalIdeal A) (hcq : ∃ d ∈ IsLocalRing.maximalIdeal A, c * d = ((q : ℕ) : A))

    (data : ModularPolynomialData q) (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R)

    (J Jq : modularFunctionFieldBar (1 * q))
    (hΦF : N1cE9.twoVarEval (modularFunctionFieldBar (1 * q)) J Jq data.Φ = 0)
    (hplace : ∀ x y : AlgebraicClosure ℚ, data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0 →
      ∃ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        0 < W.ord (J - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) x) ∧
        0 < W.ord (Jq - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) y))
    (hplace_unique : ∀ x y : AlgebraicClosure ℚ, data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0 →
      (data.Φ.map (Polynomial.aeval (R := ℤ) x).toRingHom).rootMultiplicity y = 1 →
      ∀ W W' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        0 < W.ord (J - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) x) →
        0 < W.ord (Jq - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) y) →
        0 < W'.ord (J - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) x) →
        0 < W'.ord (Jq - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) y) → W = W') :
    ∃! W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = a ∧
          0 < W.ord (J - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
       (∃ y : A, red y = a ^ q ∧
          0 < W.ord (Jq - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) ∧
      W.HasValue (Jq - J ^ q) (c : AlgebraicClosure ℚ) := by
  classical
  obtain ⟨d, hd, hcd⟩ := hcq
  have hqA : ((q : ℕ) : A) ≠ 0 := by
    intro h
    have := congrArg (fun t : A => (t : AlgebraicClosure ℚ)) h
    push_cast at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hcd
    exact hqA hcd.symm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcd
    exact hqA hcd.symm

  have values_eq_zero : ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (u w : A),
      V.HasValue J (u : AlgebraicClosure ℚ) → V.HasValue Jq (w : AlgebraicClosure ℚ) →
      N1cE9.twoVarEval A u w data.Φ = 0 := by
    intro V u w hu hw
    have hv := N1cE9.hasValue_twoVarEval V hu hw data.Φ
    rw [hΦF] at hv
    have h0 : V.HasValue (0 : modularFunctionFieldBar (1 * q)) (0 : AlgebraicClosure ℚ) := by
      simpa only [map_zero] using V.hasValue_algebraMap (0 : AlgebraicClosure ℚ)
    have h := hv.unique h0
    apply Subtype.ext
    rw [show ((N1cE9.twoVarEval A u w data.Φ : A) : AlgebraicClosure ℚ) = A.subtype (N1cE9.twoVarEval A u w data.Φ)
      from rfl, N1cE9.map_twoVarEval]
    simpa using h
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (IsLocalRing.ResidueField A) q := charP_residueField' red hker q
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt

  obtain ⟨x₀, hx₀⟩ := exists_red_eq_of_pow_eq red hker hq2 ha2

  set g : Polynomial A := fc q R c d with hg
  have hcres : IsLocalRing.residue A c = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hc
  have hdres : IsLocalRing.residue A d = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hd
  have hgred : g.map (IsLocalRing.residue A) = X ^ (q ^ 2) - X := map_fc_eq _ R hcres hdres
  have hb2 : (IsLocalRing.residue A x₀) ^ (q ^ 2) = IsLocalRing.residue A x₀ := by
    apply (redBar red hker).injective
    rw [map_pow, redBar_residue, hx₀, ha2]
  have hmult1 : (g.map (IsLocalRing.residue A)).rootMultiplicity (IsLocalRing.residue A x₀) = 1 := by
    rw [hgred]
    exact rootMultiplicity_X_pow_sq_sub_X hb2

  obtain ⟨r, ⟨hroot, hrA, hrres⟩, huniq⟩ :=
    ValuationSubring.existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one A g
      (IsAlgClosed.splits _) (IsLocalRing.residue A x₀) hmult1
  set x : A := ⟨r, hrA⟩ with hx
  set y : A := x ^ q + c with hy
  have hredx : red x = a := by
    rw [← hx₀, ← residue_eq_residue_iff red hker]
    exact hrres
  have hredy : red y = a ^ q := by
    rw [hy, map_add, map_pow, hredx, (hker c).mpr hc, add_zero]

  have hyℚ : ((y : A) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) ^ q + A.subtype c := by
    rw [hy]
    push_cast
    rfl
  have hΦxy : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (x : AlgebraicClosure ℚ)).toRingHom (y : AlgebraicClosure ℚ) = 0 := by
    rw [eval₂_aeval_eq_twoVarEvalHom, hyℚ, twoVarEvalHom_eq_mul_eval_fc A.subtype hR hcd, ← hg]
    have : ((g.map A.subtype).eval (x : AlgebraicClosure ℚ)) = 0 := hroot
    rw [this, mul_zero]

  obtain ⟨W, hW1, hW2⟩ := hplace x y hΦxy
  have hJ : W.HasValue J (x : AlgebraicClosure ℚ) := N1cE9.hasValue_of_ord_sub_pos W hW1
  have hJq : W.HasValue Jq (y : AlgebraicClosure ℚ) := N1cE9.hasValue_of_ord_sub_pos W hW2
  have hGval : ((y : A) : AlgebraicClosure ℚ) - (x : AlgebraicClosure ℚ) ^ q = (c : AlgebraicClosure ℚ) := by
    rw [hyℚ]
    simp
  have hG : W.HasValue (Jq - J ^ q) (c : AlgebraicClosure ℚ) := by
    rw [← hGval]
    exact N1cE9.HasValue.sub W hJq (N1cE9.HasValue.pow W hJ q)
  refine ⟨W, ⟨⟨⟨x, hredx, hW1⟩, ⟨y, hredy, hW2⟩⟩, hG⟩, ?_⟩

  rintro W' ⟨⟨⟨x', hx'a, hx'ord⟩, ⟨y', hy'a, hy'ord⟩⟩, hG'⟩
  have hJ' : W'.HasValue J (x' : AlgebraicClosure ℚ) := N1cE9.hasValue_of_ord_sub_pos W' hx'ord
  have hJq' : W'.HasValue Jq (y' : AlgebraicClosure ℚ) := N1cE9.hasValue_of_ord_sub_pos W' hy'ord
  have hc' : (c : AlgebraicClosure ℚ) = (y' : AlgebraicClosure ℚ) - (x' : AlgebraicClosure ℚ) ^ q :=
    hG'.unique (N1cE9.HasValue.sub W' hJq' (N1cE9.HasValue.pow W' hJ' q))
  have hy' : y' = x' ^ q + c := by
    apply Subtype.ext
    push_cast
    linear_combination -hc'

  have hΦ' : N1cE9.twoVarEval A x' y' data.Φ = 0 := values_eq_zero W' x' y' hJ' hJq'
  have hroot' : (g.map (algebraMap A (AlgebraicClosure ℚ))).IsRoot (x' : AlgebraicClosure ℚ) := by
    have h1 := twoVarEvalHom_eq_mul_eval_fc (RingHom.id A) hR hcd x'
    rw [RingHom.id_apply, Polynomial.map_id, ← hy', twoVarEvalHom_eq, hΦ', ← hg] at h1
    have h2 : g.eval x' = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact absurd h hc0
      · exact h
    rw [IsRoot, eval_map]
    change g.eval₂ (algebraMap A (AlgebraicClosure ℚ)) (algebraMap A (AlgebraicClosure ℚ) x') = 0
    rw [eval₂_hom, h2, map_zero]
  have hres' : IsLocalRing.residue A x' = IsLocalRing.residue A x₀ := by
    rw [residue_eq_residue_iff red hker, hx'a, hx₀]
  have hxx : (x' : AlgebraicClosure ℚ) = r := huniq (x' : AlgebraicClosure ℚ) ⟨hroot', x'.2, by simpa using hres'⟩
  have hxeq : x' = x := Subtype.ext hxx
  have hyeq : y' = y := by rw [hy', hy, hxeq]
  rw [hxeq] at hx'ord
  rw [hyeq] at hy'ord

  have hK : (x ^ q - y) * (x - y ^ q) + (q : A) * N1cE9.twoVarEval A x y R = 0 := by
    rw [← N1cE9.twoVarEval_of_kronecker hR]
    exact values_eq_zero W x y hJ hJq
  have hu := N1cE9.isUnit_twoVarEval_R red hker hq ha h0 h1728 hR x y hredx hredy
  have hder := eval_derivative_ne_zero hR c d hc hcd hc0 hd0 x y hy hK hu
  have hmult : (data.Φ.map (Polynomial.aeval (R := ℤ) (x : AlgebraicClosure ℚ)).toRingHom).rootMultiplicity
      (y : AlgebraicClosure ℚ) = 1 :=
    rootMultiplicity_eq_one_of_eval_derivative_ne_zero (by rw [IsRoot, eval_map]; exact hΦxy) hder
  exact (hplace_unique x y hΦxy hmult W W' hW1 hW2 hx'ord hy'ord).symm

end Core
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29 P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29.N1c"

end FltWs29.N1c
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29 P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29.N1c"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29 P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29.N1c"

namespace FltWs29
namespace N1c
open AlgebraicCurve IsLocalRing ModularCurve Polynomial

noncomputable def liftLevel {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (d : ModularPolynomialData m) :
    ModularPolynomialData n := by
  subst h
  exact d

theorem liftLevel_Φ {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (d : ModularPolynomialData m) :
    (liftLevel h d).Φ = d.Φ := by
  subst h
  rfl

end FltWs29.N1c
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29 P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29.N1c"
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29 P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord.FltWs29.N1c"

open AlgebraicCurve IsLocalRing ModularCurve in
set_option maxHeartbeats 6400000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (c : A) (hc : c ∈ IsLocalRing.maximalIdeal A) (hcq : ∃ d ∈ IsLocalRing.maximalIdeal A, c * d = ((q : ℕ) : A)) :
    ∃! W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) ∧ W.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) (c : AlgebraicClosure ℚ) := by
  obtain ⟨data, R, hR⟩ := N1cE9.exists_data_kronecker (q := q)
  haveI : NeZero (1 * q) := ⟨by rw [Nat.one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  have hp : (1 * q).Prime := by rw [Nat.one_mul]; exact Fact.out
  set data' : ModularPolynomialData (1 * q) := FltWs29.N1c.liftLevel (Nat.one_mul q).symm data with hdata'
  have hΦ' : data'.Φ = data.Φ := FltWs29.N1c.liftLevel_Φ _ _
  have hΦF := N1cE9.twoVarEval_jFun_jqFun (q := q) data
  refine FltWs29.N1c.iib_core red hker hq a ha ha2 h0 h1728 c hc hcq data R hR (N1cE9.J q) (N1cE9.Jq q) hΦF ?_ ?_
  · intro x y hxy
    obtain ⟨W, -, h1, h2⟩ := exists_place_of_modularPolynomial_eval_eq_zero (1 * q) hp data' x y (by rw [hΦ']; exact hxy)
    exact ⟨W, h1, h2⟩
  · intro x y hxy hm W W' h1 h2 h1' h2'
    exact place_eq_of_modularPolynomial_rootMultiplicity_eq_one (1 * q) hp data' x y (by rw [hΦ']; exact hxy)
      (by rw [hΦ']; exact hm) W W' h1 h2 h1' h2'

end S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord (solution)
