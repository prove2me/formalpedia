-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/bb23222b-56cd-589a-8714-1dfcfa37d6bc

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_eq_iff_centred_levelOne
import Theorems.Thm_ModularCurve_geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
p2m_open "ModularCurve.PlaceSpecialization~jFun ModularCurve.PlaceSpecialization.ProlongationTuple"

namespace ResRat

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~jFun"

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_sub_algebraMap (W : Place K F) (f : F) (b c : K) (hb : W.HasValue f b) :
    W.HasValue (f - algebraMap K F c) (b - c) := by
  obtain ⟨hmem, hres⟩ := hb
  refine ⟨sub_mem hmem (W.algebraMap_mem' c), ?_⟩
  have : (⟨f - algebraMap K F c, sub_mem hmem (W.algebraMap_mem' c)⟩ : W.toValuationSubring)
      = ⟨f, hmem⟩ - algebraMap K W.toValuationSubring c := by
    apply Subtype.ext; simp [AlgebraicCurve.Place.coe_algebraMap]
  rw [this, map_sub, hres, AlgebraicCurve.Place.residue_algebraMap, map_sub]

theorem hasValue_add_algebraMap (W : Place K F) (f : F) (b c : K) (hb : W.HasValue f b) :
    W.HasValue (f + algebraMap K F c) (b + c) := by
  have h := hasValue_sub_algebraMap W f b (-c) hb
  rwa [map_neg, sub_neg_eq_add, sub_neg_eq_add] at h

theorem ord_pos_of_hasValue_zero (W : Place K F) {f : F} (h : W.HasValue f 0) (hf : f ≠ 0) : 0 < W.ord f := by
  obtain ⟨hm, hr⟩ := h
  have h0 : 0 ≤ W.ord f := W.ord_nonneg_of_mem hm
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := W.exists_isUnit_of_ord_eq_zero hf heq.symm
    have hres : IsLocalRing.residue W.toValuationSubring ⟨f, hm'⟩ = 0 := by
      have e : (⟨f, hm'⟩ : W.toValuationSubring) = ⟨f, hm⟩ := rfl
      rw [e, hr, map_zero]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

end Generic

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem ι_algebraMap (R : ProlongationTuple P) (x : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (↥(modularFunctionFieldFullC (ResidueField A) N)) x)
      = algebraMap k (↥(modularFunctionFieldC k N)) (R.redBar x) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem residue₁_const (R : ProlongationTuple P) (a : A) (h : algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    (R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k (↥(modularFunctionFieldC k N)) (red a) := by
  have e : (⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : R.R₁.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), (R.R₁.algebraMap_mem_iff _).mpr a.2⟩ := rfl
  rw [ProlongationTuple.residue₁_apply, e, R.R₁.residue_algebraMap a, ι_algebraMap, R.redBar_residue]

theorem residue₂_const (R : ProlongationTuple P) (a : A) (h : algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    (R.residue₂ ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k (↥(modularFunctionFieldC k N)) (red a) := by
  have e : (⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : R.R₂.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), (R.R₂.algebraMap_mem_iff _).mpr a.2⟩ := rfl
  rw [ProlongationTuple.residue₂_apply, e, R.R₂.residue_algebraMap a, ι_algebraMap, R.redBar_residue]

section MoreGeneric
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_add' (W : Place K F) {f g : F} {b c : K} (hb : W.HasValue f b) (hc : W.HasValue g c) :
    W.HasValue (f + g) (b + c) := by
  obtain ⟨hf, hrf⟩ := hb
  obtain ⟨hg, hrg⟩ := hc
  refine ⟨add_mem hf hg, ?_⟩
  have e : (⟨f + g, add_mem hf hg⟩ : W.toValuationSubring) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
  rw [e, map_add, hrf, hrg, map_add]

theorem hasValue_pow' (W : Place K F) {f : F} {b : K} (hb : W.HasValue f b) (n : ℕ) :
    W.HasValue (f ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using W.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hb

theorem hasValue_eval₂ (W : Place K F) {S : Type*} [CommRing S] (φ : S →+* K) {σ : Type*} (v : σ → F) (c : σ → K)
    (hv : ∀ i, W.HasValue (v i) (c i)) (p : MvPolynomial σ S) :
    W.HasValue (MvPolynomial.eval₂ ((algebraMap K F).comp φ) v p) (MvPolynomial.eval₂ φ c p) := by
  induction p using MvPolynomial.induction_on with
  | C s => simpa using W.hasValue_algebraMap (φ s)
  | add p q hp hq => rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add]; exact hasValue_add' W hp hq
  | mul_X p i hp => rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact hp.mul (hv i)

end MoreGeneric
end ResRat

namespace ResRat

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

noncomputable def cKF (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : ↥(NodeLocalized.coeffSubring A K) →+* ↥(modularFunctionFieldBar (1 * q)) :=
  (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).comp (NodeLocalized.coeffSubring A K).subtype

noncomputable def evF (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K) →+* ↥(modularFunctionFieldBar (1 * q)) :=
  MvPolynomial.eval₂Hom (cKF K) ![ProlongationTuple.jFun 1 q, ProlongationTuple.jQFun 1 q]

theorem evF_C (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(NodeLocalized.coeffSubring A K)) :
    evF (q := q) K (MvPolynomial.C c) = cKF K c := MvPolynomial.eval₂Hom_C _ _ _

theorem evF_X (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (i : Fin 2) :
    evF (q := q) K (MvPolynomial.X i : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K)) = ![ProlongationTuple.jFun 1 q, ProlongationTuple.jQFun 1 q] i :=
  MvPolynomial.eval₂Hom_X' (cKF (q := q) K) _ i

theorem jFun_mem (R : ProlongationTuple P) (hqN : ¬ q ∣ 1) : ProlongationTuple.jFun 1 q ∈ R.R₁.integers := by
  obtain ⟨h₁, -, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN 0
  simpa using h₁

theorem jQFun_mem (R : ProlongationTuple P) (hqN : ¬ q ∣ 1) : ProlongationTuple.jQFun 1 q ∈ R.R₁.integers := by
  obtain ⟨-, -, h₃, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN 0
  simpa using h₃

theorem residue₁_jFun (R : ProlongationTuple P) (hqN : ¬ q ∣ 1) (h : ProlongationTuple.jFun 1 q ∈ R.R₁.integers) :
    R.residue₁ ⟨ProlongationTuple.jFun 1 q, h⟩ = jGeomGen k 1 := by
  obtain ⟨h₁, -, -, -, e₁, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN 0
  have e : (⟨ProlongationTuple.jFun 1 q, h⟩ : R.R₁.integers) = ⟨_, h₁⟩ := Subtype.ext (by simp)
  rw [e, e₁]
  simp

theorem residue₁_jQFun (R : ProlongationTuple P) (hqN : ¬ q ∣ 1) (h : ProlongationTuple.jQFun 1 q ∈ R.R₁.integers) :
    R.residue₁ ⟨ProlongationTuple.jQFun 1 q, h⟩ = jGeomGen k 1 ^ q := by
  obtain ⟨-, -, h₃, -, -, -, e₃, -⟩ := R.residue_jFun_sub_jQFun_sub hqN 0
  have e : (⟨ProlongationTuple.jQFun 1 q, h⟩ : R.R₁.integers) = ⟨_, h₃⟩ := Subtype.ext (by simp)
  rw [e, e₃]
  simp

theorem evF_mem (R : ProlongationTuple P) (hqN : ¬ q ∣ 1) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (p : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K)) : evF K p ∈ R.R₁.integers := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [evF_C]
    exact (R.R₁.algebraMap_mem_iff _).mpr c.2.1
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [evF_X]
    fin_cases i
    · exact jFun_mem R hqN
    · exact jQFun_mem R hqN

noncomputable def evC (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K) →+* ↥(modularFunctionFieldC k 1) :=
  MvPolynomial.eval₂Hom ((algebraMap k ↥(modularFunctionFieldC k 1)).comp (NodeLocalized.redRestrict red K)) ![jGeomGen k 1, jGeomGen k 1 ^ q]

theorem residue₁_evF (R : ProlongationTuple P) (hqN : ¬ q ∣ 1) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (p : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K)) :
    R.residue₁ ⟨evF K p, evF_mem R hqN K p⟩ = evC (q := q) (red := red) K p := by

  have key : R.residue₁.comp ((evF K).codRestrict R.R₁.integers (evF_mem R hqN K)) = evC (q := q) (red := red) K := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · show R.residue₁ ⟨evF K (MvPolynomial.C c), _⟩ = evC (q := q) (red := red) K (MvPolynomial.C c)
      have e : (⟨evF K (MvPolynomial.C c), evF_mem R hqN K (MvPolynomial.C c)⟩ : R.R₁.integers)
          = ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((⟨(c : AlgebraicClosure ℚ), c.2.1⟩ : A) : AlgebraicClosure ℚ),
              (R.R₁.algebraMap_mem_iff _).mpr c.2.1⟩ := Subtype.ext (evF_C K c)
      rw [e, residue₁_const R ⟨(c : AlgebraicClosure ℚ), c.2.1⟩, evC, MvPolynomial.eval₂Hom_C]
      rfl
    · show R.residue₁ ⟨evF K (MvPolynomial.X i), _⟩ = evC (q := q) (red := red) K (MvPolynomial.X i)
      rw [evC, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · have e : (⟨evF K (MvPolynomial.X 0), evF_mem R hqN K (MvPolynomial.X 0)⟩ : R.R₁.integers)
            = ⟨ProlongationTuple.jFun 1 q, jFun_mem R hqN⟩ := Subtype.ext (evF_X K 0)
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        rw [e, residue₁_jFun R hqN]
      · have e : (⟨evF K (MvPolynomial.X 1), evF_mem R hqN K (MvPolynomial.X 1)⟩ : R.R₁.integers)
            = ⟨ProlongationTuple.jQFun 1 q, jQFun_mem R hqN⟩ := Subtype.ext (evF_X K 1)
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
        rw [e, residue₁_jQFun R hqN]
  exact RingHom.congr_fun key p

theorem isUnit_of_redRestrict_ne_zero (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (σ : ↥(NodeLocalized.coeffSubring A K)) (hσ : NodeLocalized.redRestrict red K σ ≠ 0) : IsUnit σ := by
  have hred : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := fun c => by
    rw [← R.redBar_residue, map_eq_zero_iff _ R.redBar.injective, IsLocalRing.residue_eq_zero_iff]
  have hA : IsUnit ((⟨(σ : AlgebraicClosure ℚ), σ.2.1⟩ : A)) := by
    by_contra h
    exact hσ ((hred _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
  obtain ⟨u, hu⟩ := hA
  have hinvA : ((σ : AlgebraicClosure ℚ))⁻¹ ∈ A := by
    have h1 : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) * (σ : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) u.inv_mul
      rw [hu] at this
      simpa using this
    have hσ0 : (σ : AlgebraicClosure ℚ) ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
    have : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = ((σ : AlgebraicClosure ℚ))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [← this]
    exact ((u⁻¹ : Aˣ) : A).2
  have hinvK : ((σ : AlgebraicClosure ℚ))⁻¹ ∈ K := K.inv_mem σ.2.2
  have hσ0 : (σ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hσ
    have : σ = 0 := Subtype.ext h0
    rw [this, map_zero]
  refine ⟨⟨σ, ⟨((σ : AlgebraicClosure ℚ))⁻¹, Subring.mem_inf.mpr ⟨hinvA, hinvK⟩⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hσ0)
  · exact Subtype.ext (inv_mul_cancel₀ hσ0)

theorem core (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ 1)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k ↥(modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces q 1 k)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = w.evalAt (jGeomGen k 1))
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg : g ∈ R.R₁.integers) (a : k) (ha : w.HasValue (R.residue₁ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) a)
    (r s : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K))
    (hs : MvPolynomial.eval₂ (NodeLocalized.redRestrict red K) ![w.evalAt (jGeomGen k 1), w.evalAt (jGeomGen k 1) ^ q] s ≠ 0)
    (hpres : g * evF K s = evF K r) :
    a ∈ Set.range (NodeLocalized.redRestrict red K) := by
  classical

  have hres : (R.residue₁ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) * evC (q := q) (red := red) K s = evC (q := q) (red := red) K r := by
    have e : (⟨g, hg⟩ : R.R₁.integers) * ⟨evF K s, evF_mem R hqN K s⟩ = ⟨evF K r, evF_mem R hqN K r⟩ :=
      Subtype.ext hpres
    rw [← residue₁_evF R hqN K s, ← residue₁_evF R hqN K r, ← map_mul, e]

  have hrat : w.IsRational := hw.1
  have hjmem : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ∈ w.toValuationSubring := hw.2.1.1
  have hj : w.HasValue (jGeomGen k 1) (w.evalAt (jGeomGen k 1)) := ⟨hjmem, (Place.algebraMap_evalAt w hrat hjmem).symm⟩
  have hv : ∀ i : Fin 2, w.HasValue (![jGeomGen k 1, jGeomGen k 1 ^ q] i)
      (![w.evalAt (jGeomGen k 1), w.evalAt (jGeomGen k 1) ^ q] i) := by
    intro i; fin_cases i
    · simpa using hj
    · simpa using hasValue_pow' w hj q
  have hvs := hasValue_eval₂ w (NodeLocalized.redRestrict red K) _ _ hv s
  have hvr := hasValue_eval₂ w (NodeLocalized.redRestrict red K) _ _ hv r

  have h1 := ha.mul hvs
  rw [show (R.residue₁ ⟨g, hg⟩ : ↥(modularFunctionFieldC k 1)) * MvPolynomial.eval₂ ((algebraMap k ↥(modularFunctionFieldC k 1)).comp (NodeLocalized.redRestrict red K))
      ![jGeomGen k 1, jGeomGen k 1 ^ q] s = evC (q := q) (red := red) K r from hres] at h1
  have heq : a * MvPolynomial.eval₂ (NodeLocalized.redRestrict red K) ![w.evalAt (jGeomGen k 1), w.evalAt (jGeomGen k 1) ^ q] s
      = MvPolynomial.eval₂ (NodeLocalized.redRestrict red K) ![w.evalAt (jGeomGen k 1), w.evalAt (jGeomGen k 1) ^ q] r :=
    h1.unique hvr

  have hred : ∀ p : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K),
      MvPolynomial.eval₂ (NodeLocalized.redRestrict red K) ![w.evalAt (jGeomGen k 1), w.evalAt (jGeomGen k 1) ^ q] p
        = NodeLocalized.redRestrict red K (MvPolynomial.eval ![x, x ^ q] p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    | add p p' hp hp' => rw [MvPolynomial.eval₂_add, map_add, map_add, hp, hp']
    | mul_X p i hp =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, map_mul, MvPolynomial.eval_X, hp]
      congr 1
      fin_cases i
      · simp [hx]
      · simp [hx, map_pow]
  rw [hred s, hred r] at heq
  rw [hred s] at hs
  obtain ⟨u, hu⟩ := isUnit_of_redRestrict_ne_zero R K _ hs
  refine ⟨MvPolynomial.eval ![x, x ^ q] r * ↑u⁻¹, ?_⟩
  have hinv : NodeLocalized.redRestrict red K (↑u⁻¹ : ↥(NodeLocalized.coeffSubring A K))
      = (NodeLocalized.redRestrict red K (MvPolynomial.eval ![x, x ^ q] s))⁻¹ := by
    rw [← hu]
    exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])
  rw [map_mul, hinv, ← heq, mul_assoc, mul_inv_cancel₀ hs, mul_one]

end ResRat

namespace ResRat

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem coe_evF (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K)) :
    ((evF (q := q) K p : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) p := by
  have key : (modularFunctionFieldBar (1 * q)).val.toRingHom.comp (evF (q := q) K)
      = NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · show ((evF (q := q) K (MvPolynomial.C c) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
      rw [evF_C, NodeLocalized.modularEval, MvPolynomial.eval₂Hom_C]
      rfl
    · show ((evF (q := q) K (MvPolynomial.X i) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
      rw [evF_X, NodeLocalized.modularEval, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ)
        exact map_jqModC _
      · show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ q (jqModC ℚ)) = jqNModC (AlgebraicClosure ℚ) (1 * q)
        simp only [one_mul]
        rw [jqNModC, coeffMap_qExpand]
        exact congrArg (qExpand (AlgebraicClosure ℚ) q) (map_jqModC _)
  exact RingHom.congr_fun key p

end ResRat

open ResRat in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces q 1 k)
    (hKres : w.evalAt (jGeomGen k 1) ∈ Set.range (NodeLocalized.redRestrict red K))
    (g : ↥(R.nodeIntegersOver K w)) (a : k)
    (ha : w.HasValue (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k 1)) a) :
    a ∈ Set.range (NodeLocalized.redRestrict red K) := by
  classical
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp h)
  obtain ⟨x, hx⟩ := hKres
  have hss : w.evalAt (jGeomGen k 1) ∈ ssJSet q k := hw.2.2
  have ha2 : w.evalAt (jGeomGen k 1) ^ (q ^ 2) = w.evalAt (jGeomGen k 1) := pow_q_sq_eq_self_of_mem_ssJSet q hss
  have hg₁ : (g : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers := g.2.1.1
  have hg₂ : (g : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₂.integers := g.2.1.2.1
  have hgK : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (1 * q) K := g.2.2
  have h₁ : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    (R.mem_integersFst_iff (g : ↥(modularFunctionFieldBar (1 * q)))).mp hg₁
  have h₂ : ((frickeInvolutionBar (1 * q) (g : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    have h := (R.mem_integersSnd_iff (g : ↥(modularFunctionFieldBar (1 * q)))).mp hg₂
    have eAL : ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) :=
      geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar q
    rw [eAL] at h
    exact h
  have hJQ : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : ↥(modularFunctionFieldBar (1 * q))) = ProlongationTuple.jQFun 1 q := by
    apply Subtype.ext
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
    simp only [one_mul]
  have hmem := NodeLocalized.mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg
    red hq (w.evalAt (jGeomGen k 1)) hss ha2 (g : ↥(modularFunctionFieldBar (1 * q))) h₁ h₂ (fun W hW => by
      apply R.ord_nonneg_of_mem_nodeIntegers g.2.1
      apply (reduceFst_eq_iff_centred_levelOne P w hw (w.evalAt (jGeomGen k 1)) rfl W).mpr
      refine ⟨hW.1, ?_⟩
      obtain ⟨y, hy, hyo⟩ := hW.2
      refine ⟨y, hy, ?_⟩
      rw [hJQ] at hyo
      exact hyo) K x hx hgK
  obtain ⟨r, s, hs, hpresL⟩ := (NodeLocalized.mem_modularLocalizedAtPoint _ _ _ _ _).mp hmem
  have hs' : MvPolynomial.eval₂ (NodeLocalized.redRestrict red K)
      ![w.evalAt (jGeomGen k 1), w.evalAt (jGeomGen k 1) ^ q] s ≠ 0 := by
    simpa [NodeLocalized.pointEval] using hs
  have hpresF : (g : ↥(modularFunctionFieldBar (1 * q))) * evF K s = evF K r := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, coe_evF, coe_evF]
    exact hpresL
  exact ResRat.core R hqN K w hw x hx (g : ↥(modularFunctionFieldBar (1 * q))) hg₁ a ha r s hs' hpresF

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst_levelOne_of_five_le (solution)
