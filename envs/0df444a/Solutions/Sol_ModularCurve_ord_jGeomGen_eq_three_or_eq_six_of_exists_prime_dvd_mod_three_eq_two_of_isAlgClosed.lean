-- Prove2me | solution 1 for ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ea581730-a202-57cc-9651-b2f192702227

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

universe u

private theorem fullC_eq_C (k : Type*) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (n : ℕ) [NeZero n] (hℓn : ¬ ℓ ∣ n) :
    modularFunctionFieldFullC k n = modularFunctionFieldC k n := by

  have hF1 : modularFunctionFieldFullC k 1 =
      IntermediateField.adjoin k {(jqModC k : LaurentSeries k)} := by
    apply le_antisymm
    · rw [modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
      rintro x ⟨d, _, hd, rfl⟩
      obtain rfl : d = 1 := Nat.dvd_one.mp hd
      rw [qExpand_one_apply]
      exact IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact jqModC_mem_full k 1

  have hFn : ∀ {m m' : ℕ} [NeZero m] [NeZero m'], m = m' →
      modularFunctionFieldFullC k m = modularFunctionFieldFullC k m' := by
    intro m m' _ _ h
    subst h
    rfl
  have hcast : ((1 * n : ℕ) : k) ≠ 0 := by
    rw [one_mul]
    exact fun h => hℓn ((CharP.cast_eq_zero_iff k ℓ n).mp h)

  have hdeg := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k 1 n hcast).1
  rw [hFn (one_mul n), hF1, dedekindPsi_one, mul_one, one_mul] at hdeg

  have hC : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k n) = dedekindPsi n :=
    relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k n ℓ hℓn
  have hle : modularFunctionFieldC k n ≤ modularFunctionFieldFullC k n :=
    modularFunctionFieldC_le_full k n
  have hA0C : IntermediateField.adjoin k {(jqModC k : LaurentSeries k)} ≤
      modularFunctionFieldC k n := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact jqModC_mem k n

  have htower := IntermediateField.relfinrank_mul_relfinrank
    (A := IntermediateField.adjoin k {(jqModC k : LaurentSeries k)})
    (B := modularFunctionFieldC k n) (C := modularFunctionFieldFullC k n) hA0C hle
  rw [hC, hdeg] at htower
  have hψ : dedekindPsi n ≠ 0 := (dedekindPsi_pos n (NeZero.ne n)).ne'
  have h1 : (modularFunctionFieldC k n).relfinrank (modularFunctionFieldFullC k n) = 1 :=
    mul_left_cancel₀ hψ (htower.trans (mul_one _).symm)
  exact le_antisymm
    ((IntermediateField.relfinrank_eq_one_iff (A := modularFunctionFieldC k n)
      (B := modularFunctionFieldFullC k n)).mp h1) hle

private noncomputable def toC (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) :
    modularFunctionFieldFullC k N →ₐ[k] modularFunctionFieldC k N :=
  (IntermediateField.equivOfEq (fullC_eq_C k q N hqN)).toAlgHom

private theorem toC_surjective (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) : Function.Surjective (toC k q N hqN) :=
  (IntermediateField.equivOfEq (fullC_eq_C k q N hqN)).surjective

private theorem toC_isIntegral (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) : (toC k q N hqN).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ (toC_surjective k q N hqN)

private theorem toC_jq (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) :
    toC k q N hqN ((⟨jqModC k, jqModC_mem_full k N⟩ : modularFunctionFieldFullC k N) -
        algebraMap k (modularFunctionFieldFullC k N) 0) =
      jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0 := by
  exact Subtype.ext rfl

private theorem ramificationIndexAlong_toC (k : Type u) [Field k] (q : ℕ) [Fact q.Prime]
    [CharP k q] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (w : Place k (modularFunctionFieldC k N)) :
    Place.ramificationIndexAlong (toC k q N hqN) w = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have h1 : w.ord (π : modularFunctionFieldC k N) = 1 := w.ord_coe_irreducible hπ
  obtain ⟨g, hg⟩ := toC_surjective k q N hqN π
  have h2 := Place.ord_restrictAlong (toC k q N hqN) (toC_isIntegral k q N hqN) w g
  rw [hg, h1] at h2
  exact_mod_cast Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg _) h2.symm

private theorem ord_toC (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (w : Place k (modularFunctionFieldC k N))
    (g : modularFunctionFieldFullC k N) :
    w.ord (toC k q N hqN g) =
      (w.restrictAlong (toC k q N hqN) (toC_isIntegral k q N hqN)).ord g := by
  rw [Place.ord_restrictAlong (toC k q N hqN) (toC_isIntegral k q N hqN), ramificationIndexAlong_toC]
  simp

private theorem finiteAlong_toC (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) : FiniteAlong k (toC k q N hqN) := by
  unfold FiniteAlong
  letI := algebraAlong (toC k q N hqN)
  exact Module.Finite.of_surjective
    (Algebra.linearMap (modularFunctionFieldFullC k N) (modularFunctionFieldC k N))
    (toC_surjective k q N hqN)

private theorem separableAlong_toC (k : Type u) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) : SeparableAlong k (toC k q N hqN) := by
  unfold SeparableAlong
  letI := algebraAlong (toC k q N hqN)
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := toC_surjective k q N hqN x
  exact isSeparable_algebraMap (K := modularFunctionFieldC k N) y

private theorem restrictAlong_toC_surjective (k : Type u) [Field k] (q : ℕ) [Fact q.Prime]
    [CharP k q] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) :
    Function.Surjective (fun w : Place k (modularFunctionFieldC k N) =>
      w.restrictAlong (toC k q N hqN) (toC_isIntegral k q N hqN)) :=
  Place.restrictAlong_surjective (toC k q N hqN) (toC_isIntegral k q N hqN)
    (finiteAlong_toC k q N hqN) (separableAlong_toC k q N hqN)

private theorem evalAt_jGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five {q' : ℕ} [Fact q'.Prime] {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hq5 : q' < 5) {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q' N k) :
    w.evalAt (jGeomGen k N) = 0 := by
  have hj : w.evalAt (jGeomGen k N) ∈ ssJSet q' k := ((mem_ssPlaces_iff q' N k).1 hw).2.2
  have hpow := pow_q_sq_eq_self_of_mem_ssJSet q' hj
  have hpr : q'.Prime := Fact.out
  have hp : q' = 2 ∨ q' = 3 := by
    have h2 := hpr.two_le
    rcases Nat.lt_or_ge q' 4 with h | h
    · omega
    · have h4 : q' = 4 := by omega
      subst h4
      exact absurd hpr (by decide)
  rcases hp with rfl | rfl
  · exact eq_zero_of_mem_ssJSet_two _ hj hpow
  · exact eq_zero_of_mem_ssJSet_three _ hj hpow

private theorem isRational_of_isAlgClosed {N : ℕ} [NeZero N] {k : Type u} [Field k] [IsAlgClosed k]
    (w : Place k (modularFunctionFieldC k N)) : w.IsRational := by
  haveI : IsCurveOver k (modularFunctionFieldC k N) := isCurveOver_modularFunctionFieldC_of_perfectField k N
  haveI : Module.Finite k w.ResidueField := IsCurveOver.finite_residueField w
  haveI : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite k w.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := w.ResidueField)).2

private theorem mem_valuationSubring_of_evalModularPair_eq_zero {L : Type*} [Field L]
    (A : ValuationSubring L) {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) {x y : L}
    (hx : x ∈ A) (hxy : evalModularPair x y Φ = 0) : y ∈ A := by
  have hint : IsIntegral A y := by
    refine ⟨Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) ⟨x, hx⟩), hΦ.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap A L).comp (Polynomial.eval₂RingHom (Int.castRingHom A) ⟨x, hx⟩)
        = Polynomial.eval₂RingHom (Int.castRingHom L) x := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
    rw [hcomp]
    exact hxy
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hz]
  exact z.2

private theorem ord_pos_of_mem_ssPlaces {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type u}
    [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (hq5 : q < 5)
    {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k) :
    0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) := by
  have hj := evalAt_jGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five hq5 hw
  obtain ⟨hrat, haff, -⟩ := (isSupersingularPlace_iff q N k w).1 ((mem_ssPlaces_iff q N k).1 hw)
  have h := ord_sub_evalAt_pos_of_isRational hrat haff.1 (jGeomGen_sub_algebraMap_ne_zero k N _)
  rwa [hj] at h

private theorem mem_ssPlaces_of_ord_pos {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type u}
    [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (hq5 : q < 5)
    {w : Place k (modularFunctionFieldC k N)}
    (hw : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0)) :
    w ∈ ssPlaces q N k := by
  have hrat := isRational_of_isAlgClosed (N := N) w
  have hw' : 0 < w.ord (jGeomGen k N) := by simpa using hw
  have hne : jGeomGen k N ≠ 0 := by simpa using jGeomGen_sub_algebraMap_ne_zero k N 0
  have hjmem : jGeomGen k N ∈ w.toValuationSubring := w.mem_of_ord_nonneg hne hw'.le
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hjNmem : jNGeomGen k N ∈ w.toValuationSubring :=
    mem_valuationSubring_of_evalModularPair_eq_zero w.toValuationSubring data.monic hjmem
      (evalModularPair_jGeomGen_eq_zero k N data)
  have hcentre : IsCentreOf k N (0, w.evalAt (jNGeomGen k N)) w :=
    ⟨hw, ord_sub_evalAt_pos_of_isRational hrat hjNmem (jNGeomGen_sub_algebraMap_ne_zero k N _)⟩
  refine (mem_ssPlaces_iff q N k).2 ((isSupersingularPlace_iff q N k w).2 ⟨hrat, ⟨hjmem, hjNmem⟩, ?_⟩)
  rw [hcentre.evalAt_jGeomGen]
  exact zero_mem_ssJSet_of_lt_five hq5

private theorem placeRamificationJ_eq_toNat_ord {N : ℕ} [NeZero N] {k : Type u} [Field k]
    {w : Place k (modularFunctionFieldC k N)} (hj : w.evalAt (jGeomGen k N) = 0) :
    placeRamificationJ N w =
      (w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0)).toNat := by
  unfold placeRamificationJ
  rw [hj]

open WeierstrassCurve WeierstrassCurve.Affine in

private theorem indexing_of_j_eq_zero {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type u}
    [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (hq5 : q < 5) (hqN : ¬ q ∣ N)
    (hN : (N : k) ≠ 0) (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.j = 0) :
    ∃ (α : Type u) (f : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} → α),
      (∀ H H', f H = f H' ↔ ∃ γ : VariableChange k, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧
      (∀ H, ∃ w ∈ ssPlaces q N k,
        placeRamificationJ N w = Nat.card {H' : {H : AddSubgroup E₀.toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N} // f H' = f H}) ∧
      (∀ w ∈ ssPlaces q N k, ∃ H,
        placeRamificationJ N w = Nat.card {H' : {H : AddSubgroup E₀.toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N} // f H' = f H}) := by
  classical

  have hfin := finite_setOf_ord_jGeomGen_sub_pos k N (isSeparable_jqNModC_of_natCast_ne_zero k N hN) 0

  let ρ : Place k (modularFunctionFieldC k N) → Place k (modularFunctionFieldFullC k N) :=
    fun w => w.restrictAlong (toC k q N hqN) (toC_isIntegral k q N hqN)
  let S : Finset (Place k (modularFunctionFieldFullC k N)) := hfin.toFinset.image ρ
  have hS : ∀ P, P ∈ S ↔ 0 < P.ord ((⟨jqModC k, jqModC_mem_full k N⟩ : modularFunctionFieldFullC k N) -
      algebraMap k (modularFunctionFieldFullC k N) 0) := by
    intro P
    constructor
    · intro hP
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hP
      have hw' : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) :=
        hfin.mem_toFinset.1 hw
      rwa [← toC_jq k q N hqN, ord_toC] at hw'
    · intro hP
      obtain ⟨w, rfl⟩ := restrictAlong_toC_surjective k q N hqN P
      refine Finset.mem_image.2 ⟨w, hfin.mem_toFinset.2 ?_, rfl⟩
      show 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0)
      rwa [← toC_jq k q N hqN, ord_toC]
  obtain ⟨f, hfS, hSf, hf, hord⟩ :=
    exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC k N hN 0 E₀ hE₀ S hS
  refine ⟨Place k (modularFunctionFieldFullC k N), f, hf, ?_, ?_⟩
  · intro H
    obtain ⟨w, hw₀⟩ := restrictAlong_toC_surjective k q N hqN (f H)
    have hw : ρ w = f H := hw₀
    have hpos : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) 0) := by
      rw [← toC_jq k q N hqN, ord_toC]
      have h := (hS _).1 (hfS H)
      rw [← hw] at h
      exact h
    refine ⟨w, mem_ssPlaces_of_ord_pos hq5 hpos, ?_⟩
    rw [placeRamificationJ_eq_toNat_ord (evalAt_jGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five hq5
      (mem_ssPlaces_of_ord_pos hq5 hpos)), ← toC_jq k q N hqN, ord_toC]
    change ((ρ w).ord _).toNat = _
    rw [hw, hord H]
    exact Int.toNat_natCast _
  · intro w hw
    have hpos := ord_pos_of_mem_ssPlaces hq5 hw
    have hmem : ρ w ∈ S := (hS _).2 (by rwa [← toC_jq k q N hqN, ord_toC] at hpos)
    obtain ⟨H, hH⟩ := hSf _ hmem
    refine ⟨H, ?_⟩
    rw [placeRamificationJ_eq_toNat_ord (evalAt_jGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five hq5 hw),
      ← toC_jq k q N hqN, ord_toC]
    change ((ρ w).ord _).toNat = _
    rw [← hH, hord H]
    exact Int.toNat_natCast _

private theorem model_three_isElliptic (k : Type u) [Field k] [CharP k 3] :
    (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  have hΔ : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k).Δ = 64 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    norm_num
  rw [hΔ]
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  have := (ringChar.spec k 64).mp (by exact_mod_cast h)
  rw [ringChar.eq k 3] at this
  omega

private theorem model_three_j (k : Type u) [Field k] [CharP k 3] :
    letI := model_three_isElliptic k
    (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k).j = 0 := by
  letI := model_three_isElliptic k
  have hc₄ : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k).c₄ = 0 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    have h48 : ((48 : ℕ) : k) = 0 := (ringChar.spec k 48).mpr (by rw [ringChar.eq k 3]; norm_num)
    norm_num
    exact_mod_cast h48
  rw [WeierstrassCurve.j, hc₄]
  simp

open WeierstrassCurve WeierstrassCurve.Affine in

private theorem loc_R2_char3 {N : ℕ} [NeZero N] {k : Type u} [Field k] [CharP k 3] [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ 3 ∣ N) (hN : (N : k) ≠ 0) :
    ∃ (α : Type u) (f : {H : AddSubgroup (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} → α),
      (∀ H H', f H = f H' ↔ ∃ γ : VariableChange k, γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k) = ⟨0, 0, 0, -1, 0⟩ ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k).toAffine T) T') ∧
      (∀ H, ∃ w ∈ ssPlaces 3 N k,
        placeRamificationJ N w = Nat.card {H' : {H : AddSubgroup (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} // f H' = f H}) ∧
      (∀ w ∈ ssPlaces 3 N k, ∃ H,
        placeRamificationJ N w = Nat.card {H' : {H : AddSubgroup (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve k).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} // f H' = f H}) := by
  letI := model_three_isElliptic k
  exact indexing_of_j_eq_zero (q := 3) (by decide) hqN hN _ (model_three_j k)

noncomputable section

namespace B3Step3

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K]

private def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

private theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

private def autPt {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

private theorem autPt_apply {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

private theorem autPt_eq_iff_heq {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

omit [DecidableEq K] in
private theorem heq_some {V V' : WeierstrassCurve.Affine K} (hV : V' = V) {x y : K}
    {h : V.Nonsingular x y} {h' : V'.Nonsingular x y} :
    HEq (Point.some x y h' : V'.Point) (Point.some x y h : V.Point) := by
  subst hV; rfl

omit [DecidableEq K] in
private theorem some_eq_some {V : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂) {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

omit [DecidableEq K] in
private theorem nonsingular_vcInv {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    {x y : K} (h : W.toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular (vcXInv γ x) (vcYInv γ x y) := by
  have h' : (γ • W).toAffine.Nonsingular (vcXInv γ x) (vcYInv γ x y) :=
    (nonsingular_variableChange_iff (vcXInv γ x) (vcYInv γ x y)).mpr
      (by rwa [vcX_vcXInv, vcY_vcYInv])
  rwa [hγ] at h'

private theorem autPt_some {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W) {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    autPt γ hγ (.some x y h) = .some (vcXInv γ x) (vcYInv γ x y) (nonsingular_vcInv γ hγ h) := by
  rw [autPt_eq_iff_heq]
  show HEq (Point.some (vcXInv γ x) (vcYInv γ x y) _ : (γ • W).toAffine.Point) _
  exact heq_some (congrArg WeierstrassCurve.toAffine hγ)

private abbrev Aut (W : WeierstrassCurve K) : Subgroup (VariableChange K) :=
  MulAction.stabilizer (VariableChange K) W

omit [DecidableEq K] in
private theorem smul_eq_of_mem_Aut {W : WeierstrassCurve K} (γ : Aut W) : (γ : VariableChange K) • W = W :=
  MulAction.mem_stabilizer_iff.mp γ.2

omit [DecidableEq K] in
private theorem one_u : (1 : VariableChange K).u = 1 := rfl
omit [DecidableEq K] in
private theorem one_r : (1 : VariableChange K).r = 0 := rfl
omit [DecidableEq K] in
private theorem one_s : (1 : VariableChange K).s = 0 := rfl
omit [DecidableEq K] in
private theorem one_t : (1 : VariableChange K).t = 0 := rfl
omit [DecidableEq K] in
private theorem mul_u (C C' : VariableChange K) : (C * C').u = C.u * C'.u := rfl
omit [DecidableEq K] in
private theorem mul_r (C C' : VariableChange K) : (C * C').r = C.r * C'.u ^ 2 + C'.r := rfl
omit [DecidableEq K] in
private theorem mul_s (C C' : VariableChange K) : (C * C').s = C'.u * C.s + C'.s := rfl
omit [DecidableEq K] in
private theorem mul_t (C C' : VariableChange K) :
    (C * C').t = C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t := rfl

omit [DecidableEq K] in
private theorem vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  rw [vcXInv, one_u, one_r]; simp

omit [DecidableEq K] in
private theorem vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  rw [vcYInv, one_u, one_r, one_s, one_t]; simp

omit [DecidableEq K] in
private theorem vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, mul_u, mul_r, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

omit [DecidableEq K] in
private theorem vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, mul_u, mul_r, mul_s, mul_t, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

private scoped instance instMulActionAutPoint (W : WeierstrassCurve K) : MulAction (Aut W) W.toAffine.Point where
  smul γ P := autPt γ.1 (smul_eq_of_mem_Aut γ) P
  one_smul P := by
    change autPt (1 : VariableChange K) _ P = P
    rcases P with _ | ⟨x, y, h⟩
    · exact map_zero (autPt (1 : VariableChange K) _)
    · rw [autPt_some]
      exact some_eq_some (vcXInv_one x) (vcYInv_one x y)
  mul_smul γ δ P := by
    change autPt (γ.1 * δ.1) _ P = autPt γ.1 _ (autPt δ.1 _ P)
    rcases P with _ | ⟨x, y, h⟩
    · show autPt (γ.1 * δ.1) _ 0 = autPt γ.1 _ (autPt δ.1 _ 0)
      simp only [map_zero]
    · rw [autPt_some, autPt_some, autPt_some]
      exact some_eq_some (vcXInv_mul _ _ x) (vcYInv_mul _ _ x y)

private theorem aut_smul_def {W : WeierstrassCurve K} (γ : Aut W) (P : W.toAffine.Point) :
    γ • P = autPt γ.1 (smul_eq_of_mem_Aut γ) P := rfl

private scoped instance instDistribMulActionAutPoint (W : WeierstrassCurve K) :
    DistribMulAction (Aut W) W.toAffine.Point where
  smul_zero γ := map_zero (autPt γ.1 (smul_eq_of_mem_Aut γ))
  smul_add γ P Q := map_add (autPt γ.1 (smul_eq_of_mem_Aut γ)) P Q

open scoped Pointwise

private abbrev CycSub (W : WeierstrassCurve K) (N : ℕ) : Type _ :=
  {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}

private theorem natCard_smul_addSubgroup {W : WeierstrassCurve K} (γ : Aut W) (H : AddSubgroup W.toAffine.Point) :
    Nat.card (γ • H : AddSubgroup W.toAffine.Point) = Nat.card H := by
  rw [AddSubgroup.pointwise_smul_def]
  exact (Nat.card_congr (H.equivMapOfInjective _ (MulAction.injective γ)).toEquiv).symm

private theorem isAddCyclic_smul_addSubgroup {W : WeierstrassCurve K} (γ : Aut W)
    (H : AddSubgroup W.toAffine.Point) [hH : IsAddCyclic H] :
    IsAddCyclic (γ • H : AddSubgroup W.toAffine.Point) := by
  rw [AddSubgroup.pointwise_smul_def]
  exact isAddCyclic_of_surjective (H.equivMapOfInjective _ (MulAction.injective γ))
    (H.equivMapOfInjective _ (MulAction.injective γ)).surjective

private scoped instance instMulActionAutCycSub (W : WeierstrassCurve K) (N : ℕ) : MulAction (Aut W) (CycSub W N) where
  smul γ H := ⟨γ • H.1, ⟨by haveI := H.2.1; exact isAddCyclic_smul_addSubgroup γ H.1,
    (natCard_smul_addSubgroup γ H.1).trans H.2.2⟩⟩
  one_smul H := Subtype.ext (one_smul (Aut W) H.1)
  mul_smul γ δ H := Subtype.ext (mul_smul γ δ H.1)

private theorem coe_smul_cycSub {W : WeierstrassCurve K} {N : ℕ} (γ : Aut W) (H : CycSub W N) :
    ((γ • H : CycSub W N) : AddSubgroup W.toAffine.Point) = γ • (H : AddSubgroup W.toAffine.Point) := rfl

private theorem rel_iff_mem_orbit {W : WeierstrassCurve K} {N : ℕ} [NeZero N] (H H' : CycSub W N) :
    (∃ γ : VariableChange K, γ • W = W ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T') ↔
      H' ∈ MulAction.orbit (Aut W) H := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    let g : Aut W := ⟨γ, MulAction.mem_stabilizer_iff.mpr hγ⟩
    have hle : (g • H.1 : AddSubgroup W.toAffine.Point) ≤ H'.1 := by
      intro P hP
      obtain ⟨T, hT, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists P g H.1).mp hP
      obtain ⟨T', hT', hh⟩ := h T hT
      have : g • T = T' := (autPt_eq_iff_heq γ hγ T T').mpr hh
      rwa [this]
    haveI : Finite H'.1 := Nat.finite_of_card_ne_zero (by rw [H'.2.2]; exact NeZero.ne N)
    have heq : (g • H.1 : AddSubgroup W.toAffine.Point) = H'.1 :=
      AddSubgroup.eq_of_le_of_card_ge hle (by rw [natCard_smul_addSubgroup, H.2.2, H'.2.2])
    exact MulAction.mem_orbit_iff.mpr ⟨g, Subtype.ext heq⟩
  · intro hmem
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hmem
    refine ⟨g.1, smul_eq_of_mem_Aut g, fun T hT => ⟨g • T, ?_, ?_⟩⟩
    · exact AddSubgroup.smul_mem_pointwise_smul T g H.1 hT
    · exact (autPt_eq_iff_heq g.1 (smul_eq_of_mem_Aut g) T _).mp rfl

private def negVC (W : WeierstrassCurve K) : VariableChange K := ⟨-1, 0, -W.a₁, -W.a₃⟩

omit [DecidableEq K] in
private theorem negVC_smul (W : WeierstrassCurve K) : negVC W • W = W := by
  rw [WeierstrassCurve.ext_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
      negVC, inv_neg_one, Units.val_neg, Units.val_one] <;>
    ring

private def negAut (W : WeierstrassCurve K) : Aut W := ⟨negVC W, MulAction.mem_stabilizer_iff.mpr (negVC_smul W)⟩

private theorem negAut_smul_point {W : WeierstrassCurve K} (P : W.toAffine.Point) : negAut W • P = -P := by
  change autPt (negVC W) _ P = -P
  rcases P with _ | ⟨x, y, h⟩
  · show autPt (negVC W) _ 0 = -0
    rw [map_zero, neg_zero]
  · rw [autPt_some, Point.neg_some]
    refine some_eq_some ?_ ?_
    · show ((((negVC W).u⁻¹ : Kˣ) : K)) ^ 2 * (x - (negVC W).r) = x
      simp [negVC]
    · show ((((negVC W).u⁻¹ : Kˣ) : K)) ^ 3 * (y - (negVC W).t - (negVC W).s * (x - (negVC W).r))
          = W.toAffine.negY x y
      rw [Affine.negY]
      simp [negVC]
      ring

omit [DecidableEq K] in
private theorem negAut_mul_self (W : WeierstrassCurve K) : negAut W * negAut W = 1 := by
  refine Subtype.ext (VariableChange.ext ?_ ?_ ?_ ?_)
  · show (negVC W).u * (negVC W).u = 1
    simp [negVC]
  · show (negVC W).r * (negVC W).u ^ 2 + (negVC W).r = 0
    simp [negVC]
  · show (negVC W).u * (negVC W).s + (negVC W).s = 0
    simp [negVC]
  · show (negVC W).t * (negVC W).u ^ 3 + (negVC W).r * (negVC W).s * (negVC W).u ^ 2 + (negVC W).t = 0
    simp only [negVC]
    push_cast
    ring

omit [DecidableEq K] in
private theorem negAut_ne_one (W : WeierstrassCurve K) (h2 : ringChar K ≠ 2) : negAut W ≠ 1 := by
  intro h
  have hu : ((negVC W).u : K) = ((1 : VariableChange K).u : K) :=
    congrArg (fun g : Aut W => ((g.1).u : K)) h
  rw [one_u] at hu
  have hneg : ((negVC W).u : K) = -1 := by simp [negVC]
  rw [hneg, Units.val_one] at hu
  have : (2 : K) = 0 := by linear_combination -hu
  exact Ring.two_ne_zero h2 this

omit [DecidableEq K] in
private theorem orderOf_negAut (W : WeierstrassCurve K) (h2 : ringChar K ≠ 2) : orderOf (negAut W) = 2 :=
  orderOf_eq_prime (by rw [pow_two, negAut_mul_self]) (negAut_ne_one W h2)

private theorem negAut_smul_addSubgroup {W : WeierstrassCurve K} (H : AddSubgroup W.toAffine.Point) :
    negAut W • H = H := by
  ext P
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : (negAut W)⁻¹ = negAut W :=
    inv_eq_of_mul_eq_one_right (negAut_mul_self W)
  rw [hinv, negAut_smul_point]
  exact neg_mem_iff

private theorem negAut_mem_stabilizer {W : WeierstrassCurve K} {N : ℕ} (H : CycSub W N) :
    negAut W ∈ MulAction.stabilizer (Aut W) H :=
  MulAction.mem_stabilizer_iff.mpr (Subtype.ext (negAut_smul_addSubgroup H.1))

private abbrev modelThree (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

omit [DecidableEq K] in
private theorem three_eq_zero' [CharP K 3] : (3 : K) = 0 := by
  have := CharP.cast_eq_zero K 3
  exact_mod_cast this

omit [DecidableEq K] in
private theorem two_ne_zero' [CharP K 3] : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 3] at h'
  omega

omit [DecidableEq K] in

private theorem smul_modelThree_eq_iff [CharP K 3] (γ : VariableChange K) :
    γ • modelThree K = modelThree K ↔
      γ.s = 0 ∧ γ.t = 0 ∧ ((γ.u : K)) ^ 4 = 1 ∧ γ.r ^ 3 = γ.r := by
  have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
  have h3 : (3 : K) = 0 := three_eq_zero'
  have h2 : (2 : K) ≠ 0 := two_ne_zero'
  rw [WeierstrassCurve.ext_iff]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
    Units.val_inv_eq_inv_val, h3]

  simp only [zero_add, add_zero, mul_zero, zero_mul, sub_zero, zero_sub, mul_one, mul_neg]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
    have hs : γ.s = 0 := by
      have := h₁
      field_simp at this
      rcases mul_eq_zero.mp (by linear_combination this : (2 : K) * γ.s = 0) with h | h
      · exact absurd h h2
      · exact h
    have ht : γ.t = 0 := by
      have := h₃
      field_simp at this
      rcases mul_eq_zero.mp (by linear_combination this : (2 : K) * γ.t = 0) with h | h
      · exact absurd h h2
      · exact h
    refine ⟨hs, ht, ?_, ?_⟩
    · have := h₄
      rw [hs, ht] at this
      field_simp at this
      linear_combination this
    · have := h₆
      rw [ht] at this
      field_simp at this
      linear_combination this
  · rintro ⟨hs, ht, hu4, hr⟩
    rw [hs, ht]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · field_simp
      rw [hu4]
      ring
    · field_simp
      linear_combination hr

private def autModelThreeEquiv [CharP K 3] :
    Aut (modelThree K) ≃ {u : Kˣ // ((u : K)) ^ 4 = 1} × {r : K // r ^ 3 = r} where
  toFun γ :=
    (⟨γ.1.u, ((smul_modelThree_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)).2.2.1⟩,
      ⟨γ.1.r, ((smul_modelThree_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)).2.2.2⟩)
  invFun p :=
    ⟨⟨p.1.1, p.2.1, 0, 0⟩, MulAction.mem_stabilizer_iff.mpr
      ((smul_modelThree_eq_iff _).mpr ⟨rfl, rfl, p.1.2, p.2.2⟩)⟩
  left_inv γ := by
    obtain ⟨hs, ht, -, -⟩ := (smul_modelThree_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)
    exact Subtype.ext (VariableChange.ext rfl rfl hs.symm ht.symm)
  right_inv p := rfl

omit [DecidableEq K] in

private theorem natCard_fourthRoots_dvd : Nat.card {u : Kˣ // ((u : K)) ^ 4 = 1} ∣ 4 := by
  have e : {u : Kˣ // ((u : K)) ^ 4 = 1} ≃ rootsOfUnity 4 K :=
    Equiv.subtypeEquivRight fun u => by
      rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  rw [Nat.card_congr e]
  have hexp : Monoid.exponent (rootsOfUnity 4 K) ∣ 4 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun ζ =>
      Subtype.ext (by simpa using (mem_rootsOfUnity 4 ζ.1).mp ζ.2)
  exact (IsCyclic.exponent_eq_card (α := rootsOfUnity 4 K)) ▸ hexp

omit [DecidableEq K] in

private theorem natCard_cubeRoots [CharP K 3] : Nat.card {r : K // r ^ 3 = r} = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let φ : ZMod 3 → {r : K // r ^ 3 = r} := fun z =>
    ⟨ZMod.castHom (dvd_refl 3) K z, by
      rw [← map_pow, ZMod.pow_card z]⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      exact ZMod.castHom_injective K (congrArg Subtype.val hab)
    · rintro ⟨r, hr⟩
      have h3 : (3 : K) = 0 := three_eq_zero'
      have hfac : r * (r - 1) * (r + 1) = 0 := by linear_combination hr
      rcases mul_eq_zero.mp hfac with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact ⟨0, Subtype.ext (by simp [φ, h])⟩
        · exact ⟨1, Subtype.ext (by simp [φ, sub_eq_zero.mp h])⟩
      · refine ⟨2, Subtype.ext ?_⟩
        have hr' : r = -1 := by linear_combination h
        simp only [φ, map_ofNat]
        rw [hr']
        linear_combination h3
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_zmod]

omit [DecidableEq K] in

private theorem natCard_aut_modelThree_dvd [CharP K 3] : Nat.card (Aut (modelThree K)) ∣ 12 := by
  rw [Nat.card_congr autModelThreeEquiv, Nat.card_prod, natCard_cubeRoots]
  exact Nat.mul_dvd_mul_right natCard_fourthRoots_dvd 3

omit [DecidableEq K] in
private theorem ringChar_ne_two' [CharP K 3] : ringChar K ≠ 2 := by
  rw [ringChar.eq K 3]
  decide

private theorem natCard_orbit_dvd_six [CharP K 3] {N : ℕ} (H : CycSub (modelThree K) N) :
    Nat.card (MulAction.orbit (Aut (modelThree K)) H) ∣ 6 := by
  have hos : (MulAction.stabilizer (Aut (modelThree K)) H).index *
      Nat.card (MulAction.stabilizer (Aut (modelThree K)) H) = Nat.card (Aut (modelThree K)) :=
    Subgroup.index_mul_card _
  have hidx : (MulAction.stabilizer (Aut (modelThree K)) H).index =
      Nat.card (MulAction.orbit (Aut (modelThree K)) H) := by
    rw [MulAction.index_stabilizer]; rfl
  have h2dvd : 2 ∣ Nat.card (MulAction.stabilizer (Aut (modelThree K)) H) := by
    have := orderOf_dvd_natCard
      (⟨negAut (modelThree K), negAut_mem_stabilizer H⟩ : MulAction.stabilizer (Aut (modelThree K)) H)
    rwa [Subgroup.orderOf_mk, orderOf_negAut (modelThree K) ringChar_ne_two'] at this
  obtain ⟨c, hc⟩ := h2dvd
  rw [hidx, hc] at hos
  have h12 : Nat.card (MulAction.orbit (Aut (modelThree K)) H) * 2 ∣ 6 * 2 := by
    refine dvd_trans ⟨c, ?_⟩ (natCard_aut_modelThree_dvd (K := K))
    rw [← hos]; ring
  exact Nat.dvd_of_mul_dvd_mul_right two_pos h12

private theorem natCard_fibre_dvd_six [CharP K 3] (N : ℕ) [NeZero N] {α : Type*}
    (f : CycSub (modelThree K) N → α)
    (hf : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • modelThree K = modelThree K ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ (modelThree K).toAffine T) T')
    (H : CycSub (modelThree K) N) :
    Nat.card {H' : CycSub (modelThree K) N // f H' = f H} ∣ 6 := by
  have e : {H' : CycSub (modelThree K) N // f H' = f H} ≃ MulAction.orbit (Aut (modelThree K)) H :=
    Equiv.subtypeEquivRight (fun H' => by
      rw [eq_comm, hf H H', rel_iff_mem_orbit H H']
      try rfl)
  rw [Nat.card_congr e]
  exact natCard_orbit_dvd_six H

private def transVC : VariableChange K := ⟨1, 1, 0, 0⟩

omit [DecidableEq K] in
private theorem transVC_u : (transVC : VariableChange K).u = 1 := rfl
omit [DecidableEq K] in
private theorem transVC_r : (transVC : VariableChange K).r = 1 := rfl
omit [DecidableEq K] in
private theorem transVC_s : (transVC : VariableChange K).s = 0 := rfl
omit [DecidableEq K] in
private theorem transVC_t : (transVC : VariableChange K).t = 0 := rfl

omit [DecidableEq K] in
private theorem transVC_smul [CharP K 3] : (transVC : VariableChange K) • modelThree K = modelThree K :=
  (smul_modelThree_eq_iff _).mpr ⟨rfl, rfl, by rw [transVC_u, Units.val_one, one_pow], by rw [transVC_r, one_pow]⟩

private def transAut [CharP K 3] : Aut (modelThree K) :=
  ⟨transVC, MulAction.mem_stabilizer_iff.mpr transVC_smul⟩

omit [DecidableEq K] in

private theorem transAut_cube [CharP K 3] :
    (transAut : Aut (modelThree K)) * transAut * transAut = 1 := by
  have h3 : (3 : K) = 0 := three_eq_zero'
  apply Subtype.ext
  apply VariableChange.ext
  · show (transVC * transVC * transVC).u = (1 : VariableChange K).u
    simp only [mul_u, transVC_u, one_u, mul_one]
  · show (transVC * transVC * transVC).r = (1 : VariableChange K).r
    simp only [mul_r, transVC_u, transVC_r, one_r, Units.val_one, one_pow, mul_one]
    linear_combination h3
  · show (transVC * transVC * transVC).s = (1 : VariableChange K).s
    simp only [mul_s, transVC_u, transVC_s, one_s, Units.val_one, mul_zero, add_zero]
  · show (transVC * transVC * transVC).t = (1 : VariableChange K).t
    simp only [mul_t, mul_r, transVC_u, transVC_r, transVC_s, transVC_t, one_t, Units.val_one, one_pow, mul_one,
      mul_zero, add_zero]

omit [DecidableEq K] in
private theorem transAut_ne_one [CharP K 3] : (transAut : Aut (modelThree K)) ≠ 1 := by
  intro h
  have hr : (transVC : VariableChange K).r = (1 : VariableChange K).r :=
    congrArg (fun g : Aut (modelThree K) => (g.1).r) h
  rw [transVC_r, one_r] at hr
  exact one_ne_zero hr

omit [DecidableEq K] in
private theorem orderOf_transAut [CharP K 3] : orderOf (transAut : Aut (modelThree K)) = 3 :=
  orderOf_eq_prime (by rw [pow_three', transAut_cube]) transAut_ne_one

omit [DecidableEq K] in

private theorem u_eq_one_of_pow_three [CharP K 3] (g : Aut (modelThree K)) (hg : g ^ 3 = 1) : (g.1.u : K) = 1 := by
  have hu4 : (g.1.u : K) ^ 4 = 1 := ((smul_modelThree_eq_iff g.1).mp (smul_eq_of_mem_Aut g)).2.2.1
  have hcube : g * g * g = 1 := by
    rw [← pow_three']
    exact hg
  have hu3' : (g.1.u : K) * (g.1.u : K) * (g.1.u : K) = 1 :=
    congrArg (fun a : Aut (modelThree K) => ((a.1.u : Kˣ) : K)) hcube
  have hu3 : (g.1.u : K) ^ 3 = 1 := by
    rw [pow_three']
    exact hu3'
  calc (g.1.u : K) = (g.1.u : K) * (g.1.u : K) ^ 3 := by rw [hu3, mul_one]
    _ = (g.1.u : K) ^ 4 := by ring
    _ = 1 := hu4

private theorem eq_one_of_smul_some_eq [CharP K 3] (g : Aut (modelThree K)) (hg : g ^ 3 = 1) {x y : K}
    (h : (modelThree K).toAffine.Nonsingular x y) (hfix : g • (Point.some x y h) = Point.some x y h) : g = 1 := by
  obtain ⟨hs, ht, -, -⟩ := (smul_modelThree_eq_iff g.1).mp (smul_eq_of_mem_Aut g)
  have hu : (g.1.u : K) = 1 := u_eq_one_of_pow_three g hg
  rw [aut_smul_def, autPt_some] at hfix
  have hx : vcXInv g.1 x = x := (Point.some.inj hfix).1
  have hx' : ((g.1.u⁻¹ : Kˣ) : K) ^ 2 * (x - g.1.r) = x := hx
  rw [Units.val_inv_eq_inv_val, hu, inv_one, one_pow, one_mul] at hx'
  have hr : g.1.r = 0 := by linear_combination -hx'
  apply Subtype.ext
  apply VariableChange.ext
  · show g.1.u = 1
    exact Units.ext (by rw [hu, Units.val_one])
  · show g.1.r = 0
    exact hr
  · show g.1.s = 0
    exact hs
  · show g.1.t = 0
    exact ht

private theorem smul_zsmul_point {W : WeierstrassCurve K} (γ : Aut W) (n : ℤ) (P : W.toAffine.Point) :
    γ • (n • P) = n • (γ • P) :=
  map_zsmul (DistribSMul.toAddMonoidHom W.toAffine.Point γ) n P

private theorem false_of_dvd_pow_three_sub_one {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 2) (k : ℤ)
    (hq_dvd : (q : ℤ) ∣ k ^ 3 - 1) (hq_ndvd : ¬ (q : ℤ) ∣ k - 1) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hz3 : ((k : ZMod q)) ^ 3 = 1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ 3 - 1) q).mpr hq_dvd
    push_cast at h
    linear_combination h
  have hz1 : (k : ZMod q) ≠ 1 := by
    intro h1
    apply hq_ndvd
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h1, sub_self]
  have hz0 : (k : ZMod q) ≠ 0 := by
    intro h0
    rw [h0] at hz3
    simp at hz3
  have hord : orderOf (k : ZMod q) = 3 := orderOf_eq_prime hz3 hz1
  have hdvd : orderOf (k : ZMod q) ∣ q - 1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hz0)
  rw [hord] at hdvd
  have := hq.two_le
  omega

private theorem exists_forall_smul_eq_zsmul {W : WeierstrassCurve K} {N : ℕ} (H : CycSub W N) (g : Aut W)
    (hgH : g ∈ MulAction.stabilizer (Aut W) H) :
    ∃ k : ℤ, ∀ T : H.1, g • (T : W.toAffine.Point) = k • (T : W.toAffine.Point) := by
  have hstab : (g • H.1 : AddSubgroup W.toAffine.Point) = H.1 :=
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hgH)
  have hmem : ∀ T : H.1, g • (T : W.toAffine.Point) ∈ H.1 := by
    intro T
    have h := AddSubgroup.smul_mem_pointwise_smul _ g H.1 T.2
    rwa [hstab] at h
  haveI : IsAddCyclic H.1 := H.2.1
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : H.1, ∀ T : H.1, T ∈ AddSubgroup.zmultiples h₀ := IsAddCyclic.exists_generator
  obtain ⟨k, hk₀⟩ := AddSubgroup.mem_zmultiples_iff.mp (hh₀ ⟨_, hmem h₀⟩)
  have hk₀' : g • (h₀ : W.toAffine.Point) = k • (h₀ : W.toAffine.Point) := (congrArg Subtype.val hk₀).symm
  refine ⟨k, fun T => ?_⟩
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp (hh₀ T)
  have ha' : (T : W.toAffine.Point) = a • (h₀ : W.toAffine.Point) := (congrArg Subtype.val ha).symm
  rw [ha', smul_zsmul_point, hk₀', ← mul_zsmul, ← mul_zsmul, mul_comm]

private theorem exists_coe_addOrderOf_eq {W : WeierstrassCurve K} {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime)
    (hqN : q ∣ N) (H : CycSub W N) :
    ∃ P : H.1, addOrderOf (P : W.toAffine.Point) = q ∧ (P : W.toAffine.Point) ≠ 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [H.2.2]; exact NeZero.ne N)
  obtain ⟨P, hP⟩ : ∃ P : H.1, addOrderOf P = q := exists_prime_addOrderOf_dvd_card' q (by rw [H.2.2]; exact hqN)
  have hPord : addOrderOf (P : W.toAffine.Point) = q := by
    rw [AddSubgroup.addOrderOf_coe]
    exact hP
  refine ⟨P, hPord, fun h0 => ?_⟩
  rw [h0, addOrderOf_zero] at hPord
  exact hq.one_lt.ne hPord

private theorem not_mem_stabilizer_of_orderOf_eq_three [CharP K 3] {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime)
    (hqN : q ∣ N) (hq3 : q % 3 = 2) (H : CycSub (modelThree K) N) (g : Aut (modelThree K))
    (hg3 : orderOf g = 3) : g ∉ MulAction.stabilizer (Aut (modelThree K)) H := by
  intro hgH
  have hgpow : g ^ 3 = 1 := by
    rw [← hg3]
    exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg3
    omega
  obtain ⟨k, hact⟩ := exists_forall_smul_eq_zsmul H g hgH
  obtain ⟨P, hPord, hPne⟩ := exists_coe_addOrderOf_eq hq hqN H
  have hk : g • (P : (modelThree K).toAffine.Point) = k • (P : (modelThree K).toAffine.Point) := hact P
  have hk3 : (k ^ 3) • (P : (modelThree K).toAffine.Point) = P := by
    have h1 : g • (g • (g • (P : (modelThree K).toAffine.Point))) = P := by
      rw [smul_smul, smul_smul, ← pow_three', hgpow, one_smul]
    rw [hk, smul_zsmul_point, hk, smul_zsmul_point, smul_zsmul_point, hk, ← mul_zsmul, ← mul_zsmul] at h1
    rw [pow_three']
    exact h1
  have hk1 : k • (P : (modelThree K).toAffine.Point) ≠ P := by
    intro hfix
    rw [← hk] at hfix
    obtain ⟨x, y, h, hsome⟩ : ∃ (x y : K) (h : (modelThree K).toAffine.Nonsingular x y),
        (P : (modelThree K).toAffine.Point) = Point.some x y h := by
      rcases hPt : (P : (modelThree K).toAffine.Point) with _ | ⟨x, y, h⟩
      · exact absurd hPt hPne
      · exact ⟨x, y, h, rfl⟩
    rw [hsome] at hfix
    exact hg1 (eq_one_of_smul_some_eq g hgpow h hfix)
  refine false_of_dvd_pow_three_sub_one hq hq3 k ?_ ?_
  · rw [← hPord, addOrderOf_dvd_iff_zsmul_eq_zero, sub_zsmul, one_zsmul, hk3, ← sub_eq_add_neg, sub_self]
  · intro hdvd
    apply hk1
    rw [← hPord, addOrderOf_dvd_iff_zsmul_eq_zero, sub_zsmul, one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at hdvd
    exact hdvd

private theorem three_dvd_natCard_orbit [CharP K 3] {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (hq3 : q % 3 = 2) (H : CycSub (modelThree K) N) :
    3 ∣ Nat.card (MulAction.orbit (Aut (modelThree K)) H) := by
  haveI : Finite (Aut (modelThree K)) := by
    apply Nat.finite_of_card_ne_zero
    intro h0
    have h12 := natCard_aut_modelThree_dvd (K := K)
    rw [h0] at h12
    norm_num at h12
  have h3aut : 3 ∣ Nat.card (Aut (modelThree K)) := by
    have h := orderOf_dvd_natCard (transAut : Aut (modelThree K))
    rwa [orderOf_transAut] at h
  have hstab : ¬ 3 ∣ Nat.card (MulAction.stabilizer (Aut (modelThree K)) H) := by
    intro h3
    obtain ⟨g, hg⟩ : ∃ g : MulAction.stabilizer (Aut (modelThree K)) H, orderOf g = 3 :=
      exists_prime_orderOf_dvd_card' 3 h3
    rw [← Subgroup.orderOf_coe] at hg
    exact not_mem_stabilizer_of_orderOf_eq_three hq hqN hq3 H g.1 hg g.2
  have hos : (MulAction.stabilizer (Aut (modelThree K)) H).index *
      Nat.card (MulAction.stabilizer (Aut (modelThree K)) H) = Nat.card (Aut (modelThree K)) :=
    Subgroup.index_mul_card _
  have hidx : (MulAction.stabilizer (Aut (modelThree K)) H).index =
      Nat.card (MulAction.orbit (Aut (modelThree K)) H) := by
    rw [MulAction.index_stabilizer]; rfl
  rw [hidx] at hos
  rw [← hos] at h3aut
  exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h3aut).resolve_right hstab

private theorem natCard_fibre_eq_three_or_six [CharP K 3] (N : ℕ) [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (hq3 : q % 3 = 2) {α : Type*} (f : CycSub (modelThree K) N → α)
    (hf : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • modelThree K = modelThree K ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ (modelThree K).toAffine T) T')
    (H : CycSub (modelThree K) N) :
    Nat.card {H' : CycSub (modelThree K) N // f H' = f H} = 3 ∨
      Nat.card {H' : CycSub (modelThree K) N // f H' = f H} = 6 := by
  have h6 := natCard_fibre_dvd_six N f hf H
  have e : {H' : CycSub (modelThree K) N // f H' = f H} ≃ MulAction.orbit (Aut (modelThree K)) H :=
    Equiv.subtypeEquivRight (fun H' => by
      rw [eq_comm, hf H H', rel_iff_mem_orbit H H']
      try rfl)
  have h3 : 3 ∣ Nat.card {H' : CycSub (modelThree K) N // f H' = f H} := by
    rw [Nat.card_congr e]
    exact three_dvd_natCard_orbit hq hqN hq3 H
  have hle : Nat.card {H' : CycSub (modelThree K) N // f H' = f H} ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  obtain ⟨n, hn⟩ : ∃ n, Nat.card {H' : CycSub (modelThree K) N // f H' = f H} = n := ⟨_, rfl⟩
  rw [hn] at h6 h3 hle ⊢
  interval_cases n <;> omega

end B3Step3
p2m_reactivate "P2MW.S_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed.B3Step3"

end
p2m_reactivate "P2MW.S_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed.B3Step3"

theorem solution
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F]
    (x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N'))
    (hx : 0 < x.ord (ModularCurve.jGeomGen F N')) :
    x.ord (ModularCurve.jGeomGen F N') = 3 ∨ x.ord (ModularCurve.jGeomGen F N') = 6 := by
  classical
  obtain ⟨q, hq, hqN, hq3⟩ := hε
  have hN : (N' : F) ≠ 0 := by
    intro h
    exact hpN' ((CharP.cast_eq_zero_iff F 3 N').mp h)
  have hx' : 0 < x.ord (jGeomGen F N' - algebraMap F (modularFunctionFieldC F N') 0) := by
    rwa [map_zero, sub_zero]
  have hw : x ∈ ssPlaces 3 N' F := mem_ssPlaces_of_ord_pos (q := 3) (by decide) hx'
  have hj : x.evalAt (jGeomGen F N') = 0 :=
    evalAt_jGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five (q' := 3) (by decide) hw
  obtain ⟨α, f, hf, -, hidx⟩ := loc_R2_char3 (k := F) hpN' hN
  obtain ⟨H, hH⟩ := hidx x hw
  have hfib' : placeRamificationJ N' x = 3 ∨ placeRamificationJ N' x = 6 := by
    rw [hH]
    exact B3Step3.natCard_fibre_eq_three_or_six N' hq hqN hq3 f hf H
  rw [placeRamificationJ_eq_toNat_ord hj, map_zero, sub_zero] at hfib'
  omega

end S_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed (solution)
