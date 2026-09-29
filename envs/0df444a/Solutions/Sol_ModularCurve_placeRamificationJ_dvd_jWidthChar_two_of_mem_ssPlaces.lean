-- Prove2me | solution 1 for ModularCurve.placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0c835e20-2dee-5354-9951-afd6cf824a28

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

namespace P2MW.S_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
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

private theorem model_two_isElliptic (k : Type u) [Field k] [CharP k 2] :
    (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  have hΔ : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k).Δ = -27 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    norm_num
  rw [hΔ]
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  have h27 : ((27 : ℕ) : k) = 0 := by
    have h' : (27 : k) = 0 := by linear_combination -h
    exact_mod_cast h'
  have := (ringChar.spec k 27).mp h27
  rw [ringChar.eq k 2] at this
  omega

private theorem model_two_j (k : Type u) [Field k] [CharP k 2] :
    letI := model_two_isElliptic k
    (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k).j = 0 := by
  letI := model_two_isElliptic k
  have hc₄ : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k).c₄ = 0 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    norm_num
  rw [WeierstrassCurve.j, hc₄]
  simp

open WeierstrassCurve WeierstrassCurve.Affine in

private theorem loc_R2_char2 {N : ℕ} [NeZero N] {k : Type u} [Field k] [CharP k 2] [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ 2 ∣ N) (hN : (N : k) ≠ 0) :
    ∃ (α : Type u) (f : {H : AddSubgroup (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} → α),
      (∀ H H', f H = f H' ↔ ∃ γ : VariableChange k, γ • (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k) = ⟨0, 0, 1, 0, 0⟩ ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k).toAffine T) T') ∧
      (∀ H, ∃ w ∈ ssPlaces 2 N k,
        placeRamificationJ N w = Nat.card {H' : {H : AddSubgroup (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} // f H' = f H}) ∧
      (∀ w ∈ ssPlaces 2 N k, ∃ H,
        placeRamificationJ N w = Nat.card {H' : {H : AddSubgroup (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve k).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} // f H' = f H}) := by
  letI := model_two_isElliptic k
  exact indexing_of_j_eq_zero (q := 2) (by decide) hqN hN _ (model_two_j k)

noncomputable section

namespace SupersingularWidthTwo

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

omit [DecidableEq K] in

private theorem negAut_ne_one_of_a₃_ne_zero (W : WeierstrassCurve K) (h : W.a₃ ≠ 0) : negAut W ≠ 1 := by
  intro h1
  have ht : (negVC W).t = (1 : VariableChange K).t := congrArg (fun g : Aut W => (g.1).t) h1
  rw [one_t] at ht
  have hneg : (negVC W).t = -W.a₃ := rfl
  rw [hneg, neg_eq_zero] at ht
  exact h ht

omit [DecidableEq K] in
private theorem orderOf_negAut_of_a₃_ne_zero (W : WeierstrassCurve K) (h : W.a₃ ≠ 0) : orderOf (negAut W) = 2 :=
  orderOf_eq_prime (by rw [pow_two, negAut_mul_self]) (negAut_ne_one_of_a₃_ne_zero W h)

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

private abbrev modelTwo (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

omit [DecidableEq K] in
private theorem two_eq_zero'' [CharP K 2] : (2 : K) = 0 := by
  have := CharP.cast_eq_zero K 2
  exact_mod_cast this

omit [DecidableEq K] in

private theorem smul_modelTwo_eq_iff [CharP K 2] (γ : VariableChange K) :
    γ • modelTwo K = modelTwo K ↔
      ((γ.u : K)) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s = γ.r ^ 2 ∧ γ.t ^ 2 + γ.t = γ.r ^ 3 := by
  have h2 : (2 : K) = 0 := two_eq_zero''
  have hw : ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) = 1 := Units.inv_mul γ.u
  have hwne : ((γ.u⁻¹ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  constructor
  · intro h
    have h₂ := congrArg WeierstrassCurve.a₂ h
    have h₃ := congrArg WeierstrassCurve.a₃ h
    have h₄ := congrArg WeierstrassCurve.a₄ h
    have h₆ := congrArg WeierstrassCurve.a₆ h
    rw [variableChange_a₂] at h₂
    rw [variableChange_a₃] at h₃
    rw [variableChange_a₄] at h₄
    rw [variableChange_a₆] at h₆
    simp only at h₂ h₃ h₄ h₆
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (-((γ.u : K)) ^ 3) * h₃
        + (1 + 2 * γ.t) * (((γ.u⁻¹ : Kˣ) : K) ^ 2 * ((γ.u : K)) ^ 2 + ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) + 1) * hw
        + γ.t * h2
    · rcases mul_eq_zero.mp h₂ with h' | h'
      · exact absurd h' (pow_ne_zero _ hwne)
      · linear_combination h' - γ.r * h2
    · rcases mul_eq_zero.mp h₄ with h' | h'
      · exact absurd h' (pow_ne_zero _ hwne)
      · linear_combination -h' + (γ.r ^ 2 - γ.s * γ.t) * h2
    · rcases mul_eq_zero.mp h₆ with h' | h'
      · exact absurd h' (pow_ne_zero _ hwne)
      · linear_combination -h'
  · rintro ⟨hu3, hr, hs, ht⟩
    have hw3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      linear_combination (-(((γ.u⁻¹ : Kˣ) : K)) ^ 3) * hu3
        + (((γ.u⁻¹ : Kˣ) : K) ^ 2 * ((γ.u : K)) ^ 2 + ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) + 1) * hw
    rw [WeierstrassCurve.ext_iff]
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆,
      modelTwo]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · linear_combination ((γ.u⁻¹ : Kˣ) : K) * γ.s * h2
    · linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 2 * (hr + γ.r * h2)
    · linear_combination hw3 + ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2
    · linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 4 * (-hs + (γ.r ^ 2 - γ.s * γ.t) * h2)
    · linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 6 * (-ht)

omit [DecidableEq K] in
private def cubeRootsEquiv : {u : Kˣ // ((u : K)) ^ 3 = 1} ≃ rootsOfUnity 3 K :=
  Equiv.subtypeEquivRight fun u => by
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]

omit [DecidableEq K] in

private theorem natCard_cubeRoots_dvd : Nat.card {u : Kˣ // ((u : K)) ^ 3 = 1} ∣ 3 := by
  rw [Nat.card_congr (cubeRootsEquiv (K := K))]
  have hexp : Monoid.exponent (rootsOfUnity 3 K) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun ζ =>
      Subtype.ext (by simpa using (mem_rootsOfUnity 3 ζ.1).mp ζ.2)
  exact (IsCyclic.exponent_eq_card (α := rootsOfUnity 3 K)) ▸ hexp

private def fourthFixedEquiv : {r : K // r ^ 4 = r} ≃ {u : Kˣ // ((u : K)) ^ 3 = 1} ⊕ Unit where
  toFun r :=
    if h : (r : K) = 0 then Sum.inr () else
      Sum.inl ⟨Units.mk0 (r : K) h, by
        have hr : (r : K) ^ 4 = (r : K) := r.2
        have hfac : (r : K) * ((r : K) ^ 3 - 1) = 0 := by linear_combination hr
        rcases mul_eq_zero.mp hfac with h' | h'
        · exact absurd h' h
        · rw [Units.val_mk0]
          exact sub_eq_zero.mp h'⟩
  invFun p :=
    match p with
    | Sum.inl u => ⟨(u.1 : K), by
        have h3 : ((u.1 : K)) ^ 3 = 1 := u.2
        calc ((u.1 : K)) ^ 4 = ((u.1 : K)) ^ 3 * (u.1 : K) := by ring
          _ = (u.1 : K) := by rw [h3, one_mul]⟩
    | Sum.inr _ => ⟨0, by simp⟩
  left_inv r := by
    by_cases h : (r : K) = 0
    · simp only [h, dite_true]
      exact Subtype.ext h.symm
    · simp only [h, dite_false]
      exact Subtype.ext (by simp)
  right_inv p := by
    rcases p with u | u
    · have hne : (u.1 : K) ≠ 0 := u.1.ne_zero
      simp only [hne, dite_false]
      congr 1
      exact Subtype.ext (Units.ext (by simp))
    · simp

private theorem natCard_fourthFixed_dvd : Nat.card {r : K // r ^ 4 = r} ∣ 4 := by
  haveI : Finite {u : Kˣ // ((u : K)) ^ 3 = 1} := Finite.of_equiv _ (cubeRootsEquiv (K := K)).symm
  have hdvd : Nat.card {u : Kˣ // ((u : K)) ^ 3 = 1} ∣ 3 := natCard_cubeRoots_dvd
  have h1 : Nat.card Unit = 1 := Nat.card_unique
  rw [Nat.card_congr (fourthFixedEquiv (K := K)), Nat.card_sum, h1]
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h <;> rw [h] <;> norm_num

omit [DecidableEq K] in

private theorem exists_root_quadratic [IsAlgClosed K] (c : K) : ∃ t : K, t ^ 2 + t = c := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : Polynomial K)
    (by
      have hdeg : (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : Polynomial K).degree = 2 := by
        compute_degree!
      rw [hdeg]
      decide)
  refine ⟨t, ?_⟩
  rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at ht
  linear_combination ht

omit [DecidableEq K] in

private theorem eq_or_eq_add_one_of_sq_add [CharP K 2] {c t₀ t : K} (h₀ : t₀ ^ 2 + t₀ = c)
    (h : t ^ 2 + t = c) : t = t₀ ∨ t = t₀ + 1 := by
  have h2 : (2 : K) = 0 := two_eq_zero''
  have hfac : (t - t₀) * (t - t₀ - 1) = 0 := by
    linear_combination h - h₀ + (t₀ ^ 2 + t₀ - t * t₀ - t) * h2
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (by linear_combination h')

omit [DecidableEq K] in
private theorem ne_add_one' (x : K) : x ≠ x + 1 := by
  intro h
  have : (1 : K) = 0 := by linear_combination -h
  exact one_ne_zero this

private noncomputable def root0 [IsAlgClosed K] (c : K) : K :=
  Classical.choose (exists_root_quadratic (K := K) c)

omit [DecidableEq K] in
private theorem root0_spec [IsAlgClosed K] (c : K) : root0 (K := K) c ^ 2 + root0 (K := K) c = c :=
  Classical.choose_spec (exists_root_quadratic (K := K) c)

private noncomputable def autModelTwoEquiv [CharP K 2] [IsAlgClosed K] :
    Aut (modelTwo K) ≃ ({u : Kˣ // ((u : K)) ^ 3 = 1} × {r : K // r ^ 4 = r}) × Bool where
  toFun γ :=
    ((⟨γ.1.u, ((smul_modelTwo_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)).1⟩,
      ⟨γ.1.r, by
        obtain ⟨-, hr, hs, -⟩ := (smul_modelTwo_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)
        calc γ.1.r ^ 4 = (γ.1.r ^ 2) ^ 2 := by ring
          _ = γ.1.r := by rw [← hs, ← hr]⟩),
      decide (γ.1.t = root0 (K := K) (γ.1.r ^ 3) + 1))
  invFun := fun ⟨⟨u, r⟩, b⟩ =>
    ⟨⟨u.1, r.1, r.1 ^ 2, if b then root0 (K := K) (r.1 ^ 3) + 1 else root0 (K := K) (r.1 ^ 3)⟩,
      MulAction.mem_stabilizer_iff.mpr ((smul_modelTwo_eq_iff _).mpr ⟨u.2, by
        show r.1 = (r.1 ^ 2) ^ 2
        calc r.1 = r.1 ^ 4 := r.2.symm
          _ = (r.1 ^ 2) ^ 2 := by ring, rfl, by
        have h2 : (2 : K) = 0 := two_eq_zero''
        have h0 := root0_spec (K := K) (r.1 ^ 3)
        cases b
        · show root0 (K := K) (r.1 ^ 3) ^ 2 + root0 (K := K) (r.1 ^ 3) = r.1 ^ 3
          exact h0
        · show (root0 (K := K) (r.1 ^ 3) + 1) ^ 2 + (root0 (K := K) (r.1 ^ 3) + 1) = r.1 ^ 3
          linear_combination h0 + (root0 (K := K) (r.1 ^ 3) + 1) * h2⟩)⟩
  left_inv γ := by
    obtain ⟨-, -, hs, ht⟩ := (smul_modelTwo_eq_iff γ.1).mp (smul_eq_of_mem_Aut γ)
    refine Subtype.ext (VariableChange.ext rfl rfl hs.symm ?_)
    show (if decide (γ.1.t = root0 (K := K) (γ.1.r ^ 3) + 1) = true then root0 (K := K) (γ.1.r ^ 3) + 1
        else root0 (K := K) (γ.1.r ^ 3)) = γ.1.t
    rcases eq_or_eq_add_one_of_sq_add (root0_spec (K := K) (γ.1.r ^ 3)) ht with h | h
    · have hb : decide (γ.1.t = root0 (K := K) (γ.1.r ^ 3) + 1) = false :=
        decide_eq_false (by rw [h]; exact ne_add_one' _)
      rw [hb]
      exact h.symm
    · have hb : decide (γ.1.t = root0 (K := K) (γ.1.r ^ 3) + 1) = true := decide_eq_true h
      rw [hb]
      exact h.symm
  right_inv := fun ⟨⟨u, r⟩, b⟩ => by
    refine Prod.ext (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)) ?_
    cases b
    · show decide (root0 (K := K) (r.1 ^ 3) = root0 (K := K) (r.1 ^ 3) + 1) = false
      exact decide_eq_false (ne_add_one' _)
    · show decide (root0 (K := K) (r.1 ^ 3) + 1 = root0 (K := K) (r.1 ^ 3) + 1) = true
      exact decide_eq_true rfl

private theorem natCard_aut_modelTwo_dvd [CharP K 2] [IsAlgClosed K] : Nat.card (Aut (modelTwo K)) ∣ 24 := by
  rw [Nat.card_congr (autModelTwoEquiv (K := K)), Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  have h : (24 : ℕ) = 3 * 4 * 2 := by norm_num
  rw [h]
  exact Nat.mul_dvd_mul (Nat.mul_dvd_mul natCard_cubeRoots_dvd natCard_fourthFixed_dvd) (dvd_refl 2)

omit [DecidableEq K] in
private theorem modelTwo_a₃_ne_zero : (modelTwo K).a₃ ≠ 0 := one_ne_zero

private theorem natCard_orbit_dvd_twelve [CharP K 2] [IsAlgClosed K] {N : ℕ} (H : CycSub (modelTwo K) N) :
    Nat.card (MulAction.orbit (Aut (modelTwo K)) H) ∣ 12 := by
  have hos : (MulAction.stabilizer (Aut (modelTwo K)) H).index *
      Nat.card (MulAction.stabilizer (Aut (modelTwo K)) H) = Nat.card (Aut (modelTwo K)) :=
    Subgroup.index_mul_card _
  have hidx : (MulAction.stabilizer (Aut (modelTwo K)) H).index =
      Nat.card (MulAction.orbit (Aut (modelTwo K)) H) := by
    rw [MulAction.index_stabilizer]; rfl
  have h2dvd : 2 ∣ Nat.card (MulAction.stabilizer (Aut (modelTwo K)) H) := by
    have := orderOf_dvd_natCard
      (⟨negAut (modelTwo K), negAut_mem_stabilizer H⟩ : MulAction.stabilizer (Aut (modelTwo K)) H)
    rwa [Subgroup.orderOf_mk, orderOf_negAut_of_a₃_ne_zero (modelTwo K) modelTwo_a₃_ne_zero] at this
  obtain ⟨c, hc⟩ := h2dvd
  rw [hidx, hc] at hos
  have h24 : Nat.card (MulAction.orbit (Aut (modelTwo K)) H) * 2 ∣ 12 * 2 := by
    refine dvd_trans ⟨c, ?_⟩ (natCard_aut_modelTwo_dvd (K := K))
    rw [← hos]; ring
  exact Nat.dvd_of_mul_dvd_mul_right two_pos h24

private theorem natCard_fibre_dvd_twelve [CharP K 2] [IsAlgClosed K] (N : ℕ) [NeZero N] {α : Type*}
    (f : CycSub (modelTwo K) N → α)
    (hf : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • modelTwo K = modelTwo K ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ (modelTwo K).toAffine T) T')
    (H : CycSub (modelTwo K) N) :
    Nat.card {H' : CycSub (modelTwo K) N // f H' = f H} ∣ 12 := by
  have e : {H' : CycSub (modelTwo K) N // f H' = f H} ≃ MulAction.orbit (Aut (modelTwo K)) H :=
    Equiv.subtypeEquivRight (fun H' => by
      rw [eq_comm, hf H H', rel_iff_mem_orbit H H']
      try rfl)
  rw [Nat.card_congr e]
  exact natCard_orbit_dvd_twelve H
end SupersingularWidthTwo
p2m_reactivate "P2MW.S_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces.SupersingularWidthTwo"

end
p2m_reactivate "P2MW.S_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces.SupersingularWidthTwo"

theorem solution
    {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K] [DecidableEq K]
    (h2N : ¬ 2 ∣ N)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces 2 N K) :
    placeRamificationJ N w ∣ jWidthChar 2 (w.evalAt (jGeomGen K N)) := by
  have hj : w.evalAt (jGeomGen K N) = 0 :=
    evalAt_jGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five (q' := 2) (by decide) hw
  rw [hj, jWidthChar_two_of_eq_zero rfl]
  have hN : (N : K) ≠ 0 := by
    intro h
    exact h2N ((CharP.cast_eq_zero_iff K 2 N).mp h)
  obtain ⟨α, f, hf, -, hidx⟩ := loc_R2_char2 (k := K) h2N hN
  obtain ⟨H, hH⟩ := hidx w hw
  rw [hH]
  exact SupersingularWidthTwo.natCard_fibre_dvd_twelve N f hf H

#print axioms solution

end S_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces (solution)
