-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.mem_range_redRestrict_of_hasValue_nodeResidueFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7216927f-ab6d-505d-80ee-9d1c2a99476c

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_arithFrobC_pow_smul_residueFst_eq_of_isFrobeniusAt_of_coe_mem_fieldOver
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open scoped Pointwise

namespace PressDescent

theorem two_dvd_of_sq_sub_one_dvd_pow_sub_one {q d : ℕ} (hq : 2 ≤ q) (h : (q ^ 2 - 1) ∣ (q ^ d - 1)) : 2 ∣ d := by
  by_contra hodd
  have hd : d = 2 * (d / 2) + 1 := by omega
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hmod : q ^ 2 ≡ 1 [MOD q ^ 2 - 1] := by
    have : q ^ 2 = (q ^ 2 - 1) + 1 := by omega
    conv_lhs => rw [this]
    exact Nat.add_modEq_left
  have hqd : q ^ d ≡ q [MOD q ^ 2 - 1] := by
    have h1 : (q ^ 2) ^ (d / 2) * q ≡ 1 ^ (d / 2) * q [MOD q ^ 2 - 1] := (hmod.pow _).mul_right _
    rw [one_pow, one_mul, ← pow_mul] at h1
    have : q ^ d = q ^ (2 * (d / 2)) * q := by
      conv_lhs => rw [hd]
      rw [pow_succ]
    rwa [this]
  have h1d : 1 ≡ q ^ d [MOD q ^ 2 - 1] := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mpr h
  have hq1 : 1 ≡ q [MOD q ^ 2 - 1] := h1d.trans hqd
  have hdvd : (q ^ 2 - 1) ∣ (q - 1) := (Nat.modEq_iff_dvd' (by omega)).mp hq1
  have hle : q ^ 2 - 1 ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
  have : q * q ≥ 2 * q := Nat.mul_le_mul_right q hq
  rw [pow_two] at hle
  omega

end PressDescent

open PressDescent in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (g : ↥(R.nodeIntegersOver K w)) (a : k)
    (ha : w.HasValue (R.nodeResidue₁ w ⟨g, g.2.1⟩ : ↥(modularFunctionFieldC k N)) a) :
    a ∈ Set.range (NodeLocalized.redRestrict red K) := by
  classical
  have hqF : q.Prime := Fact.out

  have hmemq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hAq : A.LiesOverPrime q := by
    show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
    rw [ValuationSubring.mem_nonunits_iff]
    rcases ((A.valuation_le_one_iff _).mpr hmemq).lt_or_eq with h | h
    · exact h
    · exfalso
      have hu : IsUnit ((⟨((q : ℕ) : AlgebraicClosure ℚ), hmemq⟩ : ↥A)) := (A.valuation_eq_one_iff _).mpr h
      have h2 := hu.map red
      have h3 : red ⟨((q : ℕ) : AlgebraicClosure ℚ), hmemq⟩ = ((q : ℕ) : k) := by
        rw [← map_natCast red q]
        congr 1
      rw [h3, CharP.cast_eq_zero k q] at h2
      exact not_isUnit_zero h2

  obtain ⟨d, σ, hd, hcard, hσK, hσA⟩ :=
    ValuationSubring.exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime q A hAq K

  have hk₀pow : ∀ c : ↥(NodeLocalized.coeffSubring A K),
      (NodeLocalized.redRestrict red K c) ^ (q ^ d) = NodeLocalized.redRestrict red K c := by
    intro c
    have hres := hσA.smul_residue_eq (IsLocalRing.residue ↥A ⟨(c : AlgebraicClosure ℚ), c.2.1⟩)
    rw [← IsLocalRing.ResidueField.residue_smul] at hres
    have hgx : ((⟨σ, hσA.mem_decompositionSubgroup⟩ : ↥(A.decompositionSubgroup ℚ)) •
        (⟨(c : AlgebraicClosure ℚ), c.2.1⟩ : ↥A)) = ⟨(c : AlgebraicClosure ℚ), c.2.1⟩ :=
      Subtype.ext (hσK _ c.2.2)
    rw [hgx] at hres
    have h := congrArg R.redBar hres
    rw [map_pow, R.redBar_residue] at h
    exact h.symm

  have hk₀card : Nat.card (Set.range (NodeLocalized.redRestrict red K)) = q ^ d := by
    have himg : Set.range (NodeLocalized.redRestrict red K) =
        R.redBar '' (Set.range fun a : {a : ↥A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue ↥A a.1) := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨_, ⟨⟨⟨(c : AlgebraicClosure ℚ), c.2.1⟩, c.2.2⟩, rfl⟩, by rw [R.redBar_residue]; rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨⟨(a.1 : AlgebraicClosure ℚ), a.1.2, a.2⟩, by rw [R.redBar_residue]; rfl⟩
    rw [himg, Nat.card_image_of_injective R.redBar.injective, hcard]
  have hk₀fin : (Set.range (NodeLocalized.redRestrict red K)).Finite :=
    Nat.finite_of_card_ne_zero (by rw [hk₀card]; exact pow_ne_zero _ hqF.ne_zero)

  have hqd1 : 1 < q ^ d := Nat.one_lt_pow hd.ne' hqF.one_lt
  have hmemk₀ : ∀ x : k, x ^ (q ^ d) = x → x ∈ Set.range (NodeLocalized.redRestrict red K) := by
    intro x hx
    have hne : (Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hqd1
    have hmemR : ∀ y : k, y ∈ (Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k).roots.toFinset ↔ y ^ (q ^ d) = y := by
      intro y
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero]
    have hTsub : hk₀fin.toFinset ⊆ (Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k).roots.toFinset := by
      intro y hy
      rw [Set.Finite.mem_toFinset] at hy
      obtain ⟨c, rfl⟩ := hy
      exact (hmemR _).mpr (hk₀pow c)
    have hTcard : hk₀fin.toFinset.card = q ^ d := by
      rw [← hk₀card, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hk₀fin]
    have hRcard : (Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k).roots.toFinset.card ≤ q ^ d := by
      refine (Multiset.toFinset_card_le _).trans ?_
      refine (Polynomial.card_roots' _).trans ?_
      rw [FiniteField.X_pow_card_sub_X_natDegree_eq k hqd1]
    have hTeq := Finset.eq_of_subset_of_card_le hTsub (by rw [hTcard]; exact hRcard)
    have hxR : x ∈ (Polynomial.X ^ (q ^ d) - Polynomial.X : Polynomial k).roots.toFinset := (hmemR x).mpr hx
    rw [← hTeq, Set.Finite.mem_toFinset] at hxR
    exact hxR

  have h2d : 2 ∣ d := by
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hqF.pos
    have hn : q ^ 2 - 1 ≠ 0 := by
      have : 4 ≤ q ^ 2 := by have := hqF.two_le; nlinarith
      omega
    haveI : NeZero ((q ^ 2 - 1 : ℕ) : k) := ⟨by
      rw [Nat.cast_sub hq2, Nat.cast_pow, CharP.cast_eq_zero k q, zero_pow two_ne_zero, zero_sub, Nat.cast_one]
      exact neg_ne_zero.mpr one_ne_zero⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ : k, IsPrimitiveRoot ζ (q ^ 2 - 1) := by
      obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (q ^ 2 - 1) k)
        (Polynomial.degree_cyclotomic_pos (q ^ 2 - 1) k (Nat.pos_of_ne_zero hn)).ne'
      exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩
    have hζq2 : ζ ^ (q ^ 2) = ζ := by
      have : q ^ 2 = (q ^ 2 - 1) + 1 := by omega
      rw [this, pow_succ, hζ.pow_eq_one, one_mul]
    obtain ⟨c, hc⟩ := hk₀ ζ hζq2
    have hζqd : ζ ^ (q ^ d) = ζ := by rw [← hc]; exact hk₀pow c
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hn
    have hdvd : (q ^ 2 - 1) ∣ (q ^ d - 1) := by
      apply hζ.dvd_of_pow_eq_one
      have h1 : ζ ^ (q ^ d - 1) * ζ = 1 * ζ := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hqF.pos), one_mul]
        exact hζqd
      exact mul_right_cancel₀ hζ0 h1
    exact two_dvd_of_sq_sub_one_dvd_pow_sub_one hqF.two_le hdvd
  obtain ⟨m, hm⟩ := h2d

  have hφw : (arithFrobC q k N) ^ d • w = w := by
    have h2 : (arithFrobC q k N) ^ 2 • w = w := by
      rw [pow_two, mul_smul]
      exact arithFrobC_smul_arithFrobC_smul_eq_self_of_mem_ssPlaces q N hqN k w hw
    rw [hm, pow_mul]
    clear hm
    induction m with
    | zero => rw [pow_zero, one_smul]
    | succ m ih => rw [pow_succ, mul_smul, h2, ih]

  have hφg := arithFrobC_pow_smul_residueFst_eq_of_isFrobeniusAt_of_coe_mem_fieldOver R K σ hσK d hσA
    (g : ↥(modularFunctionFieldBar (N * q))) g.2.1.1 g.2.2

  have hval : w.HasValue (R.residue₁ ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.1⟩ : ↥(modularFunctionFieldC k N)) a := ha
  have ht := Place.HasValue.smul ((arithFrobC q k N) ^ d) hval
  rw [hφw, hφg] at ht
  have hbase : SemilinearAut.baseAut ((arithFrobC q k N) ^ d) a = a ^ (q ^ d) := by
    show (((arithFrobC q k N) ^ d).val.2) a = a ^ (q ^ d)
    rw [Subgroup.coe_pow, Prod.pow_snd]
    show ((frobeniusEquiv k q : k ≃+* k) ^ d) a = a ^ (q ^ d)
    rw [RingAut.coe_pow, ← iterate_frobenius]
    rfl
  rw [hbase] at ht
  exact hmemk₀ a (hval.unique ht).symm

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst (solution)
