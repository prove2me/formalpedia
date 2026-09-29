-- Prove2me | solution 1 for ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b61977f0-34b1-518f-bee8-5d9351bfc22c

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_symVec_mem_of_stable
import Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_AlgebraicCurve_sum_absLogHeight_roots_le_coeff
import Theorems.Thm_ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false
set_option Elab.async false

attribute [local instance] AlgebraicCurve.finiteDimensional_adjoin_range

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single Divisor.mem_degZero finiteDimensional_adjoin_range absLogHeight pointHt sum_absLogHeight_roots_le_coeff" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in

private theorem AlgebraicCurve.absLogHeight_eq_of_mem {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] (hx : ∀ i, x i ∈ L) :
    absLogHeight x
      = (Module.finrank ℚ L : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : L)) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (Set.range_subset_iff.mpr hx)
  have h3 := Height.inv_finrank_mul_logHeight_inclusion (L := L) hle
    (fun i => (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range x)))
  have htup : (fun i => IntermediateField.inclusion hle
      (⟨x i, IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range x))) = fun i => (⟨x i, hx i⟩ : L) := by
    funext i
    rfl
  unfold AlgebraicCurve.absLogHeight
  rw [← htup]
  exact h3.symm

namespace MWB1

p2m_open "ModularCurve P2MW.S_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight.ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight.AlgebraicCurve"

private theorem mwb1_absLogHeight_nonneg {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  unfold AlgebraicCurve.absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

private theorem mwb1_pointHt_nonneg {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) : 0 ≤ pointHt s v :=
  mwb1_absLogHeight_nonneg _

private theorem mwb1_absLogHeight_zero {ι : Type} [Fintype ι] :
    absLogHeight (0 : ι → AlgebraicClosure ℚ) = 0 := by
  unfold AlgebraicCurve.absLogHeight
  have h0 : (fun i => (⟨(0 : ι → AlgebraicClosure ℚ) i,
      IntermediateField.subset_adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)))) = 0 := by
    funext i
    exact Subtype.ext rfl
  rw [h0, Height.logHeight_zero, mul_zero]

private theorem mwb1_srh_abs {ι : Type*} (t : Finset ι) (α : ι → AlgebraicClosure ℚ)
    (m : ι → ℕ) {n : ℕ} (hdeg : ∑ i ∈ t, m i ≤ n) :
    ∑ i ∈ t, (m i : ℝ) * absLogHeight ![α i, 1]
      ≤ absLogHeight (fun k : Fin (n + 1) =>
          (∏ i ∈ t, (Polynomial.X - Polynomial.C (α i)) ^ m i).coeff k)
        + Real.log (Real.sqrt (n + 1)) :=
  AlgebraicCurve.sum_absLogHeight_roots_le_coeff t α m hdeg

private theorem mwb1_perpoint (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (_hs : IsEmbBasis N s) :
    ∃ Bs Cs : ℝ, 0 ≤ Bs ∧ 0 ≤ Cs ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) →
        pointHt s v ≤ Bs * absLogHeight ![jCoord N v, 1] + Cs :=
  ModularCurve.JZero.exists_pointHt_le_absLogHeight_jCoord N s _hs

open Real in

private theorem mwb1_absLogHeight_rev {n : ℕ} (x : Fin (n + 1) → AlgebraicClosure ℚ) :
    absLogHeight (fun k : Fin (n + 1) => x (Fin.rev k)) = absLogHeight x := by
  classical
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
    AlgebraicCurve.finiteDimensional_adjoin_range x
  have hx : ∀ k, x k ∈ IntermediateField.adjoin ℚ (Set.range x) := fun k =>
    IntermediateField.subset_adjoin ℚ (Set.range x) ⟨k, rfl⟩
  have hxrev : ∀ k : Fin (n + 1), x (Fin.rev k) ∈ IntermediateField.adjoin ℚ (Set.range x) :=
    fun k => hx (Fin.rev k)
  rw [AlgebraicCurve.absLogHeight_eq_of_mem _ _ hxrev,
    AlgebraicCurve.absLogHeight_eq_of_mem _ _ hx]
  congr 1
  rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight]
  congr 1
  exact Height.mulHeight_comp_equiv Fin.revPerm
    (fun k => (⟨x k, hx k⟩ : IntermediateField.adjoin ℚ (Set.range x)))

private theorem mwb1_cusp_bound (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) < 0 →
        pointHt s v ≤ Cc := by
  classical
  obtain ⟨-, -, hfin⟩ := ModularCurve.jCoordinate_spec_modularFunctionFieldBar N
  refine ⟨hfin.toFinset.sum fun v => pointHt s v,
    Finset.sum_nonneg fun v _ => mwb1_pointHt_nonneg s v, fun v hv => ?_⟩
  exact Finset.single_le_sum (f := fun w => pointHt s w)
    (fun w _ => mwb1_pointHt_nonneg s w) (hfin.mem_toFinset.mpr hv)

open Real in

private theorem mwb1_absLogHeight_symVec_le (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (g' : ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hmem : ∀ k, symVec N g' D k ∈ K) :
    absLogHeight (symVec N g' D) ≤ divNaiveHeight N K g' D := by
  classical
  unfold ModularCurve.divNaiveHeight
  rw [dif_pos hmem]
  rw [AlgebraicCurve.absLogHeight_eq_of_mem (symVec N g' D) K hmem]
  have hlog0 : (0 : ℝ) ≤ Height.logHeight fun k => (⟨symVec N g' D k, hmem k⟩ : K) :=
    Height.logHeight_nonneg _
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hinv : (Module.finrank ℚ K : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact hd1
  nlinarith

private theorem mwb1_symPoly_eq_filter (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    symPoly N D = ∏ v ∈ D.support.filter (fun v => 0 ≤ v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
      (Polynomial.X - Polynomial.C (jCoord N v)) ^ (D v).toNat := by
  classical
  rw [ModularCurve.symPoly, Finsupp.prod]
  rw [← Finset.prod_filter_mul_prod_filter_not D.support (fun v => 0 ≤ v.ord
    (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N))]
  have h2 : (∏ v ∈ D.support.filter (fun v => ¬ (0 ≤ v.ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N))),
      jFactor N v ^ (D v).toNat) = 1 := by
    refine Finset.prod_eq_one fun v hv => ?_
    rw [ModularCurve.jFactor_of_neg (not_le.mp (Finset.mem_filter.mp hv).2), one_pow]
  rw [h2, mul_one]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [ModularCurve.jFactor_of_nonneg (Finset.mem_filter.mp hv).2]

end MWB1

namespace ModularCurve p2m_export "ModularCurve" "jCoord jFactor symPoly symVec divNaiveHeight jFactor_of_nonneg jFactor_of_neg cuspInftyBar jq_mem_full jq modularFunctionFieldBar JZero coeffEmb coeffEmb_mem_laurentBaseChange IsEmbBasis JZero.IsRepOf deg_eq_one_modularFunctionFieldBar symVec_mem_of_stable jCoordinate_spec_modularFunctionFieldBar JZero.exists_pointHt_le_absLogHeight_jCoord" namespace JZero p2m_export "ModularCurve.JZero" "IsRepOf exists_pointHt_le_absLogHeight_jCoord" end ModularCurve.JZero
p2m_open_scoped "ModularCurve ModularCurve.JZero" in
open _root_.ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight.AlgebraicCurve in

private theorem ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∃ C₁ : ℝ,
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        JZero.IsRepOf N K n c D →
        ((D.erase (cuspInftyBar N)).sum fun v m => (m : ℝ) * pointHt s v)
          ≤ B * divNaiveHeight N K n D + C₁ := by
  classical
  obtain ⟨Bs, Cs, hBs0, hCs0, hper⟩ := MWB1.mwb1_perpoint N s hs
  obtain ⟨Cc, hCc0, hcusp⟩ := MWB1.mwb1_cusp_bound N s
  refine ⟨Bs, hBs0, fun n => ?_⟩
  refine ⟨Bs * Real.log (Real.sqrt (n + 1)) + (Cs + Cc) * n, fun c D hD => ?_⟩
  obtain ⟨EE, heff, hshape, hstab, hc⟩ := hD
  have hdeg1 := ModularCurve.deg_eq_one_modularFunctionFieldBar N
  have hdegD : Divisor.degree (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) D
      = n := by
    rw [← hshape, map_add, Divisor.mem_degZero.mp EE.2, zero_add, map_zsmul,
      Divisor.degree_single, hdeg1]
    simp
  have hsumZ : (D.sum fun _ m => m) = (n : ℤ) := by
    have hunfold : Divisor.degree (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar N)) D = D.sum fun v m => m * v.deg := by
      simp [Divisor.degree, Finsupp.liftAddHom_apply]
    have hcongr : (D.sum fun v m => m * v.deg) = D.sum fun _ m => m := by
      refine Finsupp.sum_congr fun v _ => ?_
      rw [hdeg1, Nat.cast_one, mul_one]
    rw [← hcongr, ← hunfold, hdegD]
  have htoNat : (∑ v ∈ D.support, (D v).toNat) = n := by
    have h1 : ((∑ v ∈ D.support, (D v).toNat : ℕ) : ℤ) = (n : ℤ) := by
      push_cast
      calc (∑ v ∈ D.support, ((D v).toNat : ℤ))
          = ∑ v ∈ D.support, D v := by
            refine Finset.sum_congr rfl fun v _ => ?_
            exact Int.toNat_of_nonneg (heff v)
        _ = (n : ℤ) := hsumZ
    exact_mod_cast h1
  have hDsumR : (∑ v ∈ D.support, ((D v) : ℝ)) = n := by
    have h2 : (∑ v ∈ D.support, ((D v) : ℝ)) = ((∑ v ∈ D.support, (D v).toNat : ℕ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun v _ => ?_
      exact_mod_cast (Int.toNat_of_nonneg (heff v)).symm
    rw [h2, htoNat]
  have herase_le : ∀ v, ((D.erase (cuspInftyBar N)) v : ℝ) ≤ (D v : ℝ) := by
    intro v
    rw [Finsupp.erase_apply]
    split_ifs
    · exact_mod_cast heff v
    · exact le_rfl
  have hEnn : ∀ v, (0 : ℝ) ≤ ((D.erase (cuspInftyBar N)) v : ℝ) := by
    intro v
    rw [Finsupp.erase_apply]
    split_ifs
    · simp
    · exact_mod_cast heff v
  have hE'sub : (D.erase (cuspInftyBar N)).support ⊆ D.support := by
    rw [Finsupp.support_erase]
    exact Finset.erase_subset _ _
  have hsub_le : ∀ t : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      t ⊆ D.support → (∑ v ∈ t, ((D.erase (cuspInftyBar N)) v : ℝ)) ≤ n := by
    intro t ht
    calc (∑ v ∈ t, ((D.erase (cuspInftyBar N)) v : ℝ))
        ≤ ∑ v ∈ t, ((D v) : ℝ) := Finset.sum_le_sum fun v _ => herase_le v
      _ ≤ ∑ v ∈ D.support, ((D v) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg ht fun v _ _ => by exact_mod_cast heff v
      _ = n := hDsumR
  have hsplit : ((D.erase (cuspInftyBar N)).sum fun v m => (m : ℝ) * pointHt s v)
      = (∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => 0 ≤ v.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
          ((D.erase (cuspInftyBar N)) v : ℝ) * pointHt s v)
        + ∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => ¬ (0 ≤ v.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N))),
          ((D.erase (cuspInftyBar N)) v : ℝ) * pointHt s v := by
    rw [Finsupp.sum, Finset.sum_filter_add_sum_filter_not]
  have hcuspsum : (∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => ¬ (0 ≤ v.ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N))),
      ((D.erase (cuspInftyBar N)) v : ℝ) * pointHt s v) ≤ Cc * n := by
    have hle : ∀ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => ¬ (0 ≤ v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N))),
        ((D.erase (cuspInftyBar N)) v : ℝ) * pointHt s v
          ≤ Cc * ((D.erase (cuspInftyBar N)) v : ℝ) := by
      intro v hv
      rw [mul_comm Cc]
      exact mul_le_mul_of_nonneg_left
        (hcusp v (not_le.mp (Finset.mem_filter.mp hv).2)) (hEnn v)
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (hsub_le _ ((Finset.filter_subset _ _).trans hE'sub)) hCc0
  have hnoncusp : (∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => 0 ≤ v.ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
      ((D.erase (cuspInftyBar N)) v : ℝ) * pointHt s v)
      ≤ Bs * (∑ v ∈ D.support.filter (fun v => 0 ≤ v.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
          (((D v).toNat : ℕ) : ℝ) * absLogHeight ![jCoord N v, 1]) + Cs * n := by
    have hstep1 : ∀ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => 0 ≤ v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
        ((D.erase (cuspInftyBar N)) v : ℝ) * pointHt s v
          ≤ ((D.erase (cuspInftyBar N)) v : ℝ) *
              (Bs * absLogHeight ![jCoord N v, 1] + Cs) := fun v hv =>
      mul_le_mul_of_nonneg_left (hper v (Finset.mem_filter.mp hv).2) (hEnn v)
    refine (Finset.sum_le_sum hstep1).trans ?_
    have hexpand : (∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => 0 ≤ v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
        ((D.erase (cuspInftyBar N)) v : ℝ) * (Bs * absLogHeight ![jCoord N v, 1] + Cs))
        = Bs * (∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => 0 ≤ v.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
            ((D.erase (cuspInftyBar N)) v : ℝ) * absLogHeight ![jCoord N v, 1])
          + Cs * ∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => 0 ≤ v.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
            ((D.erase (cuspInftyBar N)) v : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    rw [hexpand]
    refine add_le_add ?_ (mul_le_mul_of_nonneg_left
      (hsub_le _ ((Finset.filter_subset _ _).trans hE'sub)) hCs0)
    refine mul_le_mul_of_nonneg_left ?_ hBs0
    calc (∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => 0 ≤ v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
        ((D.erase (cuspInftyBar N)) v : ℝ) * absLogHeight ![jCoord N v, 1])
        ≤ ∑ v ∈ (D.erase (cuspInftyBar N)).support.filter (fun v => 0 ≤ v.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
            ((D v) : ℝ) * absLogHeight ![jCoord N v, 1] :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (herase_le v)
            (MWB1.mwb1_absLogHeight_nonneg _)
      _ ≤ ∑ v ∈ D.support.filter (fun v => 0 ≤ v.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
            ((D v) : ℝ) * absLogHeight ![jCoord N v, 1] :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset_filter _ hE'sub) fun v _ _ =>
            mul_nonneg (by exact_mod_cast heff v) (MWB1.mwb1_absLogHeight_nonneg _)
      _ = ∑ v ∈ D.support.filter (fun v => 0 ≤ v.ord
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
            (((D v).toNat : ℕ) : ℝ) * absLogHeight ![jCoord N v, 1] := by
          refine Finset.sum_congr rfl fun v _ => ?_
          congr 1
          have h := Int.toNat_of_nonneg (heff v)
          exact_mod_cast h.symm
  have hsrh : (∑ v ∈ D.support.filter (fun v => 0 ≤ v.ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
      (((D v).toNat : ℕ) : ℝ) * absLogHeight ![jCoord N v, 1])
      ≤ divNaiveHeight N K n D + Real.log (Real.sqrt (n + 1)) := by
    have hdeg' : (∑ v ∈ D.support.filter (fun v => 0 ≤ v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)), (D v).toNat) ≤ n := by
      calc (∑ v ∈ D.support.filter (fun v => 0 ≤ v.ord
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)), (D v).toNat)
          ≤ ∑ v ∈ D.support, (D v).toNat :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = n := htoNat
    have h1 := MWB1.mwb1_srh_abs (D.support.filter (fun v => 0 ≤ v.ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N))) (jCoord N) (fun v => (D v).toNat) hdeg'
    rw [show (∏ v ∈ D.support.filter (fun v => 0 ≤ v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)),
        (Polynomial.X - Polynomial.C (jCoord N v)) ^ (D v).toNat) = symPoly N D
      from (MWB1.mwb1_symPoly_eq_filter N D).symm] at h1
    have h3 : absLogHeight (fun k : Fin (n + 1) => (symPoly N D).coeff k)
        = absLogHeight (symVec N n D) := by
      rw [← MWB1.mwb1_absLogHeight_rev (fun k : Fin (n + 1) => (symPoly N D).coeff k)]
      congr 1
      funext k
      show (symPoly N D).coeff ((Fin.rev k : Fin (n + 1)) : ℕ) = (symPoly N D).coeff (n - k)
      congr 1
      rw [Fin.val_rev]
      omega
    rw [h3] at h1
    have hmem : ∀ k, symVec N n D k ∈ K := fun k =>
      ModularCurve.symVec_mem_of_stable N K n D hstab k
    have h4 := MWB1.mwb1_absLogHeight_symVec_le N K n D hmem
    linarith
  rw [hsplit]
  have hBsrh := mul_le_mul_of_nonneg_left hsrh hBs0
  have hring : Bs * (divNaiveHeight N K n D + Real.log (Real.sqrt (n + 1)))
      = Bs * divNaiveHeight N K n D + Bs * Real.log (Real.sqrt (n + 1)) := by ring
  linarith

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight.ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight.AlgebraicCurve in
theorem solution (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∃ C₁ : ℝ,
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        JZero.IsRepOf N K n c D →
        ((D.erase (cuspInftyBar N)).sum fun v m => (m : ℝ) * pointHt s v)
          ≤ B * divNaiveHeight N K n D + C₁ :=
  ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight N K s hs

end S_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight
end P2MW
export P2MW.S_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight (solution)
