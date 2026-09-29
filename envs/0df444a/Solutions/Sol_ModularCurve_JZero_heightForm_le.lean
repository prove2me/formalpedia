-- Prove2me | solution 1 for ModularCurve.JZero.heightForm_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/fb160d4b-a20d-5603-b076-d5f7e72ba2c2

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_heightForm_le
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false
set_option Elab.async false

attribute [local instance] AlgebraicCurve.finiteDimensional_adjoin_range

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single Divisor.mem_degZero finiteDimensional_adjoin_range absLogHeight evalVec chordVec pointHt pairHt baseHt heightFormAux heightForm genusFF" end AlgebraicCurve
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

p2m_open "ModularCurve P2MW.S_ModularCurve_JZero_heightForm_le.ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JZero_heightForm_le.AlgebraicCurve"

private noncomputable def mwb1Minor (M : Type*) [Field M] (r : ℕ) :
    Fin r × Fin r → MvPolynomial (Fin r × Fin r) M :=
  fun a => MvPolynomial.X (a.1, a.2) - MvPolynomial.X (a.2, a.1)

private theorem mwb1Minor_apply {M : Type*} [Field M] {r : ℕ} (a : Fin r × Fin r) :
    mwb1Minor M r a = MvPolynomial.X (a.1, a.2) - MvPolynomial.X (a.2, a.1) := rfl

private theorem mwb1Minor_coeff_le {M : Type*} [Field M] {r : ℕ}
    (v : AbsoluteValue M ℝ) (a : Fin r × Fin r) (e : (Fin r × Fin r) →₀ ℕ) :
    v (MvPolynomial.coeff e (mwb1Minor M r a)) ≤ 1 := by
  unfold mwb1Minor
  simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_X']
  split_ifs <;> simp [v.map_one]

private theorem mwb1Minor_support_card {M : Type*} [Field M] {r : ℕ} (a : Fin r × Fin r) :
    (mwb1Minor M r a).support.card ≤ 2 := by
  have hsub : (mwb1Minor M r a).support ⊆
      {Finsupp.single ((a.1 : Fin r), (a.2 : Fin r)) 1,
        Finsupp.single ((a.2 : Fin r), (a.1 : Fin r)) 1} := by
    unfold mwb1Minor
    refine Finset.Subset.trans (MvPolynomial.support_sub ..) ?_
    refine Finset.union_subset ?_ ?_ <;>
      simp [MvPolynomial.support_X, Finset.singleton_subset_iff]
  have h2 : ({Finsupp.single ((a.1 : Fin r), (a.2 : Fin r)) 1,
      Finsupp.single ((a.2 : Fin r), (a.1 : Fin r)) 1} :
      Finset ((Fin r × Fin r) →₀ ℕ)).card ≤ 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    simp
  exact (Finset.card_le_card hsub).trans h2

private theorem mwb1Minor_sum_le {M : Type*} [Field M] {r : ℕ}
    (v : AbsoluteValue M ℝ) (a : Fin r × Fin r) :
    ((AddMonoidAlgebra.coeff (mwb1Minor M r a)).sum fun _ c => v c) ≤ 2 := by
  calc ((AddMonoidAlgebra.coeff (mwb1Minor M r a)).sum fun _ c => v c)
      ≤ ∑ _e ∈ (mwb1Minor M r a).support, (1 : ℝ) :=
        Finset.sum_le_sum fun e _ => mwb1Minor_coeff_le v a e
    _ = ((mwb1Minor M r a).support.card : ℝ) := by simp [MvPolynomial.support]
    _ ≤ 2 := by exact_mod_cast mwb1Minor_support_card a

private theorem mwb1_prod_map_le_pow {ι : Type*} (s : Multiset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h2 : ∀ i ∈ s, f i ≤ 2) :
    (s.map f).prod ≤ 2 ^ Multiset.card s := by
  revert h0 h2
  induction s using Multiset.induction_on with
  | empty => intro _ _; simp
  | cons a t ih =>
    intro h0 h2
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    have ht0 : ∀ i ∈ t, 0 ≤ f i := fun i hi => h0 i (Multiset.mem_cons_of_mem hi)
    have ht2 : ∀ i ∈ t, f i ≤ 2 := fun i hi => h2 i (Multiset.mem_cons_of_mem hi)
    have hprod0 : 0 ≤ (t.map f).prod := by
      refine Multiset.prod_nonneg fun x hx => ?_
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
      exact ht0 i hi
    calc f a * (t.map f).prod
        ≤ 2 * 2 ^ Multiset.card t :=
          mul_le_mul (h2 a (Multiset.mem_cons_self a t)) (ih ht0 ht2) hprod0 (by norm_num)
      _ = 2 ^ (Multiset.card t + 1) := by ring

open Real Height _root_.Height.AdmissibleAbsValues in

private theorem mwb1_minor_bound_le {M : Type*} [Field M] [Height.AdmissibleAbsValues M]
    {r : ℕ} [Nonempty (Fin r × Fin r)] :
    Real.log (max (Height.mulHeightBound (mwb1Minor M r)) 1)
      ≤ (Height.totalWeight M : ℝ) * Real.log 2 := by
  classical
  have hbound : Height.mulHeightBound (mwb1Minor M r) ≤ 2 ^ Height.totalWeight M := by
    rw [Height.mulHeightBound_eq]
    have hnon : (∏ᶠ v : nonarchAbsVal (K := M),
        ⨆ j, max (⨆ s : (mwb1Minor M r j).support,
          v.val (MvPolynomial.coeff s (mwb1Minor M r j))) 1) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      refine le_antisymm (ciSup_le fun j => ?_) ?_
      · refine max_le ?_ le_rfl
        exact Real.iSup_le (fun s => mwb1Minor_coeff_le v.val j s) zero_le_one
      · exact le_ciSup_of_le (Set.Finite.bddAbove (Set.finite_range _))
          (Classical.arbitrary _) (le_max_right _ 1)
    rw [hnon, mul_one]
    have harch : ((archAbsVal (K := M)).map
          fun v => ⨆ j, (AddMonoidAlgebra.coeff (mwb1Minor M r j)).sum fun _ c => v c).prod
        ≤ 2 ^ Multiset.card (archAbsVal (K := M)) := by
      refine mwb1_prod_map_le_pow _ _ (fun v _ => ?_) (fun v _ => ?_)
      · exact Real.iSup_nonneg fun j => Finsupp.sum_nonneg' fun _ => v.nonneg _
      · exact Real.iSup_le (fun j => mwb1Minor_sum_le v j) (by norm_num)
    refine harch.trans_eq ?_
    simp only [Height.totalWeight]
  have hmax : max (Height.mulHeightBound (mwb1Minor M r)) 1 ≤ 2 ^ Height.totalWeight M :=
    max_le hbound (one_le_pow₀ (by norm_num))
  calc Real.log (max (Height.mulHeightBound (mwb1Minor M r)) 1)
      ≤ Real.log (2 ^ Height.totalWeight M) :=
        Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_right _ 1)) hmax
    _ = (Height.totalWeight M : ℝ) * Real.log 2 := by rw [Real.log_pow]

private theorem mwb1_absLogHeight_nonneg {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  unfold AlgebraicCurve.absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

private theorem mwb1_pointHt_nonneg {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) : 0 ≤ pointHt s v :=
  mwb1_absLogHeight_nonneg _

private theorem mwb1_pairHt_le {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    pairHt s v w ≤ pointHt s v + pointHt s w := by
  unfold AlgebraicCurve.pairHt
  have := mwb1_absLogHeight_nonneg (chordVec s v w)
  linarith

private theorem mwb1_baseHt_le {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) (b v : Place (AlgebraicClosure ℚ) F) :
    baseHt s b v ≤ pointHt s v + pointHt s b := by
  unfold AlgebraicCurve.baseHt
  split_ifs with h
  · exact add_nonneg (mwb1_pointHt_nonneg s v) (mwb1_pointHt_nonneg s b)
  · exact mwb1_pairHt_le s v b

private theorem mwb1_absLogHeight_zero {ι : Type} [Fintype ι] :
    absLogHeight (0 : ι → AlgebraicClosure ℚ) = 0 := by
  unfold AlgebraicCurve.absLogHeight
  have h0 : (fun i => (⟨(0 : ι → AlgebraicClosure ℚ) i,
      IntermediateField.subset_adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)))) = 0 := by
    funext i
    exact Subtype.ext rfl
  rw [h0, Height.logHeight_zero, mul_zero]

open Real in

private theorem mwb1_chord_le {r : ℕ} (x y : Fin r → AlgebraicClosure ℚ) :
    absLogHeight (fun p : Fin r × Fin r => x p.1 * y p.2 - x p.2 * y p.1)
      ≤ absLogHeight x + absLogHeight y + Real.log 2 := by
  classical
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hx : x = 0
  · have hc : (fun p : Fin r × Fin r => x p.1 * y p.2 - x p.2 * y p.1) = 0 := by
      funext p
      simp [hx]
    rw [hc, mwb1_absLogHeight_zero, hx, mwb1_absLogHeight_zero]
    have := mwb1_absLogHeight_nonneg y
    linarith
  by_cases hy : y = 0
  · have hc : (fun p : Fin r × Fin r => x p.1 * y p.2 - x p.2 * y p.1) = 0 := by
      funext p
      simp [hy]
    rw [hc, mwb1_absLogHeight_zero, hy, mwb1_absLogHeight_zero]
    have := mwb1_absLogHeight_nonneg x
    linarith

  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · exact absurd (funext fun i => absurd i.2 (by omega)) hx
    · exact hr0
  haveI : Nonempty (Fin r × Fin r) := ⟨(⟨0, hr⟩, ⟨0, hr⟩)⟩

  set S : Set (AlgebraicClosure ℚ) := Set.range x ∪ Set.range y with hS
  haveI hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  set M := IntermediateField.adjoin ℚ S with hM
  have hmem_x : ∀ i, x i ∈ M := fun i =>
    IntermediateField.subset_adjoin ℚ S (Or.inl ⟨i, rfl⟩)
  have hmem_y : ∀ i, y i ∈ M := fun i =>
    IntermediateField.subset_adjoin ℚ S (Or.inr ⟨i, rfl⟩)
  have hmem_c : ∀ p : Fin r × Fin r, x p.1 * y p.2 - x p.2 * y p.1 ∈ M := fun p =>
    sub_mem (mul_mem (hmem_x p.1) (hmem_y p.2)) (mul_mem (hmem_x p.2) (hmem_y p.1))
  rw [AlgebraicCurve.absLogHeight_eq_of_mem _ M hmem_c,
    AlgebraicCurve.absLogHeight_eq_of_mem x M hmem_x,
    AlgebraicCurve.absLogHeight_eq_of_mem y M hmem_y]
  set x' : Fin r → M := fun i => ⟨x i, hmem_x i⟩ with hx'def
  set y' : Fin r → M := fun i => ⟨y i, hmem_y i⟩ with hy'def
  have hx' : x' ≠ 0 := fun h =>
    hx (funext fun i => Subtype.ext_iff.mp (congrFun h i))
  have hy' : y' ≠ 0 := fun h =>
    hy (funext fun i => Subtype.ext_iff.mp (congrFun h i))

  have hc' : (fun p : Fin r × Fin r => (⟨x p.1 * y p.2 - x p.2 * y p.1, hmem_c p⟩ : M))
      = fun p => (mwb1Minor M r p).eval fun a : Fin r × Fin r => x' a.1 * y' a.2 := by
    funext p
    apply Subtype.ext
    rw [mwb1Minor_apply]
    push_cast [MvPolynomial.eval_sub, MvPolynomial.eval_X]
    rfl
  rw [hc']

  have homog : ∀ a : Fin r × Fin r, (mwb1Minor M r a).IsHomogeneous 1 := fun a => by
    rw [mwb1Minor_apply]
    exact (MvPolynomial.isHomogeneous_X ..).sub (MvPolynomial.isHomogeneous_X ..)

  have h1 := Height.logHeight_eval_le (K := M) homog
    (fun a : Fin r × Fin r => x' a.1 * y' a.2)

  have h2 : Height.logHeight (fun a : Fin r × Fin r => x' a.1 * y' a.2)
      = Height.logHeight x' + Height.logHeight y' := by
    rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight,
      Height.logHeight_eq_log_mulHeight, Height.mulHeight_fun_mul_eq hx' hy',
      Real.log_mul (Height.mulHeight_pos x').ne' (Height.mulHeight_pos y').ne']

  have h3 := mwb1_minor_bound_le (M := M) (r := r)
  rw [NumberField.totalWeight_eq_finrank] at h3

  have hd : (0 : ℝ) < (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hd0 : (0 : ℝ) ≤ (Module.finrank ℚ M : ℝ)⁻¹ := inv_nonneg.mpr hd.le
  have hcomb : Height.logHeight (fun p : Fin r × Fin r =>
        (mwb1Minor M r p).eval fun a : Fin r × Fin r => x' a.1 * y' a.2)
      ≤ (Module.finrank ℚ M : ℝ) * Real.log 2
        + (Height.logHeight x' + Height.logHeight y') := by
    refine h1.trans ?_
    rw [Nat.cast_one, one_mul, h2]
    exact add_le_add_left h3 _
  have := mul_le_mul_of_nonneg_left hcomb hd0
  calc (Module.finrank ℚ M : ℝ)⁻¹ * Height.logHeight (fun p : Fin r × Fin r =>
        (mwb1Minor M r p).eval fun a : Fin r × Fin r => x' a.1 * y' a.2)
      ≤ (Module.finrank ℚ M : ℝ)⁻¹ * ((Module.finrank ℚ M : ℝ) * Real.log 2
          + (Height.logHeight x' + Height.logHeight y')) := this
    _ = (Module.finrank ℚ M : ℝ)⁻¹ * Height.logHeight x'
          + (Module.finrank ℚ M : ℝ)⁻¹ * Height.logHeight y' + Real.log 2 := by
        field_simp
        ring

open Real in

private theorem mwb1_pairHt_ge {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    -Real.log 2 ≤ pairHt s v w := by
  have h : absLogHeight (chordVec s v w)
      ≤ absLogHeight (evalVec s v) + absLogHeight (evalVec s w) + Real.log 2 :=
    mwb1_chord_le (evalVec s v) (evalVec s w)
  unfold AlgebraicCurve.pairHt AlgebraicCurve.pointHt
  linarith

open Real in

private theorem mwb1_baseHt_ge {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) (b v : Place (AlgebraicClosure ℚ) F) :
    -Real.log 2 ≤ baseHt s b v := by
  unfold AlgebraicCurve.baseHt
  split_ifs
  · have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · exact mwb1_pairHt_ge s v b

private theorem mwb1_mul_bound {a a0 X Xub Xlb : ℝ}
    (haub : a ≤ a0) (halb : -a0 ≤ a) (hXub : X ≤ Xub) (hXlb : Xlb ≤ X)
    (hXub0 : 0 ≤ Xub) (hXlb0 : Xlb ≤ 0) (ha0 : 0 ≤ a0) :
    a * X ≤ a0 * Xub + a0 * (-Xlb) := by
  rcases le_or_gt 0 X with hX | hX
  · have h1 : a * X ≤ a0 * X := mul_le_mul_of_nonneg_right haub hX
    have h2 : a0 * X ≤ a0 * Xub := mul_le_mul_of_nonneg_left hXub ha0
    nlinarith
  · have h1 : a * X ≤ -a0 * X := by nlinarith
    have h2 : -X ≤ -Xlb := by linarith
    have h3 : a0 * (-X) ≤ a0 * (-Xlb) := mul_le_mul_of_nonneg_left h2 ha0
    nlinarith

set_option maxHeartbeats 6400000 in
open Real in

private theorem mwb1_Q_le_ptsum (N : ℕ) [NeZero N] (g' : ℕ) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (_hs : IsEmbBasis N s) :
    ∃ A C₀ : ℝ, 0 ≤ A ∧ ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, 0 ≤ D v) →
      ((D.erase (cuspInftyBar N)).sum fun _ n => (n : ℝ)) ≤ g' →
      JZero.heightForm N s D
        ≤ A * ((D.erase (cuspInftyBar N)).sum fun v n => (n : ℝ) * pointHt s v) + C₀ := by
  classical
  obtain ⟨γ, hγ⟩ : ∃ γ : ℤ,
      γ = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := ⟨_, rfl⟩
  have hγ0 : (0 : ℤ) ≤ γ := by
    rw [hγ]
    exact_mod_cast Nat.zero_le _
  have hγR0 : (0 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ0
  obtain ⟨a0, ha0def⟩ : ∃ a0 : ℝ, a0 = (γ : ℝ) + g' + 1 := ⟨_, rfl⟩
  have ha00 : (0 : ℝ) ≤ a0 := by rw [ha0def]; positivity
  obtain ⟨u0, hu0def⟩ : ∃ u0 : ℝ, u0 = 2 * (γ : ℝ) + 2 := ⟨_, rfl⟩
  have hu00 : (0 : ℝ) ≤ u0 := by rw [hu0def]; positivity
  have hL0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg'0 : (0 : ℝ) ≤ (g' : ℝ) := Nat.cast_nonneg g'
  refine ⟨a0 + u0 * g' / 2,
    a0 * ((g' : ℝ) * pointHt s (cuspInftyBar N)) + a0 * ((g' : ℝ) * Real.log 2)
      + Real.log 2 * (g' : ℝ) ^ 2 / 2
      + u0 * ((g' : ℝ) ^ 2 / 2 * pointHt s (cuspInftyBar N))
      + u0 * ((g' : ℝ) ^ 2 / 2 * Real.log 2),
    by positivity, fun D hD hdeg => ?_⟩
  unfold ModularCurve.JZero.heightForm AlgebraicCurve.heightForm AlgebraicCurve.heightFormAux
  rw [← hγ]

  obtain ⟨E, hEdef⟩ : ∃ E, E = D.erase (cuspInftyBar N) := ⟨_, rfl⟩
  rw [← hEdef] at hdeg ⊢
  have hEZ : ∀ v, (0 : ℤ) ≤ E v := by
    intro v
    rw [hEdef, Finsupp.erase_apply]
    split_ifs
    · exact le_refl 0
    · exact hD v
  have hE0 : ∀ v, (0 : ℝ) ≤ (E v : ℝ) := fun v => by exact_mod_cast hEZ v
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ v ∈ E.support, (E v : ℝ) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ∑ v ∈ E.support, (E v : ℝ) * pointHt s v := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ,
      T = ∑ v ∈ E.support, (E v : ℝ) * baseHt s (cuspInftyBar N) v := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = ∑ v ∈ E.support,
      ((E v : ℝ) * ((E v : ℝ) - 1) / 2) * baseHt s (cuspInftyBar N) v := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = ∑ p ∈ E.support.offDiag,
      ((E p.1 : ℝ) * (E p.2 : ℝ)) * pairHt s p.1 p.2 := ⟨_, rfl⟩

  rw [show (E.sum fun _ n => (n : ℝ)) = S from by rw [hSdef]; rfl] at hdeg
  rw [show (E.sum fun v n => (n : ℝ) * baseHt s (cuspInftyBar N) v) = T from by
      rw [hTdef]; rfl,
    show (E.sum fun _ n => (n : ℝ)) = S from by rw [hSdef]; rfl,
    show (E.sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * baseHt s (cuspInftyBar N) v) = U
      from by rw [hUdef]; rfl,
    show (∑ p ∈ E.support.offDiag, ((E p.1 : ℝ) * (E p.2 : ℝ)) * pairHt s p.1 p.2) = W
      from by rw [hWdef],
    show (E.sum fun v n => (n : ℝ) * pointHt s v) = P from by rw [hPdef]; rfl]

  have hS0 : (0 : ℝ) ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun v _ => hE0 v
  have hP0 : (0 : ℝ) ≤ P := by
    rw [hPdef]
    exact Finset.sum_nonneg fun v _ => mul_nonneg (hE0 v) (mwb1_pointHt_nonneg s v)
  have hβ0 : (0 : ℝ) ≤ pointHt s (cuspInftyBar N) := mwb1_pointHt_nonneg s _
  have hnS : ∀ v ∈ E.support, (E v : ℝ) ≤ S := by
    intro v hv
    rw [hSdef]
    exact Finset.single_le_sum (fun i _ => hE0 i) hv
  have hq0 : ∀ v, (0 : ℝ) ≤ (E v : ℝ) * ((E v : ℝ) - 1) / 2 := by
    intro v
    have h1 := hEZ v
    have h2 : (0 : ℤ) ≤ E v * (E v - 1) := by
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h]
        simp
      · have h3 : (1 : ℤ) ≤ E v := h
        nlinarith
    have h3 : (0 : ℝ) ≤ (E v : ℝ) * ((E v : ℝ) - 1) := by exact_mod_cast h2
    linarith

  have hTub : T ≤ P + S * pointHt s (cuspInftyBar N) := by
    rw [hTdef, hPdef, hSdef, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have h1 := mwb1_baseHt_le s (cuspInftyBar N) v
    have h2 := hE0 v
    nlinarith [mwb1_pointHt_nonneg s v]
  have hTlb : -(S * Real.log 2) ≤ T := by
    rw [hTdef, hSdef, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    have h1 := mwb1_baseHt_ge s (cuspInftyBar N) v
    have h2 := hE0 v
    nlinarith

  have hoffS : (∑ p ∈ E.support.offDiag, (E p.1 : ℝ) * (E p.2 : ℝ)) ≤ S ^ 2 := by
    have hsub : E.support.offDiag ⊆ E.support ×ˢ E.support := fun p hp =>
      Finset.mem_product.mpr
        ⟨(Finset.mem_offDiag.mp hp).1, (Finset.mem_offDiag.mp hp).2.1⟩
    have h1 : (∑ p ∈ E.support.offDiag, (E p.1 : ℝ) * (E p.2 : ℝ))
        ≤ ∑ p ∈ E.support ×ˢ E.support, (E p.1 : ℝ) * (E p.2 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
        mul_nonneg (hE0 p.1) (hE0 p.2)
    have h2 : (∑ p ∈ E.support ×ˢ E.support, (E p.1 : ℝ) * (E p.2 : ℝ)) = S ^ 2 := by
      rw [hSdef, sq, Finset.sum_mul_sum]
      exact Finset.sum_product (s := E.support) (t := E.support)
        (f := fun p => (E p.1 : ℝ) * (E p.2 : ℝ))
    linarith
  have hWlb : -(Real.log 2 * S ^ 2) ≤ W := by
    have h1 : (∑ p ∈ E.support.offDiag, -((E p.1 : ℝ) * (E p.2 : ℝ) * Real.log 2)) ≤ W := by
      rw [hWdef]
      refine Finset.sum_le_sum fun p _ => ?_
      have := mwb1_pairHt_ge s p.1 p.2
      nlinarith [mul_nonneg (hE0 p.1) (hE0 p.2)]
    have h2 : (∑ p ∈ E.support.offDiag, -((E p.1 : ℝ) * (E p.2 : ℝ) * Real.log 2))
        = -((∑ p ∈ E.support.offDiag, (E p.1 : ℝ) * (E p.2 : ℝ)) * Real.log 2) := by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [h2] at h1
    nlinarith

  have hUq : (∑ v ∈ E.support, (E v : ℝ) * ((E v : ℝ) - 1) / 2) ≤ S ^ 2 / 2 := by
    have hstep : (∑ v ∈ E.support, (E v : ℝ) * ((E v : ℝ) - 1) / 2)
        ≤ ∑ v ∈ E.support, S / 2 * (E v : ℝ) := by
      refine Finset.sum_le_sum fun v hv => ?_
      have h3 := hnS v hv
      have h4 := hE0 v
      nlinarith
    have h2 : (∑ v ∈ E.support, S / 2 * (E v : ℝ)) = S ^ 2 / 2 := by
      rw [← Finset.mul_sum, ← hSdef]
      ring
    linarith
  have hUq0 : (0 : ℝ) ≤ ∑ v ∈ E.support, (E v : ℝ) * ((E v : ℝ) - 1) / 2 :=
    Finset.sum_nonneg fun v _ => hq0 v
  have hUub : U ≤ S / 2 * P + S ^ 2 / 2 * pointHt s (cuspInftyBar N) := by
    have key : U ≤ ∑ v ∈ E.support, (S / 2 * ((E v : ℝ) * pointHt s v)
        + ((E v : ℝ) * ((E v : ℝ) - 1) / 2) * pointHt s (cuspInftyBar N)) := by
      rw [hUdef]
      refine Finset.sum_le_sum fun v hv => ?_
      have h1 := mwb1_baseHt_le s (cuspInftyBar N) v
      have h2 := hq0 v
      have h3 := hnS v hv
      have h4 := hE0 v
      have h5 := mwb1_pointHt_nonneg s v
      have h3' : (E v : ℝ) - 1 ≤ S := by linarith
      have h6a : (E v : ℝ) * ((E v : ℝ) - 1) ≤ (E v : ℝ) * S :=
        mul_le_mul_of_nonneg_left h3' h4
      have h6 : (E v : ℝ) * ((E v : ℝ) - 1) / 2 ≤ S / 2 * (E v : ℝ) := by linarith
      have h7 : (E v : ℝ) * ((E v : ℝ) - 1) / 2 * baseHt s (cuspInftyBar N) v
          ≤ (E v : ℝ) * ((E v : ℝ) - 1) / 2 * (pointHt s v + pointHt s (cuspInftyBar N)) :=
        mul_le_mul_of_nonneg_left h1 h2
      have h7' : (E v : ℝ) * ((E v : ℝ) - 1) / 2 * (pointHt s v + pointHt s (cuspInftyBar N))
          = (E v : ℝ) * ((E v : ℝ) - 1) / 2 * pointHt s v
            + (E v : ℝ) * ((E v : ℝ) - 1) / 2 * pointHt s (cuspInftyBar N) := by ring
      have h8 : (E v : ℝ) * ((E v : ℝ) - 1) / 2 * pointHt s v
          ≤ S / 2 * (E v : ℝ) * pointHt s v :=
        mul_le_mul_of_nonneg_right h6 h5
      have h9 : S / 2 * (E v : ℝ) * pointHt s v = S / 2 * ((E v : ℝ) * pointHt s v) := by
        ring
      linarith
    refine key.trans ?_
    rw [Finset.sum_add_distrib]
    have e1 : (∑ v ∈ E.support, S / 2 * ((E v : ℝ) * pointHt s v)) = S / 2 * P := by
      rw [← Finset.mul_sum, ← hPdef]
    have e2 : (∑ v ∈ E.support,
        ((E v : ℝ) * ((E v : ℝ) - 1) / 2) * pointHt s (cuspInftyBar N))
        ≤ S ^ 2 / 2 * pointHt s (cuspInftyBar N) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hUq hβ0
    linarith
  have hUlb : -(Real.log 2 * (S ^ 2 / 2)) ≤ U := by
    have h1 : (∑ v ∈ E.support, -(((E v : ℝ) * ((E v : ℝ) - 1) / 2) * Real.log 2)) ≤ U := by
      rw [hUdef]
      refine Finset.sum_le_sum fun v _ => ?_
      have h0 := mwb1_baseHt_ge s (cuspInftyBar N) v
      have h2 := hq0 v
      have h3 : (E v : ℝ) * ((E v : ℝ) - 1) / 2 * (-Real.log 2)
          ≤ (E v : ℝ) * ((E v : ℝ) - 1) / 2 * baseHt s (cuspInftyBar N) v :=
        mul_le_mul_of_nonneg_left h0 h2
      have h4 : (E v : ℝ) * ((E v : ℝ) - 1) / 2 * (-Real.log 2)
          = -((E v : ℝ) * ((E v : ℝ) - 1) / 2 * Real.log 2) := by ring
      linarith
    have h2 : (∑ v ∈ E.support, -(((E v : ℝ) * ((E v : ℝ) - 1) / 2) * Real.log 2))
        = -((∑ v ∈ E.support, (E v : ℝ) * ((E v : ℝ) - 1) / 2) * Real.log 2) := by
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [h2] at h1
    nlinarith

  have hSg : S ^ 2 ≤ (g' : ℝ) ^ 2 := by
    rw [sq, sq]
    exact mul_self_le_mul_self hS0 hdeg
  have hterm1 : ((γ : ℝ) + S - 1) * T
      ≤ a0 * P + a0 * ((g' : ℝ) * pointHt s (cuspInftyBar N))
        + a0 * ((g' : ℝ) * Real.log 2) := by
    have haub : (γ : ℝ) + S - 1 ≤ a0 := by
      rw [ha0def]
      linarith
    have halb : -a0 ≤ (γ : ℝ) + S - 1 := by
      rw [ha0def]
      linarith
    have hXub : T ≤ P + (g' : ℝ) * pointHt s (cuspInftyBar N) := by
      have := mul_le_mul_of_nonneg_right hdeg hβ0
      linarith
    have hXlb : -((g' : ℝ) * Real.log 2) ≤ T := by
      have := mul_le_mul_of_nonneg_right hdeg hL0
      linarith
    have hXub0 : (0 : ℝ) ≤ P + (g' : ℝ) * pointHt s (cuspInftyBar N) := by
      have := mul_nonneg hg'0 hβ0
      linarith
    have hXlb0 : -((g' : ℝ) * Real.log 2) ≤ 0 :=
      neg_nonpos_of_nonneg (mul_nonneg hg'0 hL0)
    have h := mwb1_mul_bound haub halb hXub hXlb hXub0 hXlb0 ha00
    calc ((γ : ℝ) + S - 1) * T
        ≤ a0 * (P + (g' : ℝ) * pointHt s (cuspInftyBar N))
          + a0 * (-(-((g' : ℝ) * Real.log 2))) := h
      _ = a0 * P + a0 * ((g' : ℝ) * pointHt s (cuspInftyBar N))
          + a0 * ((g' : ℝ) * Real.log 2) := by ring
  have hterm2 : -(W / 2) ≤ Real.log 2 * (g' : ℝ) ^ 2 / 2 := by
    have h1 : Real.log 2 * S ^ 2 ≤ Real.log 2 * (g' : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hSg hL0
    linarith
  have hterm3 : (2 * (γ : ℝ) - 2) * U
      ≤ u0 * ((g' : ℝ) / 2 * P) + u0 * ((g' : ℝ) ^ 2 / 2 * pointHt s (cuspInftyBar N))
        + u0 * ((g' : ℝ) ^ 2 / 2 * Real.log 2) := by
    have haub : 2 * (γ : ℝ) - 2 ≤ u0 := by
      rw [hu0def]
      linarith
    have halb : -u0 ≤ 2 * (γ : ℝ) - 2 := by
      rw [hu0def]
      linarith
    have hXub : U ≤ (g' : ℝ) / 2 * P + (g' : ℝ) ^ 2 / 2 * pointHt s (cuspInftyBar N) := by
      have h1 : S / 2 * P ≤ (g' : ℝ) / 2 * P :=
        mul_le_mul_of_nonneg_right (by linarith) hP0
      have h2 : S ^ 2 / 2 * pointHt s (cuspInftyBar N)
          ≤ (g' : ℝ) ^ 2 / 2 * pointHt s (cuspInftyBar N) :=
        mul_le_mul_of_nonneg_right (by linarith) hβ0
      linarith
    have hXlb : -((g' : ℝ) ^ 2 / 2 * Real.log 2) ≤ U := by
      have h3a : Real.log 2 * (S ^ 2 / 2) ≤ Real.log 2 * ((g' : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hL0
      have h3b : Real.log 2 * ((g' : ℝ) ^ 2 / 2) = (g' : ℝ) ^ 2 / 2 * Real.log 2 := by ring
      linarith
    have hXub0 : (0 : ℝ) ≤ (g' : ℝ) / 2 * P + (g' : ℝ) ^ 2 / 2 * pointHt s (cuspInftyBar N) := by
      have h4 : (0 : ℝ) ≤ (g' : ℝ) / 2 * P := by positivity
      have h5 : (0 : ℝ) ≤ (g' : ℝ) ^ 2 / 2 * pointHt s (cuspInftyBar N) := by positivity
      linarith
    have hXlb0 : -((g' : ℝ) ^ 2 / 2 * Real.log 2) ≤ 0 :=
      neg_nonpos_of_nonneg (by positivity)
    have h := mwb1_mul_bound haub halb hXub hXlb hXub0 hXlb0 hu00
    calc (2 * (γ : ℝ) - 2) * U
        ≤ u0 * ((g' : ℝ) / 2 * P + (g' : ℝ) ^ 2 / 2 * pointHt s (cuspInftyBar N))
          + u0 * (-(-((g' : ℝ) ^ 2 / 2 * Real.log 2))) := h
      _ = u0 * ((g' : ℝ) / 2 * P) + u0 * ((g' : ℝ) ^ 2 / 2 * pointHt s (cuspInftyBar N))
          + u0 * ((g' : ℝ) ^ 2 / 2 * Real.log 2) := by ring
  have hflip : (2 - 2 * (γ : ℝ)) * U = -((2 * (γ : ℝ) - 2) * U) := by ring
  have hA : (a0 + u0 * (g' : ℝ) / 2) * P = a0 * P + u0 * ((g' : ℝ) / 2 * P) := by ring
  linarith [hterm1, hterm2, hterm3]

private theorem mwb1_erase_deg_le (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (g' : ℕ)
    {c : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h : JZero.IsRepOf N K g' c D) :
    ((D.erase (cuspInftyBar N)).sum fun _ n => (n : ℝ)) ≤ g' := by
  classical
  obtain ⟨E, heff, hshape, hstab, _hc⟩ := h
  have hdeg1 := ModularCurve.deg_eq_one_modularFunctionFieldBar N

  have hdegD : Divisor.degree (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) D
      = g' := by
    rw [← hshape, map_add, Divisor.mem_degZero.mp E.2, zero_add, map_zsmul,
      Divisor.degree_single, hdeg1]
    simp

  have hsum : (D.sum fun _ n => n) = (g' : ℤ) := by
    have hunfold : Divisor.degree (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar N)) D = D.sum fun v n => n * v.deg := by
      simp [Divisor.degree, Finsupp.liftAddHom_apply]
    rw [hunfold] at hdegD
    rw [← hdegD]
    exact Finsupp.sum_congr fun v _ => by rw [hdeg1, Nat.cast_one, mul_one]

  have herase : ((D.erase (cuspInftyBar N)).sum fun _ n => (n : ℝ))
      = (D.sum fun _ n => (n : ℝ)) - (D (cuspInftyBar N) : ℝ) := by
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_erase]
    by_cases hb : cuspInftyBar N ∈ D.support
    · have hvals : ∑ v ∈ D.support.erase (cuspInftyBar N),
          ((D.erase (cuspInftyBar N)) v : ℝ)
          = ∑ v ∈ D.support.erase (cuspInftyBar N), ((D v : ℤ) : ℝ) :=
        Finset.sum_congr rfl fun v hv => by
          rw [Finsupp.erase_apply, if_neg (Finset.mem_erase.mp hv).1]
      rw [hvals, Finset.sum_erase_eq_sub hb]
    · rw [Finset.erase_eq_of_notMem hb, Finsupp.notMem_support_iff.mp hb, Int.cast_zero,
        sub_zero]
      exact Finset.sum_congr rfl fun v hv => by
        rw [Finsupp.erase_apply, if_neg]
        rintro rfl
        exact hb hv
  have hcast : (D.sum fun _ n => (n : ℝ)) = ((D.sum fun _ n => n : ℤ) : ℝ) := by
    rw [Finsupp.sum, Finsupp.sum, Int.cast_sum]
  rw [herase, hcast, hsum]
  have h0 : (0 : ℝ) ≤ (D (cuspInftyBar N) : ℝ) := by exact_mod_cast heff (cuspInftyBar N)
  push_cast
  linarith

end MWB1

namespace ModularCurve p2m_export "ModularCurve" "divNaiveHeight cuspInftyBar modularFunctionFieldBar JZero IsEmbBasis JZero.heightForm JZero.IsRepOf deg_eq_one_modularFunctionFieldBar JZero.ptsum_pointHt_le_divNaiveHeight" namespace JZero p2m_export "ModularCurve.JZero" "heightForm IsRepOf ptsum_pointHt_le_divNaiveHeight" end ModularCurve.JZero
p2m_open_scoped "ModularCurve ModularCurve.JZero" in
open _root_.ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_JZero_heightForm_le.AlgebraicCurve in

private theorem ModularCurve.JZero.heightForm_le (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₁ C : ℝ, ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), JZero.IsRepOf N K g' c D →
      JZero.heightForm N s D ≤ c₁ * divNaiveHeight N K g' D + C := by
  obtain ⟨A, C₀, hA0, hS2⟩ := MWB1.mwb1_Q_le_ptsum N g' s hs
  obtain ⟨B, hB0, hBn⟩ := ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight N K s hs
  obtain ⟨C₁, hS3⟩ := hBn g'
  refine ⟨A * B, A * C₁ + C₀, fun c D hD => ?_⟩
  obtain ⟨E, heff, hshape, hstab, hc⟩ := hD
  have h2 := hS2 D heff (MWB1.mwb1_erase_deg_le N K g' ⟨E, heff, hshape, hstab, hc⟩)
  have h3 := hS3 c D ⟨E, heff, hshape, hstab, hc⟩
  calc JZero.heightForm N s D
      ≤ A * ((D.erase (cuspInftyBar N)).sum fun v n => (n : ℝ) * pointHt s v) + C₀ := h2
    _ ≤ A * (B * divNaiveHeight N K g' D + C₁) + C₀ :=
        add_le_add_left (mul_le_mul_of_nonneg_left h3 hA0) C₀
    _ = A * B * divNaiveHeight N K g' D + (A * C₁ + C₀) := by ring

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JZero_heightForm_le.ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_JZero_heightForm_le.AlgebraicCurve in
theorem solution (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₁ C : ℝ, ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), JZero.IsRepOf N K g' c D →
      JZero.heightForm N s D ≤ c₁ * divNaiveHeight N K g' D + C :=
  ModularCurve.JZero.heightForm_le N K g' s hs

end S_ModularCurve_JZero_heightForm_le
end P2MW
export P2MW.S_ModularCurve_JZero_heightForm_le (solution)
