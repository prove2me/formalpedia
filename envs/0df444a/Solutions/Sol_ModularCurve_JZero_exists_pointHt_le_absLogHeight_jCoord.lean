-- Prove2me | solution 1 for ModularCurve.JZero.exists_pointHt_le_absLogHeight_jCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/874ba5d1-f2ef-5381-8a42-a261ba92655e

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.NumberTheory.Height.NumberField
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_AlgebraicCurve_absLogHeight_root_le_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false
set_option Elab.async false

attribute [local instance] AlgebraicCurve.finiteDimensional_adjoin_range

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.ord_one Place.ord_inv Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring finiteDimensional_adjoin_range absLogHeight pivotIndex evalVec pointHt Place.algebraMap_evalAt Place.evalAt_one riemannRochSpace mem_riemannRochSpace_iff Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.mem_fiberOver Place.fiber_eq_fiberOver Place.isRational_of_isAlgClosed Place.evalAt_algebraMap Place.evalAt_mul Place.evalAt_ne_zero Place.exists_integralClosureAt_of_ord_fiber_nonneg absLogHeight_root_le_coeff" end AlgebraicCurve
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

p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord.AlgebraicCurve"

private theorem mwb1_absLogHeight_nonneg {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  unfold AlgebraicCurve.absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

private theorem mwb1_absLogHeight_zero {ι : Type} [Fintype ι] :
    absLogHeight (0 : ι → AlgebraicClosure ℚ) = 0 := by
  unfold AlgebraicCurve.absLogHeight
  have h0 : (fun i => (⟨(0 : ι → AlgebraicClosure ℚ) i,
      IntermediateField.subset_adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)) ⟨i, rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)))) = 0 := by
    funext i
    exact Subtype.ext rfl
  rw [h0, Height.logHeight_zero, mul_zero]

private lemma mwb1_hfms_prod {M : Type*} [Field M] [NumberField M] {ι : Type*} (t : Finset ι)
    (g : ι → NumberField.FinitePlace M → ℝ)
    (hg : ∀ i ∈ t, Function.HasFiniteMulSupport (g i)) :
    Function.HasFiniteMulSupport (fun v => ∏ i ∈ t, g i v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Function.hasFiniteMulSupport_fun_one
  | insert a t ha ih =>
    have h1 := hg a (Finset.mem_insert_self a t)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have : (fun v => ∏ i ∈ insert a t, g i v)
        = fun v => g a v * ∏ i ∈ t, g i v := by
      funext v
      rw [Finset.prod_insert ha]
    rw [this]
    exact h1.mul h2

private lemma mwb1_finset_finprod_swap {M : Type*} [Field M] [NumberField M] {ι : Type*}
    (t : Finset ι) (g : ι → NumberField.FinitePlace M → ℝ)
    (hg : ∀ i ∈ t, Function.HasFiniteMulSupport (g i)) :
    ∏ i ∈ t, (∏ᶠ v, g i v) = ∏ᶠ v, ∏ i ∈ t, g i v := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have h1 := hg a (Finset.mem_insert_self a t)
    have h2 : ∀ i ∈ t, Function.HasFiniteMulSupport (g i) :=
      fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, ih h2,
      ← finprod_mul_distrib h1 (mwb1_hfms_prod t g h2)]
    refine finprod_congr fun v => ?_
    rw [Finset.prod_insert ha]

private lemma mwb1_hfms_iSup {M : Type*} [Field M] [NumberField M] {ι : Type*} [Finite ι]
    {x : ι → M} (hx : x ≠ 0) :
    (fun v : NumberField.FinitePlace M ↦ ⨆ i, v (x i)).HasFiniteMulSupport := by
  obtain ⟨i₀, hi₀⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := .intro i₀
  have hne : Nonempty {j // x j ≠ 0} := ⟨⟨i₀, hi₀⟩⟩
  have key : ∀ v : NumberField.FinitePlace M, (⨆ i, v (x i))
      = ⨆ i : {j // x j ≠ 0}, v (x i.val) := by
    intro v
    refine le_antisymm (ciSup_le fun j ↦ ?_) (ciSup_le fun i ↦ Finite.le_ciSup_of_le i.val le_rfl)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, map_zero]
      exact Real.iSup_nonneg fun i ↦ apply_nonneg v _
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  have heq : (fun v : NumberField.FinitePlace M ↦ ⨆ i, v (x i)) =
      fun v : NumberField.FinitePlace M ↦ ⨆ i : {j // x j ≠ 0}, v (x i.val) := funext key
  rw [heq]
  exact Function.HasFiniteMulSupport.iSup fun i ↦ NumberField.FinitePlace.hasFiniteMulSupport i.prop

private lemma mwb1_le_prod_of_one_le {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℝ)
    (hg : ∀ j, 1 ≤ g j) (i : ι) : g i ≤ ∏ j, g j := by
  have h1 : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, g j := by
    calc (1 : ℝ) = ∏ _j ∈ Finset.univ.erase i, (1 : ℝ) := (Finset.prod_const_one).symm
      _ ≤ ∏ j ∈ Finset.univ.erase i, g j :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => hg j)
  calc g i = g i * 1 := (mul_one _).symm
    _ ≤ g i * ∏ j ∈ Finset.univ.erase i, g j :=
      mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one (hg i))
    _ = ∏ j, g j := Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)

private lemma mwb1_mulHeight_le_prod {M : Type*} [Field M] [NumberField M] {m : ℕ}
    (x : Fin (m + 1) → M) :
    Height.mulHeight x ≤ ∏ i, Height.mulHeight₁ (x i) := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Height.mulHeight_zero]
    have h1 : (1 : ℝ) = ∏ _i : Fin (m + 1), (1 : ℝ) := (Finset.prod_const_one).symm
    refine le_trans (le_of_eq h1) ?_
    exact Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => Height.one_le_mulHeight₁ _)
  rw [NumberField.mulHeight_eq hx]
  have hBsupp : ∀ i : Fin (m + 1), Function.HasFiniteMulSupport
      (fun v : NumberField.FinitePlace M => max (v (x i)) 1) := by
    intro i
    have hxi : (fun k : Fin 2 => (![x i, 1] : Fin 2 → M) k) ≠ 0 := by
      refine Function.ne_iff.mpr ⟨1, ?_⟩
      simp
    have h := mwb1_hfms_iSup (M := M) hxi
    have heq : (fun v : NumberField.FinitePlace M ↦ ⨆ k : Fin 2, v (![x i, 1] k))
        = fun v : NumberField.FinitePlace M => max (v (x i)) 1 := by
      funext v
      refine le_antisymm (ciSup_le fun k => ?_) ?_
      · fin_cases k
        · simp
        · simp
      · rcases max_cases (v (x i)) 1 with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm]
        · exact Finite.le_ciSup_of_le (0 : Fin 2) (by simp)
        · exact Finite.le_ciSup_of_le (1 : Fin 2) (by simp [map_one])
    rw [← heq]
    exact h
  have hfin : (∏ᶠ v : NumberField.FinitePlace M, ⨆ i, v (x i))
      ≤ ∏ᶠ v : NumberField.FinitePlace M, ∏ i, max (v (x i)) 1 := by
    refine finprod_le_finprod (mwb1_hfms_iSup hx)
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v _)
      (mwb1_hfms_prod Finset.univ _ fun i _ => hBsupp i) (fun v => ?_)
    refine ciSup_le fun i => ?_
    exact le_trans (le_max_left (v (x i)) 1)
      (mwb1_le_prod_of_one_le (fun j => max (v (x j)) 1) (fun j => le_max_right _ _) i)
  have harch : (∏ w : NumberField.InfinitePlace M, (⨆ i, w (x i)) ^ w.mult)
      ≤ ∏ w : NumberField.InfinitePlace M, (∏ i, max (w (x i)) 1) ^ w.mult := by
    refine Finset.prod_le_prod (fun w _ => ?_) (fun w _ => ?_)
    · exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass w _) _
    · refine pow_le_pow_left₀ (Real.iSup_nonneg_of_nonnegHomClass w _) ?_ _
      refine ciSup_le fun i => ?_
      exact le_trans (le_max_left (w (x i)) 1)
        (mwb1_le_prod_of_one_le (fun j => max (w (x j)) 1) (fun j => le_max_right _ _) i)
  calc (∏ w : NumberField.InfinitePlace M, (⨆ i, w (x i)) ^ w.mult) *
        ∏ᶠ v : NumberField.FinitePlace M, ⨆ i, v (x i)
      ≤ (∏ w : NumberField.InfinitePlace M, (∏ i, max (w (x i)) 1) ^ w.mult) *
          ∏ᶠ v : NumberField.FinitePlace M, ∏ i, max (v (x i)) 1 := by
        refine mul_le_mul harch hfin ?_ ?_
        · exact finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v _
        · exact Finset.prod_nonneg fun w _ => pow_nonneg
            (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) _
    _ = ∏ i, Height.mulHeight₁ (x i) := by
        have hmh : (∏ i, Height.mulHeight₁ (x i))
            = ∏ i, ((∏ w : NumberField.InfinitePlace M, max (w (x i)) 1 ^ w.mult) *
                ∏ᶠ v : NumberField.FinitePlace M, max (v (x i)) 1) :=
          Finset.prod_congr rfl fun i _ => NumberField.mulHeight₁_eq (x i)
        rw [hmh, Finset.prod_mul_distrib]
        congr 1
        · calc (∏ w : NumberField.InfinitePlace M, (∏ i, max (w (x i)) 1) ^ w.mult)
              = ∏ w : NumberField.InfinitePlace M, ∏ i, max (w (x i)) 1 ^ w.mult :=
                Finset.prod_congr rfl fun w _ => (Finset.prod_pow _ _ _).symm
            _ = ∏ i, ∏ w : NumberField.InfinitePlace M, max (w (x i)) 1 ^ w.mult :=
                Finset.prod_comm
        · exact (mwb1_finset_finprod_swap Finset.univ _ fun i _ => hBsupp i).symm

open Real in

private theorem mwb1_absHt1_eq (z : AlgebraicClosure ℚ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] (hz : z ∈ L) :
    absLogHeight ![z, 1] = (Module.finrank ℚ L : ℝ)⁻¹ * Height.logHeight₁ (⟨z, hz⟩ : L) := by
  have hmem : ∀ k : Fin 2, (![z, 1] : Fin 2 → AlgebraicClosure ℚ) k ∈ L := by
    intro k
    fin_cases k
    · exact hz
    · exact one_mem L
  rw [AlgebraicCurve.absLogHeight_eq_of_mem _ L hmem]
  congr 1
  have htup : (fun k : Fin 2 => (⟨(![z, 1] : Fin 2 → AlgebraicClosure ℚ) k, hmem k⟩ : L))
      = ![(⟨z, hz⟩ : L), 1] := by
    funext k
    fin_cases k
    · rfl
    · exact Subtype.ext (by simp)
  rw [htup, ← Height.logHeight₁_eq_logHeight]

open Real in

private theorem mwb1_eval_ht (P : Polynomial (AlgebraicClosure ℚ)) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ a : AlgebraicClosure ℚ,
      absLogHeight ![P.eval a, 1] ≤ B * absLogHeight ![a, 1] + C := by
  classical
  set n : ℕ := P.natDegree with hn
  have hC0 : (0 : ℝ) ≤ (∑ k ∈ Finset.range (n + 1), absLogHeight ![P.coeff k, 1])
      + Real.log (n + 1) := by
    have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), absLogHeight ![P.coeff k, 1] :=
      Finset.sum_nonneg fun k _ => MWB1.mwb1_absLogHeight_nonneg _
    have h2 : (0 : ℝ) ≤ Real.log (n + 1) :=
      Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
    linarith
  refine ⟨((n + 1) * n : ℕ), (∑ k ∈ Finset.range (n + 1), absLogHeight ![P.coeff k, 1])
      + Real.log (n + 1), Nat.cast_nonneg _, hC0, fun a => ?_⟩
  set S : Set (AlgebraicClosure ℚ) :=
    insert a (↑((Finset.range (n + 1)).image P.coeff)) with hS
  haveI hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  set M := IntermediateField.adjoin ℚ S with hM
  have hmem_a : a ∈ M := IntermediateField.subset_adjoin ℚ S (Set.mem_insert a _)
  have hmem_c : ∀ k, k ∈ Finset.range (n + 1) → P.coeff k ∈ M := fun k hk =>
    IntermediateField.subset_adjoin ℚ S (Set.mem_insert_iff.mpr (Or.inr
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem P.coeff hk))))
  have hmem_ev : P.eval a ∈ M := by
    rw [Polynomial.eval_eq_sum_range]
    exact sum_mem fun k hk => mul_mem (hmem_c k hk) (pow_mem hmem_a k)
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := M)
  have hd0 : (0 : ℝ) < (Module.finrank ℚ M : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  set c' : ℕ → M := fun k => if h : k ∈ Finset.range (n + 1)
    then (⟨P.coeff k, hmem_c k h⟩ : M) else 0 with hc'
  have hev_eq : (⟨P.eval a, hmem_ev⟩ : M)
      = ∑ k ∈ Finset.range (n + 1), c' k * (⟨a, hmem_a⟩ : M) ^ k := by
    refine Subtype.ext ?_
    push_cast
    rw [Polynomial.eval_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [show c' k = (⟨P.coeff k, hmem_c k hk⟩ : M) from dif_pos hk]
  have hrel : Height.logHeight₁ (⟨P.eval a, hmem_ev⟩ : M)
      ≤ (Height.totalWeight M : ℝ) * Real.log (n + 1)
        + ∑ k ∈ Finset.range (n + 1),
            (Height.logHeight₁ (c' k) + (n : ℝ) * Height.logHeight₁ (⟨a, hmem_a⟩ : M)) := by
    rw [hev_eq]
    refine (Height.logHeight₁_sum_le _ _).trans ?_
    have hcard : (((Finset.range (n + 1)).card : ℕ) : ℝ) = (n + 1 : ℝ) := by
      rw [Finset.card_range]
      push_cast
      ring
    rw [hcard]
    refine add_le_add le_rfl (Finset.sum_le_sum fun k hk => ?_)
    refine (Height.logHeight₁_mul_le _ _).trans ?_
    refine add_le_add le_rfl ?_
    rw [Height.logHeight₁_pow]
    have hha : 0 ≤ Height.logHeight₁ (⟨a, hmem_a⟩ : M) := by
      rw [Height.logHeight₁_eq_log_mulHeight₁]
      exact Real.log_nonneg (Height.one_le_mulHeight₁ _)
    refine mul_le_mul_of_nonneg_right ?_ hha
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mwb1_absHt1_eq (P.eval a) M hmem_ev, mwb1_absHt1_eq a M hmem_a]
  have hcoeff_abs : ∀ k ∈ Finset.range (n + 1),
      (Module.finrank ℚ M : ℝ)⁻¹ * Height.logHeight₁ (c' k)
        = absLogHeight ![P.coeff k, 1] := by
    intro k hk
    rw [show c' k = (⟨P.coeff k, hmem_c k hk⟩ : M) from dif_pos hk]
    exact (mwb1_absHt1_eq (P.coeff k) M (hmem_c k hk)).symm
  have htW : (Height.totalWeight M : ℝ) = (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast congrArg Nat.cast (NumberField.totalWeight_eq_finrank (K := M))
  have h := mul_le_mul_of_nonneg_left hrel (inv_nonneg.mpr hd0.le)
  refine h.trans (le_of_eq ?_)
  rw [htW, mul_add, inv_mul_cancel_left₀ hd0.ne', Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, mul_add, Finset.mul_sum]
  have hc_sum : (∑ k ∈ Finset.range (n + 1),
      (Module.finrank ℚ M : ℝ)⁻¹ * Height.logHeight₁ (c' k))
      = ∑ k ∈ Finset.range (n + 1), absLogHeight ![P.coeff k, 1] :=
    Finset.sum_congr rfl hcoeff_abs
  rw [hc_sum, nsmul_eq_mul]
  push_cast
  ring

private theorem mwb1_root_ht {χ : Polynomial (AlgebraicClosure ℚ)} (hχ : χ.Monic)
    {z : AlgebraicClosure ℚ} (hz : χ.eval z = 0) :
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (χ.natDegree + 1) => χ.coeff k)
        + Real.log (Real.sqrt (χ.natDegree + 1)) :=
  AlgebraicCurve.absLogHeight_root_le_coeff hχ hz

open Real in

private theorem mwb1_absHt_le_sum {m : ℕ} (x : Fin (m + 1) → AlgebraicClosure ℚ) :
    absLogHeight x ≤ ∑ i, absLogHeight ![x i, 1] := by
  classical
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
    AlgebraicCurve.finiteDimensional_adjoin_range x
  set M := IntermediateField.adjoin ℚ (Set.range x) with hM
  have hx : ∀ k, x k ∈ M := fun k =>
    IntermediateField.subset_adjoin ℚ (Set.range x) ⟨k, rfl⟩
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := M)
  have hd0 : (0 : ℝ) < (Module.finrank ℚ M : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  rw [AlgebraicCurve.absLogHeight_eq_of_mem _ M hx]
  have hent : ∀ i, absLogHeight ![x i, 1]
      = (Module.finrank ℚ M : ℝ)⁻¹ * Height.logHeight₁ (⟨x i, hx i⟩ : M) := fun i =>
    mwb1_absHt1_eq (x i) M (hx i)
  have hrel : Height.logHeight (fun k => (⟨x k, hx k⟩ : M))
      ≤ ∑ i, Height.logHeight₁ (⟨x i, hx i⟩ : M) := by
    have hmul : Height.mulHeight (fun k => (⟨x k, hx k⟩ : M))
        ≤ ∏ i, Height.mulHeight₁ (⟨x i, hx i⟩ : M) := mwb1_mulHeight_le_prod _
    have hpos1 : (0 : ℝ) < Height.mulHeight (fun k => (⟨x k, hx k⟩ : M)) :=
      Height.mulHeight_pos _
    calc Height.logHeight (fun k => (⟨x k, hx k⟩ : M))
        = Real.log (Height.mulHeight (fun k => (⟨x k, hx k⟩ : M))) :=
          Height.logHeight_eq_log_mulHeight _
      _ ≤ Real.log (∏ i, Height.mulHeight₁ (⟨x i, hx i⟩ : M)) :=
          Real.log_le_log hpos1 hmul
      _ = ∑ i, Real.log (Height.mulHeight₁ (⟨x i, hx i⟩ : M)) :=
          Real.log_prod fun i _ =>
            (lt_of_lt_of_le zero_lt_one (Height.one_le_mulHeight₁ _)).ne'
      _ = ∑ i, Height.logHeight₁ (⟨x i, hx i⟩ : M) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Height.logHeight₁_eq_log_mulHeight₁]
  calc (Module.finrank ℚ M : ℝ)⁻¹ * Height.logHeight (fun k => (⟨x k, hx k⟩ : M))
      ≤ (Module.finrank ℚ M : ℝ)⁻¹ * ∑ i, Height.logHeight₁ (⟨x i, hx i⟩ : M) :=
        mul_le_mul_of_nonneg_left hrel (inv_nonneg.mpr hd0.le)
    _ = ∑ i, absLogHeight ![x i, 1] := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => (hent i).symm

private theorem mwb1_jelt_transcendental (N : ℕ) [NeZero N] :
    Transcendental (AlgebraicClosure ℚ)
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) :=
  ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N

private theorem mwb1_fd_adjoin (N : ℕ) [NeZero N] :
    FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) :=
  ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N

set_option synthInstance.maxHeartbeats 1600000 in
private noncomputable local instance mwb1_laurentMulAction :
    MulAction (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  inferInstance

private noncomputable def mwb1_ratFuncEquiv (N : ℕ) [NeZero N] :
    RatFunc (AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ]
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) :=
  RatFunc.algEquivOfTranscendental
    (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
    (mwb1_jelt_transcendental N)

private noncomputable def mwb1_ratFuncHom (N : ℕ) [NeZero N] :
    RatFunc (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
  (IntermediateField.val
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))).comp
    (mwb1_ratFuncEquiv N).toAlgHom

private theorem mwb1_isRational (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational := by
  haveI hfd := mwb1_fd_adjoin N
  letI : Algebra (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
    (mwb1_ratFuncHom N).toRingHom.toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))
      (modularFunctionFieldBar N) :=
    IsScalarTower.of_algebraMap_eq' ((mwb1_ratFuncHom N).comp_algebraMap).symm
  haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) := by
    refine Module.Finite.of_equiv_equiv (A₁ :=
        IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
      (B₁ := modularFunctionFieldBar N)
      (mwb1_ratFuncEquiv N).symm.toRingEquiv (RingEquiv.refl _) ?_
    refine RingHom.ext fun c => ?_
    show mwb1_ratFuncHom N ((mwb1_ratFuncEquiv N).symm c) = (c : modularFunctionFieldBar N)
    simp [mwb1_ratFuncHom]
  exact AlgebraicCurve.Place.isRational_of_isAlgClosed v

private theorem mwb1_mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rw [Place.mem_iff_adicValuation_le_one]
  have hne := v.adicValuation_ne_zero hf
  have h' : (0 : ℤ) ≤ -(WithZero.log (v.adicValuation f)) := h
  have hlog : WithZero.log (v.adicValuation f) ≤ 0 := by linarith
  calc v.adicValuation f
      = WithZero.exp (WithZero.log (v.adicValuation f)) := (WithZero.exp_log hne).symm
    _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr hlog
    _ = 1 := WithZero.exp_zero

private theorem mwb1_adicValuation_lt_one_of_ord_pos {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (h : 0 < v.ord f) :
    v.adicValuation f < 1 := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero]
    exact zero_lt_one
  have hne := v.adicValuation_ne_zero hf
  have h' : (0 : ℤ) < -(WithZero.log (v.adicValuation f)) := h
  have hlog : WithZero.log (v.adicValuation f) < 0 := by linarith
  calc v.adicValuation f
      = WithZero.exp (WithZero.log (v.adicValuation f)) := (WithZero.exp_log hne).symm
    _ < WithZero.exp 0 := WithZero.exp_lt_exp.mpr hlog
    _ = 1 := WithZero.exp_zero

private noncomputable def mwb1_residueEquiv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) : K ≃+* v.ResidueField :=
  RingEquiv.ofBijective (algebraMap K v.ResidueField)
    ⟨v.algebraMap_residueField_injective, hv⟩

private noncomputable def mwb1_psi {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) : v.toValuationSubring →+* K :=
  (mwb1_residueEquiv v hv).symm.toRingHom.comp (IsLocalRing.residue v.toValuationSubring)

private theorem mwb1_psi_eq_evalAt {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    mwb1_psi v hv ⟨f, hf⟩ = v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [Place.algebraMap_evalAt v hv hf]
  have hcoe : ∀ y, (mwb1_residueEquiv v hv) y = algebraMap K v.ResidueField y := fun y => rfl
  show algebraMap K v.ResidueField
      ((mwb1_residueEquiv v hv).symm (IsLocalRing.residue _ ⟨f, hf⟩)) = _
  rw [← hcoe, RingEquiv.apply_symm_apply]

private theorem mwb1_psi_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) (x : v.toValuationSubring) :
    mwb1_psi v hv x = 0 ↔ v.adicValuation (x : F) < 1 := by
  rw [← Place.mem_maximalIdeal_iff_adicValuation_lt_one,
    ← IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (mwb1_residueEquiv v hv) h
    rwa [mwb1_psi, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply, map_zero] at this
  · intro h
    rw [mwb1_psi, RingHom.comp_apply, h]
    simp

private theorem mwb1_s_regular (N : ℕ) [NeZero N] {r : ℕ}
    {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (i : Fin r)
    {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v ≠ cuspInftyBar N) : s i ∈ v.toValuationSubring := by
  classical
  have hne : s i ≠ 0 := hs.1.ne_zero i
  have hmem : s i ∈ riemannRochSpace (embDivisor N) := by
    rw [← hs.2]
    exact Submodule.subset_span (Set.mem_range_self i)
  rcases (AlgebraicCurve.mem_riemannRochSpace_iff.mp hmem) v with h0 | hord
  · exact absurd h0 hne
  · refine mwb1_mem_of_ord_nonneg v hne ?_
    refine le_trans (le_of_eq ?_) hord
    have hzero : (embDivisor N) v = 0 := by
      rw [ModularCurve.embDivisor]
      rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (fun h => hv h.symm)]
      simp
    rw [hzero, neg_zero]

private theorem mwb1_evalAt_jelt (N : ℕ) [NeZero N]
    {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv0 : 0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)) :
    v.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) = jCoord N v := by
  have hrat := mwb1_isRational N v
  have ht := mwb1_jelt_transcendental N
  have hjne : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ≠ 0 := by
    intro h0
    exact ht (h0 ▸ isAlgebraic_zero)
  obtain ⟨hspec, -, -⟩ := ModularCurve.jCoordinate_spec_modularFunctionFieldBar N
  have heps : 0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jCoord N v)) :=
    Classical.epsilon_spec (hspec v hv0).exists
  have hmemj : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ v.toValuationSubring :=
    mwb1_mem_of_ord_nonneg v hjne hv0
  have hmemc : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jCoord N v)
      ∈ v.toValuationSubring := v.algebraMap_mem' _
  have hmemd : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jCoord N v)
      ∈ v.toValuationSubring := sub_mem hmemj hmemc
  have hker : mwb1_psi v hrat ⟨_, hmemd⟩ = 0 :=
    (mwb1_psi_zero_iff v hrat _).mpr (mwb1_adicValuation_lt_one_of_ord_pos v heps)
  have hsplit : (⟨_, hmemj⟩ : v.toValuationSubring)
      = ⟨_, hmemc⟩ + ⟨_, hmemd⟩ := by
    refine Subtype.ext ?_
    push_cast
    ring
  have := congrArg (mwb1_psi v hrat) hsplit
  rw [map_add, hker, add_zero, mwb1_psi_eq_evalAt v hrat hmemj,
    mwb1_psi_eq_evalAt v hrat hmemc] at this
  rw [this]
  exact AlgebraicCurve.Place.evalAt_algebraMap v (jCoord N v)

private theorem mwb1_ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  have hval := (Place.mem_iff_adicValuation_le_one v).mp h
  have hne := v.adicValuation_ne_zero hf
  have h1 : WithZero.exp (WithZero.log (v.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]
    exact hval
  have h2 : WithZero.log (v.adicValuation f) ≤ 0 := WithZero.exp_le_exp.mp h1
  show (0 : ℤ) ≤ -(WithZero.log (v.adicValuation f))
  linarith

private theorem mwb1_psi_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) (c : K) :
    mwb1_psi v hv ⟨algebraMap K F c, v.algebraMap_mem' c⟩ = c := by
  rw [mwb1_psi_eq_evalAt v hv (v.algebraMap_mem' c)]
  exact AlgebraicCurve.Place.evalAt_algebraMap v c

private theorem mwb1_ne_cuspInfty_of_jelt_mem (N : ℕ) [NeZero N]
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ w.toValuationSubring) :
    w ≠ cuspInftyBar N := by
  rintro rfl
  rw [ModularCurve.cuspInftyBar_toValuationSubring] at h
  exact ModularCurve.notMem_qIntegersBar_of_order_eq_neg_one
    (show (ModularCurve.qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)).order = -1
      from ModularCurve.order_coeffEmb_jq (AlgebraicClosure ℚ)) h

private theorem mwb1_adjoin_mem (N : ℕ) [NeZero N]
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hmemj : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ w.toValuationSubring)
    {x : modularFunctionFieldBar N}
    (hx : x ∈ Algebra.adjoin (AlgebraicClosure ℚ)
      ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) :
    x ∈ w.toValuationSubring := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hmemj
  | algebraMap c => exact w.algebraMap_mem' c
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

private theorem mwb1_evalAt_aeval (N : ℕ) [NeZero N]
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hrat : w.IsRational)
    (hmemj : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ w.toValuationSubring)
    (P : Polynomial (AlgebraicClosure ℚ)) :
    w.evalAt (Polynomial.aeval
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) P)
      = P.eval (w.evalAt
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)) := by
  classical
  have hmem : Polynomial.aeval
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) P
      ∈ w.toValuationSubring := by
    refine mwb1_adjoin_mem N hmemj ?_
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨P, rfl⟩

  set ρc : (AlgebraicClosure ℚ) →+* w.toValuationSubring :=
    (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).codRestrict
      _ (fun c => w.algebraMap_mem' c) with hρc

  have hO : w.toValuationSubring.subtype
      (Polynomial.eval₂ ρc (⟨_, hmemj⟩ : w.toValuationSubring) P)
      = Polynomial.aeval
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) P := by
    rw [Polynomial.hom_eval₂]
    have h1 : (w.toValuationSubring.subtype).comp ρc
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := rfl
    rw [h1]
    rfl
  have hψ : mwb1_psi w hrat (Polynomial.eval₂ ρc (⟨_, hmemj⟩ : w.toValuationSubring) P)
      = Polynomial.eval₂ ((mwb1_psi w hrat).comp ρc)
          (mwb1_psi w hrat (⟨_, hmemj⟩ : w.toValuationSubring)) P :=
    Polynomial.hom_eval₂ _ _ _ _
  have hcomp : (mwb1_psi w hrat).comp ρc = RingHom.id (AlgebraicClosure ℚ) := by
    refine RingHom.ext fun c => ?_
    show mwb1_psi w hrat (ρc c) = c
    have hc : ρc c = ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c,
        w.algebraMap_mem' c⟩ := rfl
    rw [hc, mwb1_psi_algebraMap w hrat c]
  have heq : (⟨Polynomial.aeval
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) P, hmem⟩ : w.toValuationSubring)
      = Polynomial.eval₂ ρc (⟨_, hmemj⟩ : w.toValuationSubring) P :=
    Subtype.ext hO.symm
  rw [← mwb1_psi_eq_evalAt w hrat hmem, ← mwb1_psi_eq_evalAt w hrat hmemj, heq, hψ, hcomp,
    Polynomial.eval₂_id]

open scoped IntermediateField.algebraAdjoinAdjoin in

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in

private theorem mwb1_isIntegral_adjoin (N : ℕ) [NeZero N]
    {x : modularFunctionFieldBar N} (hx : x ≠ 0)
    (hreg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      w ≠ cuspInftyBar N → x ∈ w.toValuationSubring) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) x := by
  classical
  have ht := mwb1_jelt_transcendental N
  haveI hfd := mwb1_fd_adjoin N
  haveI hpd := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  letI eR := Polynomial.algEquivOfTranscendental (AlgebraicClosure ℚ)
    (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ht
  haveI hpir : IsPrincipalIdealRing (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) :=
    IsPrincipalIdealRing.of_surjective eR.toAlgHom.toRingHom eR.surjective
  have hRnf : ¬IsField (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) := fun h =>
    Ideal.polynomial_not_isField (R := AlgebraicClosure ℚ) (MulEquiv.isField h eR.toMulEquiv)
  haveI : CharZero (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))).injective
  have hFx : IsIntegral (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) x := IsIntegral.of_finite _ x
  have hFmem : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) :=
    IntermediateField.subset_adjoin _ _ rfl

  have coeff_mem : ∀ v : Place (AlgebraicClosure ℚ) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))),
      (⟨_, hFmem⟩ : (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))) ∈ v.toValuationSubring →
      ∀ i, (minpoly (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) x).coeff i ∈ v.toValuationSubring := by
    intro v hvt i
    have hord : ∀ w ∈ v.fiber (modularFunctionFieldBar N), 0 ≤ w.ord x := by
      intro w hw
      rw [Place.fiber_eq_fiberOver, Place.mem_fiberOver] at hw
      have hjw : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ w.toValuationSubring := by
        have h1 := hw ▸ hvt
        exact ValuationSubring.mem_comap.mp h1
      exact mwb1_ord_nonneg_of_mem w hx
        (hreg w (mwb1_ne_cuspInfty_of_jelt_mem N hjw))
    obtain ⟨c, hc⟩ := AlgebraicCurve.Place.exists_integralClosureAt_of_ord_fiber_nonneg
      (v := v) hx hord
    have hint : IsIntegral v.toValuationSubring x := by
      rw [← hc]
      exact c.2
    letI : Algebra v.toValuationSubring (modularFunctionFieldBar N) :=
      ((algebraMap (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)).comp
        (algebraMap v.toValuationSubring (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))))).toAlgebra
    haveI : IsScalarTower v.toValuationSubring (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) :=
      IsScalarTower.of_algebraMap_eq' rfl
    have heq := minpoly.isIntegrallyClosed_eq_field_fractions' (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) hint
    rw [heq, Polynomial.coeff_map]
    exact SetLike.coe_mem _

  have hc : ∀ i, (minpoly (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) x).coeff i ∈
      (Set.range (algebraMap (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))))) := by
    intro i
    have hbot : (minpoly (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) x).coeff i ∈ (⊥ : Subalgebra (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))) := by
      rw [← MaximalSpectrum.iInf_localization_eq_bot (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))), Algebra.mem_iInf]
      intro P
      have hPb : P.asIdeal ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField P.isMaximal hRnf
      let hw : IsDedekindDomain.HeightOneSpectrum (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) :=
        ⟨P.asIdeal, P.isMaximal.isPrime, hPb⟩
      have hvt : (⟨_, hFmem⟩ : (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))) ∈
          (AlgebraicCurve.Place.ofHeightOneSpectrum (K := AlgebraicClosure ℚ)
            (F := (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))) hw).toValuationSubring := by
        rw [AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring]
        have h2 : (⟨_, hFmem⟩ : (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))))
            = algebraMap (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) ⟨_, Algebra.self_mem_adjoin_singleton _ _⟩ := rfl
        rw [Valuation.mem_valuationSubring_iff, h2]
        exact hw.valuation_le_one _
      have hm := coeff_mem _ hvt i
      rw [AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring,
        ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
        at hm
      have hm2 : (minpoly _ x).coeff i
          ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime _ hw).toSubring := hm
      rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring,
        Subalgebra.mem_toSubring] at hm2
      exact hm2
    rw [Algebra.mem_bot] at hbot
    exact hbot

  obtain ⟨Q, hQmap, -, hQmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts _).mpr hc) (minpoly.monic hFx)
  refine ⟨Q, hQmonic, ?_⟩
  have h0 : Polynomial.aeval x (minpoly (IntermediateField.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) x) = 0 := minpoly.aeval _ x
  rw [← hQmap] at h0
  rwa [Polynomial.aeval_map_algebraMap] at h0

open Real in

private theorem mwb1_exists_evalAt_ne_zero (N : ℕ) [NeZero N] {r : ℕ}
    {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hrat : w.IsRational)
    (hw : ∀ i, s i ∈ w.toValuationSubring) :
    ∃ i, w.evalAt (s i) ≠ 0 := by
  classical
  by_contra hall
  push Not at hall
  have h1mem : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
    rw [AlgebraicCurve.mem_riemannRochSpace_iff]
    intro v
    refine Or.inr ?_
    rw [Place.ord_one, ModularCurve.embDivisor]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, neg_nonpos]
    split_ifs
    · positivity
    · simp
  rw [← hs.2] at h1mem
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp h1mem
  have hmem1 : (1 : modularFunctionFieldBar N) ∈ w.toValuationSubring := one_mem _
  have hsum : (⟨1, hmem1⟩ : w.toValuationSubring)
      = ∑ i ∈ c.support, (⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c i),
          w.algebraMap_mem' _⟩ : w.toValuationSubring) * ⟨s i, hw i⟩ := by
    refine Subtype.ext ?_
    push_cast
    rw [← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
  have h1 := congrArg (mwb1_psi w hrat) hsum
  rw [map_sum] at h1
  have hzero : ∀ i ∈ c.support,
      mwb1_psi w hrat ((⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (c i),
        w.algebraMap_mem' _⟩ : w.toValuationSubring) * ⟨s i, hw i⟩) = 0 := by
    intro i _
    rw [map_mul, mwb1_psi_eq_evalAt w hrat (hw i), hall i, mul_zero]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at h1
  have h2 : mwb1_psi w hrat ⟨1, hmem1⟩ = 1 := by
    rw [mwb1_psi_eq_evalAt w hrat hmem1]
    exact AlgebraicCurve.Place.evalAt_one w
  rw [h2] at h1
  exact one_ne_zero h1

private theorem mwb1_pivot_facts (N : ℕ) [NeZero N] {r : ℕ}
    {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hrat : w.IsRational)
    (hw : ∀ i, s i ∈ w.toValuationSubring) (hr : 0 < r) :
    w.evalAt (s (pivotIndex s w hr)) ≠ 0 := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i₀, hi₀⟩ := mwb1_exists_evalAt_ne_zero N hs hrat hw
  have hne : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hnn : ∀ i, 0 ≤ w.ord (s i) := fun i => mwb1_ord_nonneg_of_mem w (hne i) (hw i)
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) :=
    Finite.exists_min fun i => w.ord (s i)
  have hpiv : ∀ j : Fin r, w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
    rw [AlgebraicCurve.pivotIndex, dif_pos hex]
    exact Classical.choose_spec hex
  have hi₀ord : w.ord (s i₀) = 0 := by
    rcases lt_or_eq_of_le (hnn i₀) with hpos | heq
    · exact absurd ((mwb1_psi_eq_evalAt w hrat (hw i₀)).symm.trans
        ((mwb1_psi_zero_iff w hrat _).mpr
          (mwb1_adicValuation_lt_one_of_ord_pos w hpos))) hi₀
    · exact heq.symm
  have hpord : w.ord (s (pivotIndex s w hr)) = 0 :=
    le_antisymm (hi₀ord ▸ hpiv i₀) (hnn _)
  exact AlgebraicCurve.Place.evalAt_ne_zero w hrat (hne _) hpord

open Real in

set_option synthInstance.maxHeartbeats 800000 in

private theorem mwb1_pointHt_eq (N : ℕ) [NeZero N] {r : ℕ}
    {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s)
    {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hrat : w.IsRational)
    (hw : ∀ i, s i ∈ w.toValuationSubring) (hr : 0 < r) :
    pointHt s w = absLogHeight (fun i => w.evalAt (s i)) := by
  classical
  have hne : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hpne := mwb1_pivot_facts N hs hrat hw hr
  have hpiv : ∀ j : Fin r, w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
    have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) :=
      haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
      Finite.exists_min fun i => w.ord (s i)
    rw [AlgebraicCurve.pivotIndex, dif_pos hex]
    exact Classical.choose_spec hex
  have hmemu : ∀ i, s i * (s (pivotIndex s w hr))⁻¹ ∈ w.toValuationSubring := by
    intro i
    have hprod : s i * (s (pivotIndex s w hr))⁻¹ ≠ 0 :=
      mul_ne_zero (hne i) (inv_ne_zero (hne _))
    refine mwb1_mem_of_ord_nonneg w hprod ?_
    rw [w.ord_mul (hne i) (inv_ne_zero (hne _)), Place.ord_inv]
    have := hpiv i
    omega
  have htup : evalVec s w = fun i =>
      (w.evalAt (s (pivotIndex s w hr)))⁻¹ * w.evalAt (s i) := by
    funext i
    show (if hr' : 0 < r then
        w.evalAt (s i * (s (pivotIndex s w hr'))⁻¹) else 0) = _
    rw [dif_pos hr]
    have harg : s i * (s (pivotIndex s w hr))⁻¹ * s (pivotIndex s w hr) = s i :=
      inv_mul_cancel_right₀ (hne _) _
    have hmul : w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) * w.evalAt (s (pivotIndex s w hr))
        = w.evalAt (s i) := by
      rw [← AlgebraicCurve.Place.evalAt_mul w hrat (hmemu i) (hw _), harg]
    refine mul_left_cancel₀ hpne ?_
    rw [mul_inv_cancel_left₀ hpne, mul_comm, hmul]

  have halg : ∀ z : AlgebraicClosure ℚ, IsIntegral ℚ z := fun z =>
    ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  haveI hfdL : FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ (Set.range fun i => w.evalAt (s i))) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => halg z
  have hmemL : ∀ i, w.evalAt (s i)
      ∈ IntermediateField.adjoin ℚ (Set.range fun i => w.evalAt (s i)) := fun i =>
    IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩
  have hmempL : w.evalAt (s (pivotIndex s w hr))
      ∈ IntermediateField.adjoin ℚ (Set.range fun i => w.evalAt (s i)) := hmemL _
  have hmemVL : ∀ i, (w.evalAt (s (pivotIndex s w hr)))⁻¹ * w.evalAt (s i)
      ∈ IntermediateField.adjoin ℚ (Set.range fun i => w.evalAt (s i)) := fun i =>
    mul_mem (inv_mem hmempL) (hmemL i)
  rw [show pointHt s w = absLogHeight (evalVec s w) from rfl, htup,
    AlgebraicCurve.absLogHeight_eq_of_mem _ _ hmemVL,
    AlgebraicCurve.absLogHeight_eq_of_mem _ _ hmemL]
  congr 1
  have hsc : (fun i => (⟨(w.evalAt (s (pivotIndex s w hr)))⁻¹ * w.evalAt (s i),
      hmemVL i⟩ : IntermediateField.adjoin ℚ (Set.range fun i => w.evalAt (s i))))
      = (⟨w.evalAt (s (pivotIndex s w hr)), hmempL⟩ :
          IntermediateField.adjoin ℚ (Set.range fun i => w.evalAt (s i)))⁻¹
        • fun i => (⟨w.evalAt (s i), hmemL i⟩ :
          IntermediateField.adjoin ℚ (Set.range fun i => w.evalAt (s i))) := by
    funext i
    refine Subtype.ext ?_
    push_cast
    rfl
  rw [hsc]
  refine Height.logHeight_smul_eq_logHeight _ ?_
  simp only [ne_eq, inv_eq_zero]
  intro hz
  exact hpne (by simpa using congrArg Subtype.val hz)

open Real in

private theorem mwb1_value_root (N : ℕ) [NeZero N] {r : ℕ}
    {s : Fin r → modularFunctionFieldBar N} (hs : IsEmbBasis N s) (i : Fin r) :
    ∃ (d : ℕ) (P : Fin (d + 1) → Polynomial (AlgebraicClosure ℚ)),
      ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        0 ≤ w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) →
        absLogHeight ![w.evalAt (s i), 1]
          ≤ absLogHeight (fun k : Fin (d + 1) => (P k).eval (jCoord N w))
            + Real.log (Real.sqrt (d + 1)) := by
  classical
  have ht := mwb1_jelt_transcendental N
  have hjne : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ≠ 0 := fun h0 => ht (h0 ▸ isAlgebraic_zero)
  have hreg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      w ≠ cuspInftyBar N → s i ∈ w.toValuationSubring :=
    fun w hw => mwb1_s_regular N hs i hw
  obtain ⟨Q, hQmonic, hQ0⟩ := mwb1_isIntegral_adjoin N (hs.1.ne_zero i) hreg
  letI eR := Polynomial.algEquivOfTranscendental (AlgebraicClosure ℚ)
    (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ht
  refine ⟨Q.natDegree, fun k => eR.symm (Q.coeff (k : ℕ)), ?_⟩
  intro w hword
  have hrat := mwb1_isRational N w
  have hmemj : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ w.toValuationSubring :=
    mwb1_mem_of_ord_nonneg w hjne hword

  have hmemc : ∀ a : Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)),
      (a : modularFunctionFieldBar N) ∈ w.toValuationSubring :=
    fun a => mwb1_adjoin_mem N hmemj a.2
  letI ρ₀ := (Subalgebra.val (Algebra.adjoin (AlgebraicClosure ℚ)
    ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))).toRingHom.codRestrict w.toValuationSubring hmemc
  letI ρw := (mwb1_psi w hrat).comp ρ₀
  have hχmonic : (Q.map ρw).Monic := hQmonic.map ρw
  have hχdeg : (Q.map ρw).natDegree = Q.natDegree := hQmonic.natDegree_map ρw

  have hsub0 : Polynomial.eval₂ ρ₀ (⟨s i, hreg w (mwb1_ne_cuspInfty_of_jelt_mem N hmemj)⟩ :
      w.toValuationSubring) Q = 0 := by
    have hcomp : (w.toValuationSubring.subtype).comp ρ₀
        = algebraMap (Algebra.adjoin (AlgebraicClosure ℚ) ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
            (modularFunctionFieldBar N) := rfl
    have h1 : w.toValuationSubring.subtype (Polynomial.eval₂ ρ₀
        (⟨s i, hreg w (mwb1_ne_cuspInfty_of_jelt_mem N hmemj)⟩ : w.toValuationSubring) Q)
        = 0 := by
      rw [Polynomial.hom_eval₂, hcomp]
      exact hQ0
    exact Subtype.ext h1
  have hroot : (Q.map ρw).eval (w.evalAt (s i)) = 0 := by
    rw [Polynomial.eval_map]
    have hsi : w.evalAt (s i)
        = mwb1_psi w hrat (⟨s i, hreg w (mwb1_ne_cuspInfty_of_jelt_mem N hmemj)⟩ :
            w.toValuationSubring) :=
      (mwb1_psi_eq_evalAt w hrat _).symm
    rw [hsi]
    show Polynomial.eval₂ ((mwb1_psi w hrat).comp ρ₀) _ Q = 0
    rw [← Polynomial.hom_eval₂, hsub0, map_zero]

  have hcoeff : ∀ k : Fin (Q.natDegree + 1),
      (Q.map ρw).coeff (k : ℕ) = (eR.symm (Q.coeff (k : ℕ))).eval (jCoord N w) := by
    intro k
    rw [Polynomial.coeff_map]
    have h1 : ρw (Q.coeff (k : ℕ)) = w.evalAt ((Q.coeff (k : ℕ) :
        modularFunctionFieldBar N)) := by
      show mwb1_psi w hrat (ρ₀ (Q.coeff (k : ℕ))) = _
      exact mwb1_psi_eq_evalAt w hrat _
    have h2 : ((Q.coeff (k : ℕ)) : modularFunctionFieldBar N)
        = Polynomial.aeval
            (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
            (eR.symm (Q.coeff (k : ℕ))) := by
      have h3 := eR.apply_symm_apply (Q.coeff (k : ℕ))
      have h4 : Polynomial.aeval
          (⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N),
            Algebra.self_mem_adjoin_singleton _ _⟩ : Algebra.adjoin (AlgebraicClosure ℚ)
              ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
          (eR.symm (Q.coeff (k : ℕ))) = Q.coeff (k : ℕ) := h3
      calc ((Q.coeff (k : ℕ)) : modularFunctionFieldBar N)
          = ((Polynomial.aeval
              (⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N),
                Algebra.self_mem_adjoin_singleton _ _⟩ : Algebra.adjoin (AlgebraicClosure ℚ)
                  ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
              (eR.symm (Q.coeff (k : ℕ)))) : modularFunctionFieldBar N) := by rw [h4]
        _ = Polynomial.aeval
              (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
              (eR.symm (Q.coeff (k : ℕ))) :=
            (Polynomial.aeval_algHom_apply
              (Subalgebra.val (Algebra.adjoin (AlgebraicClosure ℚ)
                ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))))
              (⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N),
                Algebra.self_mem_adjoin_singleton _ _⟩ : Algebra.adjoin (AlgebraicClosure ℚ)
                  ({(⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
              (eR.symm (Q.coeff (k : ℕ)))).symm
    rw [h1, h2, mwb1_evalAt_aeval N hrat hmemj, mwb1_evalAt_jelt N hword]

  have hle := mwb1_root_ht hχmonic hroot
  rw [hχdeg] at hle
  refine hle.trans (le_of_eq ?_)
  congr 1
  congr 1
  funext k
  exact hcoeff k

private theorem mwb1_perpoint (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (_hs : IsEmbBasis N s) :
    ∃ Bs Cs : ℝ, 0 ≤ Bs ∧ 0 ≤ Cs ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) →
        pointHt s v ≤ Bs * absLogHeight ![jCoord N v, 1] + Cs := by
  classical
  choose d P hdP using fun i => mwb1_value_root N _hs i
  have hBC : ∀ i, ∀ k : Fin (d i + 1), ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ a : AlgebraicClosure ℚ,
        absLogHeight ![(P i k).eval a, 1] ≤ B * absLogHeight ![a, 1] + C :=
    fun i k => mwb1_eval_ht (P i k)
  choose B C hB0 hC0 hBCle using hBC
  refine ⟨∑ i, ∑ k, B i k,
    ∑ i, ((∑ k, C i k) + Real.log (Real.sqrt (d i + 1))), ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hB0 i k
  · refine Finset.sum_nonneg fun i _ =>
      add_nonneg (Finset.sum_nonneg fun k _ => hC0 i k) ?_
    refine Real.log_nonneg (Real.one_le_sqrt.mpr ?_)
    linarith
  intro v hvord
  have hrat := mwb1_isRational N v
  have htj := mwb1_jelt_transcendental N
  have hjne : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ≠ 0 :=
    fun h0 => htj (h0 ▸ isAlgebraic_zero)
  have hmemj := mwb1_mem_of_ord_nonneg v hjne hvord
  have hvne := mwb1_ne_cuspInfty_of_jelt_mem N hmemj
  have hw : ∀ i, s i ∈ v.toValuationSubring := fun i => mwb1_s_regular N _hs i hvne
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  ·
    subst hr0
    have hpt : pointHt s v = 0 := by
      show absLogHeight (evalVec s v) = 0
      show (Module.finrank ℚ _ : ℝ)⁻¹ * Height.logHeight _ = 0
      rw [show (fun i : Fin 0 => (⟨evalVec s v i, _⟩ :
          IntermediateField.adjoin ℚ (Set.range (evalVec s v)))) = 0
        from funext fun i => i.elim0]
      rw [Height.logHeight_zero, mul_zero]
    rw [hpt, Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty, zero_mul, add_zero]
  ·
    rw [mwb1_pointHt_eq N _hs hrat hw hr]
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr).symm⟩
    calc absLogHeight (fun i => v.evalAt (s i))
        ≤ ∑ i, absLogHeight ![v.evalAt (s i), 1] := mwb1_absHt_le_sum _
      _ ≤ ∑ i, (absLogHeight (fun k : Fin (d i + 1) => (P i k).eval (jCoord N v))
            + Real.log (Real.sqrt (d i + 1))) :=
          Finset.sum_le_sum fun i _ => hdP i v hvord
      _ ≤ ∑ i, ((∑ k, absLogHeight ![(P i k).eval (jCoord N v), 1])
            + Real.log (Real.sqrt (d i + 1))) :=
          Finset.sum_le_sum fun i _ => add_le_add_left (mwb1_absHt_le_sum _) _
      _ ≤ ∑ i, ((∑ k, (B i k * absLogHeight ![jCoord N v, 1] + C i k))
            + Real.log (Real.sqrt (d i + 1))) :=
          Finset.sum_le_sum fun i _ => add_le_add_left
            (Finset.sum_le_sum fun k _ => hBCle i k _) _
      _ = (∑ i, ∑ k, B i k) * absLogHeight ![jCoord N v, 1]
            + ∑ i, ((∑ k, C i k) + Real.log (Real.sqrt (d i + 1))) := by
          have hsplit : ∀ i : Fin (m + 1),
              ((∑ k, (B i k * absLogHeight ![jCoord N v, 1] + C i k))
                + Real.log (Real.sqrt (d i + 1)))
              = (∑ k, B i k) * absLogHeight ![jCoord N v, 1]
                + ((∑ k, C i k) + Real.log (Real.sqrt (d i + 1))) := by
            intro i
            rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
            ← Finset.sum_mul]

end MWB1

open ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord.AlgebraicCurve in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ Bs Cs : ℝ, 0 ≤ Bs ∧ 0 ≤ Cs ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) →
        pointHt s v ≤ Bs * absLogHeight ![jCoord N v, 1] + Cs :=
  MWB1.mwb1_perpoint N s hs

end S_ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord
end P2MW
export P2MW.S_ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord (solution)
