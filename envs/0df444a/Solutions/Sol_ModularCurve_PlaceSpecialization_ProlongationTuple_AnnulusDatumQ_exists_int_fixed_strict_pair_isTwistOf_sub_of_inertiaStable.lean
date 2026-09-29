-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.exists_int_fixed_strict_pair_isTwistOf_sub_of_inertiaStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/826afae5-ccf3-570f-a538-3318a742cd52

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
import Theorems.Thm_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_int_fixed_strict_pair_isTwistOf_sub_of_inertiaStable
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero"
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

namespace OrbitClass

def chainRec (r : ℕ → ℤ) (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => t
  | (d + 2) => 2 * chainRec r t (d + 1) - chainRec r t d - r (d + 1)

theorem chainRec_zero (r : ℕ → ℤ) (t : ℤ) : chainRec r t 0 = 0 := rfl
theorem chainRec_one (r : ℕ → ℤ) (t : ℤ) : chainRec r t 1 = t := rfl
theorem chainRec_succ_succ (r : ℕ → ℤ) (t : ℤ) (d : ℕ) :
    chainRec r t (d + 2) = 2 * chainRec r t (d + 1) - chainRec r t d - r (d + 1) := rfl

theorem chainRec_laplace (r : ℕ → ℤ) (t : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    chainRec r t (d - 1) - 2 * chainRec r t d + chainRec r t (d + 1) = - r d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, show e + 1 + 1 = e + 2 from rfl, chainRec_succ_succ]
  ring

theorem chainRec_eq (r : ℕ → ℤ) (t : ℤ) (d : ℕ) : chainRec r t d = d * t + chainRec r 0 d := by
  induction d using Nat.twoStepInduction with
  | zero => simp [chainRec_zero]
  | one => simp [chainRec_one]
  | more d ih0 ih1 =>
    rw [chainRec_succ_succ, chainRec_succ_succ, ih0, ih1]
    push_cast
    ring

theorem exists_dirichlet {ι : Type*} [Finite ι] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i)
    (hcop : Pairwise fun i j => (n i).Coprime (n j)) (r : ι → ℕ → ℤ) :
    ∃ (Z : ℤ) (c : ι → ℕ → ℤ), (∀ i, c i 0 = 0) ∧ (∀ i d, n i ≤ d → c i d = Z) ∧
      ∀ i d, 1 ≤ d → d + 1 ≤ n i → c i (d - 1) - 2 * c i d + c i (d + 1) = - r i d := by
  classical

  have hcopI : Pairwise fun i j => IsCoprime (Ideal.span {(n i : ℤ)}) (Ideal.span {(n j : ℤ)}) := by
    intro i j hij
    rw [Ideal.isCoprime_span_singleton_iff]
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using hcop hij)
  obtain ⟨Z, hZ⟩ := Ideal.exists_forall_sub_mem_ideal hcopI (fun i => chainRec (r i) 0 (n i))

  have hdiv : ∀ i, (n i : ℤ) ∣ Z - chainRec (r i) 0 (n i) := fun i =>
    Ideal.mem_span_singleton.mp (hZ i)
  choose t ht using hdiv
  refine ⟨Z, fun i d => if n i ≤ d then Z else chainRec (r i) (t i) d, ?_, ?_, ?_⟩
  · intro i
    have : ¬ n i ≤ 0 := by have := hn i; omega
    simp [this, chainRec_zero]
  · intro i d hd
    simp [hd]
  · intro i d hd1 hd2
    have hend : chainRec (r i) (t i) (n i) = Z := by
      rw [chainRec_eq]
      have h := ht i
      linear_combination -h
    have h0 : ¬ n i ≤ d - 1 := by omega
    have h1 : ¬ n i ≤ d := by omega
    simp only [h0, h1, if_false]
    by_cases h2 : n i ≤ d + 1
    · have heq : d + 1 = n i := by omega
      rw [if_pos h2, ← hend, ← heq]
      exact chainRec_laplace (r i) (t i) d hd1
    · rw [if_neg h2]
      exact chainRec_laplace (r i) (t i) d hd1

theorem tent_sum (n : ℕ) (δ : ℚ) (h0 : 0 ≤ δ) (hn : δ ≤ n) :
    ∑ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) = 1 := by
  have hfl : (⌊δ⌋₊ : ℚ) ≤ δ := Nat.floor_le h0
  have hlt : δ < ⌊δ⌋₊ + 1 := Nat.lt_floor_add_one δ
  have hmn : ⌊δ⌋₊ ≤ n := Nat.floor_le_of_le (by exact_mod_cast hn)

  have hterm : ∀ d ∈ Finset.range (n + 1), max 0 (1 - |δ - (d : ℚ)|) =
      (if d = ⌊δ⌋₊ then 1 - (δ - ⌊δ⌋₊) else 0) + (if d = ⌊δ⌋₊ + 1 then δ - ⌊δ⌋₊ else 0) := by
    intro d _
    by_cases h1 : d = ⌊δ⌋₊
    · subst h1
      have h2 : ¬ (⌊δ⌋₊ = ⌊δ⌋₊ + 1) := by omega
      rw [if_pos rfl, if_neg h2, add_zero, abs_of_nonneg (by linarith)]
      exact max_eq_right (by linarith)
    · rw [if_neg h1, zero_add]
      by_cases h2 : d = ⌊δ⌋₊ + 1
      · subst h2
        rw [if_pos rfl, abs_of_nonpos (by push_cast; linarith)]
        push_cast
        rw [max_eq_right (by linarith)]
        ring
      · rw [if_neg h2]
        apply max_eq_left

        rcases Nat.lt_or_gt_of_ne h1 with h | h
        ·
          have : (d : ℚ) + 1 ≤ ⌊δ⌋₊ := by exact_mod_cast h
          rw [abs_of_nonneg (by linarith)]
          linarith
        ·
          have : (⌊δ⌋₊ : ℚ) + 2 ≤ d := by exact_mod_cast (show ⌊δ⌋₊ + 2 ≤ d by omega)
          rw [abs_of_nonpos (by linarith)]
          linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' , Finset.sum_ite_eq']
  have hm : ⌊δ⌋₊ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [if_pos hm]
  by_cases hm1 : ⌊δ⌋₊ + 1 ∈ Finset.range (n + 1)
  · rw [if_pos hm1]; ring
  · rw [if_neg hm1, add_zero]

    have h3 : ⌊δ⌋₊ = n := by rw [Finset.mem_range] at hm1; omega
    have h4 : δ = n := le_antisymm hn (by rw [← h3]; exact hfl)
    rw [h4]; simp

end OrbitClass

namespace OrbitClass

theorem sum_laplace_Ico (f : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Ico 1 n, (f (d - 1) - 2 * f d + f (d + 1)) = f 0 - f 1 - f (n - 1) + f n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega), ih hm]
      obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

omit [PerfectField k] in
theorem not_isStrictSnd_of_isStrictFst {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h1 : P.IsStrictFst V) : ¬ P.IsStrictSnd V := fun h2 =>
  h1.2 (by rw [h1.1, ← h2.1])

theorem injOn_evalAt_of_ssPlaces [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∀ w₁ ∈ W, ∀ w₂ ∈ W, w₁.evalAt (jGeomGen k 1) = w₂.evalAt (jGeomGen k 1) → w₁ = w₂ := by
  obtain ⟨W', τ, hW', hτ⟩ := exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq q k
    (ssJSet_finite q k).toFinset (fun j => Set.Finite.mem_toFinset _)
  have hWW : W' = W := Finset.ext fun w => (hW' w).trans (hW w).symm
  subst hWW
  intro w₁ hw₁ w₂ hw₂ h12
  obtain ⟨a₁, ha₁⟩ := τ.surjective ⟨w₁, hw₁⟩
  obtain ⟨a₂, ha₂⟩ := τ.surjective ⟨w₂, hw₂⟩
  have h1 := hτ a₁
  have h2 := hτ a₂
  rw [ha₁] at h1
  rw [ha₂] at h2
  have ha : a₁ = a₂ := by
    apply Subtype.ext
    rw [← h1, ← h2]
    exact h12
  subst ha
  exact Subtype.ext_iff.mp (ha₁.symm.trans ha₂)

theorem coprime_jWidth {K : Type*} [Field K] [DecidableEq K] {j₁ j₂ : K} (h : j₁ ≠ j₂) :
    (jWidth j₁).Coprime (jWidth j₂) := by
  have hv : ∀ j : K, jWidth j = 1 ∨ (j = 0 ∧ jWidth j = 3) ∨ (j = 1728 ∧ jWidth j = 2) := by
    intro j; unfold jWidth; split_ifs with h0 h1 <;> simp_all
  rcases hv j₁ with h1 | ⟨h10, h1⟩ | ⟨h11, h1⟩ <;> rcases hv j₂ with h2 | ⟨h20, h2⟩ | ⟨h21, h2⟩ <;>
    rw [h1, h2] <;> norm_num
  · exact h (h10.trans h20.symm)
  · exact h (h11.trans h21.symm)

theorem one_le_jWidth {K : Type*} [Field K] [DecidableEq K] (j : K) : 1 ≤ jWidth j := by
  unfold jWidth; split_ifs <;> omega

end OrbitClass

namespace OrbitClass

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} {R : ProlongationTuple P}
  {W : Finset (Place k (modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)

open Classical in

theorem circleDeg_eq_sum (D : (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) (w : Place k (modularFunctionFieldC k 1)) (d : ℕ)
    (T : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) (hT : D.support ⊆ T) :
    dat.circleDeg D w d = ∑ V ∈ T, if P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V then
      (D V : ℚ) * max 0 (1 - |dat.depthQ V - d|) else 0 := by
  classical
  unfold AnnulusDatumQ.circleDeg
  rw [Finset.sum_filter]
  apply Finset.sum_subset hT
  intro V _ hV
  rw [Finsupp.notMem_support_iff.mp hV]
  simp

theorem circleDeg_congr {D D' : (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))}
    (h : ∀ V, ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → D V = D' V)
    (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) :
    dat.circleDeg D w d = dat.circleDeg D' w d := by
  classical
  rw [circleDeg_eq_sum dat D w d (D.support ∪ D'.support) Finset.subset_union_left,
    circleDeg_eq_sum dat D' w d (D.support ∪ D'.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun V _ => ?_
  split_ifs with hc
  · rw [h V hc.2.1 hc.2.2]
  · rfl

omit [PerfectField k] in

theorem degree_eq_sum_support (D : (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) : Divisor.degree D = ∑ V ∈ D.support, D V := by
  classical
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]
  simp

omit [PerfectField k] in
theorem degree_filter (D : (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop)
    [DecidablePred p] : Divisor.degree (D.filter p) = ∑ V ∈ D.support with p V, D V := by
  classical
  rw [degree_eq_sum_support, Finsupp.support_filter]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finsupp.filter_apply_pos]
  exact (Finset.mem_filter.mp hV).2

open Classical in
omit [PerfectField k] in

theorem degree_decomp (D : (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))))
    (hgood : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) :
    Divisor.degree D = Divisor.degree (P.fstDiv D) + Divisor.degree (P.sndDiv D) +
      ∑ w ∈ W, ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V := by
  classical
  have hF : Divisor.degree (P.fstDiv D) = ∑ V ∈ D.support with P.IsStrictFst V, D V := by
    unfold PlaceSpecialization.fstDiv; convert degree_filter D P.IsStrictFst
  have hS : Divisor.degree (P.sndDiv D) = ∑ V ∈ D.support with P.IsStrictSnd V, D V := by
    unfold PlaceSpecialization.sndDiv; convert degree_filter D P.IsStrictSnd
  rw [hF, hS, degree_eq_sum_support]
  have step1 := (Finset.sum_filter_add_sum_filter_not D.support P.IsStrictFst (fun V => D V)).symm
  have step2 := (Finset.sum_filter_add_sum_filter_not (D.support.filter fun V => ¬ P.IsStrictFst V)
    P.IsStrictSnd (fun V => D V)).symm
  rw [step1, step2, Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  · refine Finset.sum_congr (Finset.filter_congr fun V _ => ?_) fun _ _ => rfl
    exact ⟨fun h => h.2, fun h => ⟨fun h1 => not_isStrictSnd_of_isStrictFst P h1 h, h⟩⟩
  · rw [← Finset.sum_fiberwise_of_maps_to (s := D.support.filter fun V => ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
      (t := W) (g := P.reduceFst) (f := fun V => D V) ?_]
    · refine Finset.sum_congr rfl fun w _ => Finset.sum_congr ?_ fun _ _ => rfl
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun V _ => by tauto
    · intro V hV
      rw [Finset.mem_filter] at hV
      rcases hgood V hV.1 with h | h | h
      · exact absurd h hV.2.1
      · exact absurd h hV.2.2
      · exact h

end OrbitClass

open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumQ W)
    (hwidth : ∀ w ∈ W, 1 ≤ dat.width w)

    (hwidthj : ∀ w ∈ W, dat.width w = jWidth (w.evalAt (jGeomGen k 1)))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)

    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)

    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
        (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        dat.depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = dat.depthQ V)
    (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hEstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ •
          (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) = E)
    (hEsupp : ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
        P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (B : Finset (Place k (modularFunctionFieldC k 1))) :
    ∃ (c : ℤ) (P₁ P₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      P.IsStrictFst P₁ ∧ P.IsStrictSnd P₂ ∧ P.reduceFst P₁ ∉ B ∧ P.reduceSnd P₂ ∉ B ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • P₁ = P₁) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • P₂ = P₂) ∧
      ∃ a : ProlongationTuple.TwistVector (k := k) W,
        dat.IsTwistOf a ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) -
            c • (Finsupp.single P₂ 1 - Finsupp.single P₁ 1)) := by
  classical
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  set Xd : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) with hXd

  have hint : ∀ w ∈ W, ∀ d : ℕ, (dat.circleDeg Xd w d).den = 1 :=
    (ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable
      hq5 P hW R hR hRL hNV hO dat hwidth hwidthj hVI hKfix hdepthQ hdepthσ E hEstab hEsupp).1

  have hXdepth : ∀ V ∈ Xd.support, ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width (P.reduceFst V) := by
    intro V hV h1 h2
    have hw : P.reduceFst V ∈ W := by
      rcases hEsupp V hV with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    obtain ⟨h0, hlt, -⟩ := hdepthQ (P.reduceFst V) hw V rfl h1 h2
    exact ⟨h0, hlt⟩

  have hw1 : ∀ w : ↥W, 1 ≤ dat.width w.1 := fun w => hwidth w.1 w.2
  have hcop : Pairwise fun (w₁ w₂ : ↥W) => (dat.width w₁.1).Coprime (dat.width w₂.1) := by
    intro w₁ w₂ hne
    rw [hwidthj w₁.1 w₁.2, hwidthj w₂.1 w₂.2]
    apply OrbitClass.coprime_jWidth
    intro h
    exact hne (Subtype.ext (OrbitClass.injOn_evalAt_of_ssPlaces W hW w₁.1 w₁.2 w₂.1 w₂.2 h))

  set r : ↥W → ℕ → ℤ := fun w d => (dat.circleDeg Xd w.1 d).num with hr
  have hrq : ∀ (w : ↥W) (d : ℕ), (r w d : ℚ) = dat.circleDeg Xd w.1 d := fun w d =>
    Rat.coe_int_num_of_den_eq_one (hint w.1 w.2 d)

  obtain ⟨Z, c, hc0, hcZ, hclap⟩ := OrbitClass.exists_dirichlet (fun w : ↥W => dat.width w.1) hw1 hcop r

  let a : TwistVector (k := k) W := ⟨0, Z, fun w d => if hw : w ∈ W then c ⟨w, hw⟩ d else 0⟩
  have hchain : ∀ (w : ↥W) (d : ℕ), dat.chainVal a w.1 d = c w d := by
    intro w d
    unfold AnnulusDatumQ.chainVal
    by_cases hd0 : d = 0
    · rw [if_pos hd0, hd0, hc0]
    · rw [if_neg hd0]
      by_cases hdw : dat.width w.1 ≤ d
      · rw [if_pos hdw, hcZ w d hdw]
      · rw [if_neg hdw]
        show (if hw : w.1 ∈ W then c ⟨w.1, hw⟩ d else 0) = c w d
        rw [dif_pos w.2]

  obtain ⟨Q₁, Q₂, hQ₁s, hQ₂s, -, -, hQ₁B, hQ₂B, hQ₁fix, hQ₂fix⟩ :=
    exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq P B 1 1
  have hV₁s : P.IsStrictFst (Q₁ 0) := hQ₁s 0
  have hV₂s : P.IsStrictSnd (Q₂ 0) := hQ₂s 0
  set V₁ := Q₁ 0 with hV₁
  set V₂ := Q₂ 0 with hV₂

  set m : ℤ := -(Divisor.degree (P.fstDiv Xd)) - ∑ w ∈ W, dat.endOrderFst a Xd w with hm
  refine ⟨m, V₁, V₂, hV₁s, hV₂s, hQ₁B 0, hQ₂B 0, hQ₁fix 0, hQ₂fix 0, a, ?_⟩
  ·
    show dat.IsTwistOf a (Xd - m • (Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1))
    set D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
      Xd - m • (Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1) with hD
    have hnF2 : ¬ P.IsStrictFst V₂ := fun h => OrbitClass.not_isStrictSnd_of_isStrictFst P h hV₂s
    have hnS1 : ¬ P.IsStrictSnd V₁ := OrbitClass.not_isStrictSnd_of_isStrictFst P hV₁s

    have hF1 : ∀ V, ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → D V = Xd V := by
      intro V h1 h2
      have hV1 : V₁ ≠ V := fun h => h1 (h ▸ hV₁s)
      have hV2 : V₂ ≠ V := fun h => h2 (h ▸ hV₂s)
      simp [hD, hV1, hV2]
    have hF2 : ∀ w d, dat.circleDeg D w d = dat.circleDeg Xd w d := fun w d => OrbitClass.circleDeg_congr dat hF1 w d
    have hshF : ∀ w, dat.endShareFst D w = dat.endShareFst Xd w := fun w => by
      unfold AnnulusDatumQ.endShareFst; rw [hF2]
    have hshS : ∀ w, dat.endShareSnd D w = dat.endShareSnd Xd w := fun w => by
      unfold AnnulusDatumQ.endShareSnd; rw [hF2]
    have hoF : ∀ w, dat.endOrderFst a D w = dat.endOrderFst a Xd w := fun w => by
      unfold AnnulusDatumQ.endOrderFst; rw [hshF]
    have hoS : ∀ w, dat.endOrderSnd a D w = dat.endOrderSnd a Xd w := fun w => by
      unfold AnnulusDatumQ.endOrderSnd; rw [hshS]

    have hfst : P.fstDiv D = P.fstDiv Xd + m • Finsupp.single V₁ 1 := by
      unfold PlaceSpecialization.fstDiv
      rw [hD, Finsupp.filter_sub, Finsupp.filter_smul, Finsupp.filter_sub,
        Finsupp.filter_single_of_neg _ hnF2, Finsupp.filter_single_of_pos _ hV₁s, zero_sub, smul_neg, sub_neg_eq_add]
    have hsnd : P.sndDiv D = P.sndDiv Xd - m • Finsupp.single V₂ 1 := by
      unfold PlaceSpecialization.sndDiv
      rw [hD, Finsupp.filter_sub, Finsupp.filter_smul, Finsupp.filter_sub,
        Finsupp.filter_single_of_pos _ hV₂s, Finsupp.filter_single_of_neg _ hnS1, sub_zero]
    have hdegF : Divisor.degree (P.fstDiv D) = Divisor.degree (P.fstDiv Xd) + m := by
      rw [hfst, map_add, map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]; simp
    have hdegS : Divisor.degree (P.sndDiv D) = Divisor.degree (P.sndDiv Xd) - m := by
      rw [hsnd, map_sub, map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]; simp

    have E1 : Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endOrderFst a D w := by
      rw [hdegF, Finset.sum_congr rfl (fun w _ => hoF w), hm]; ring

    have E3 : ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
        dat.circleDeg D w d = -((dat.chainVal a w (d - 1) - 2 * dat.chainVal a w d + dat.chainVal a w (d + 1) : ℤ) : ℚ) := by
      intro w hw d hd1 hd2
      rw [hF2, ← hrq ⟨w, hw⟩ d, hchain ⟨w, hw⟩, hchain ⟨w, hw⟩, hchain ⟨w, hw⟩, hclap ⟨w, hw⟩ d hd1 hd2]
      push_cast; ring

    have hann : ∀ w ∈ W,
        ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ)
          = dat.endOrderFst a D w + dat.endOrderSnd a D w := by
      intro w hw
      have hn1 : 1 ≤ dat.width w := hw1 ⟨w, hw⟩

      have h1 : ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ)
          = ∑ d ∈ Finset.range (dat.width w + 1), dat.circleDeg D w d := by
        unfold AnnulusDatumQ.circleDeg
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun V hV => ?_
        obtain ⟨hVs, hVw, hV1, hV2⟩ := Finset.mem_filter.mp hV
        have hVX : V ∈ Xd.support := by
          rw [Finsupp.mem_support_iff, ← hF1 V hV1 hV2]; exact Finsupp.mem_support_iff.mp hVs
        obtain ⟨h0, hlt⟩ := hXdepth V hVX hV1 hV2
        rw [hVw] at hlt
        rw [← Finset.mul_sum, OrbitClass.tent_sum _ _ h0.le (by exact_mod_cast hlt.le), mul_one]

      have h2 : ∑ d ∈ Finset.range (dat.width w + 1), dat.circleDeg D w d
          = dat.circleDeg D w 0 + ∑ d ∈ Finset.Ico 1 (dat.width w), dat.circleDeg D w d + dat.circleDeg D w (dat.width w) := by
        rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn1]
      have h3 : dat.circleDeg D w 0 = dat.endShareFst D w := by
        unfold AnnulusDatumQ.endShareFst
        rw [hF2, if_pos (hint w hw 0)]
        exact_mod_cast (Rat.coe_int_num_of_den_eq_one (hint w hw 0)).symm
      have h4 : dat.circleDeg D w (dat.width w) = dat.endShareSnd D w := by
        unfold AnnulusDatumQ.endShareSnd
        rw [hF2, if_pos (hint w hw _)]
        exact_mod_cast (Rat.coe_int_num_of_den_eq_one (hint w hw _)).symm
      have h5 : ∑ d ∈ Finset.Ico 1 (dat.width w), dat.circleDeg D w d
          = (dat.endSlopeFst a w + dat.endSlopeSnd a w : ℤ) := by
        rw [Finset.sum_congr rfl (fun d hd => E3 w hw d (Finset.mem_Ico.mp hd).1
          (by have := (Finset.mem_Ico.mp hd).2; omega))]
        rw [Finset.sum_neg_distrib]
        have hL := congrArg (fun z : ℤ => (z : ℚ))
          (OrbitClass.sum_laplace_Ico (fun d => dat.chainVal a w d) (dat.width w) hn1)
        push_cast at hL ⊢
        rw [hL]
        unfold AnnulusDatumQ.endSlopeFst AnnulusDatumQ.endSlopeSnd
        push_cast; ring
      rw [h1, h2, h3, h4, h5]
      unfold AnnulusDatumQ.endOrderFst AnnulusDatumQ.endOrderSnd
      push_cast; ring

    have hdeg1 : Divisor.degree (m • (Finsupp.single V₂ (1 : ℤ) - Finsupp.single V₁ 1) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) = 0 := by
      rw [map_zsmul, map_sub, Divisor.degree_single, Divisor.degree_single,
        deg_eq_one_modularFunctionFieldBar, deg_eq_one_modularFunctionFieldBar]
      simp
    have hdeg0 : Divisor.degree D = 0 := by
      rw [hD, map_sub, hdeg1, sub_zero]
      exact Divisor.mem_degZero.mp E.2
    have hgoodD : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W := by
      intro V hV
      by_cases h1 : P.IsStrictFst V
      · exact Or.inl h1
      by_cases h2 : P.IsStrictSnd V
      · exact Or.inr (Or.inl h2)
      have hVX : V ∈ Xd.support := by
        rw [Finsupp.mem_support_iff, ← hF1 V h1 h2]; exact Finsupp.mem_support_iff.mp hV
      exact hEsupp V hVX
    have hdec := OrbitClass.degree_decomp (P := P) (W := W) D hgoodD
    have E2 : Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endOrderSnd a D w := by
      have hc := congrArg (fun z : ℤ => (z : ℚ)) hdec
      simp only [hdeg0] at hc
      push_cast at hc
      rw [Finset.sum_congr rfl (fun w hw => hann w hw), Finset.sum_add_distrib] at hc
      have hE1 := congrArg (fun z : ℤ => (z : ℚ)) E1
      push_cast at hE1
      have : (Divisor.degree (P.sndDiv D) : ℚ) = -∑ w ∈ W, (dat.endOrderSnd a D w : ℚ) := by linarith
      exact_mod_cast this
    exact ⟨E1, E2, E3⟩

end
end S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_int_fixed_strict_pair_isTwistOf_sub_of_inertiaStable
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_exists_int_fixed_strict_pair_isTwistOf_sub_of_inertiaStable (solution)
