-- Prove2me | solution 1 for OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:46:27.280617+00:00
-- url     : https://prove2.me/submissions/9a0184de-185b-4767-8905-91f0ddff0215

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A012
import Definitions.Def_OAIQ096A020
import Theorems.Thm_OAI_CubicFirstMoment_sieveExponent_four_thirds

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_finset_prod {α : Type*} (s : Finset α) (f : α → Eisenstein) :
    norm (∏ p ∈ s, f p) = ∏ p ∈ s, norm (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih => simp [hp, ih]

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeDivisorWeight_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Eisenstein, primary a → Squarefree a →
      (2 : ℝ)^(primaryPrimeFactors a).card ≤ C * norm a ^ ε := by
  let R : ℝ := (2 : ℝ)^(1/ε)
  let U : Finset Eisenstein := (finite_norm_le R).toFinset
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hε.ne', Real.rpow_one]
  refine ⟨(2 : ℝ)^U.card, by positivity, ?_⟩
  intro a ha hsa
  let P := primaryPrimeFactors a
  have hpoint : ∀ p ∈ P, (2 : ℝ) ≤ (if p ∈ U then 2 else 1) * norm p ^ ε := by
    intro p hp
    have hn1 := one_le_norm (primaryPrimeFactor_spec ha hp).1.2.ne_zero
    by_cases hpU : p ∈ U
    · simp only [ite_eq_left hpU]
      nlinarith [Real.one_le_rpow hn1 hε.le]
    · simp only [ite_eq_right hpU, one_mul]
      have hRp : R ≤ norm p := le_of_lt (not_le.mp (by
        intro he
        exact hpU (by simpa [U] using he)))
      rw [← hRe]
      exact Real.rpow_le_rpow hR.le hRp hε.le
  have hprod := Finset.prod_le_prod (s := P) (fun _ _ => (by norm_num : (0 : ℝ) ≤ 2)) hpoint
  rw [Finset.prod_const, Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ P, if p ∈ U then (2 : ℝ) else 1) ≤ (2 : ℝ)^U.card := by
    rw [Finset.prod_ite_mem, Finset.prod_const]
    exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Finset.inter_subset_right))
  have heq : (∏ p ∈ P, norm p ^ ε) = norm a ^ ε := by
    rw [Real.finsetProd_rpow P norm (fun p _ => norm_nonneg p), ← norm_finset_prod]
    rw [primaryPrimeFactors_prod ha hsa]
  rw [heq] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (norm_nonneg a) _))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic sieve operators, bilinear norms and coprime completion. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

open UniqueFactorizationMonoid

namespace CubicFirstMoment

lemma finiteCubicBound_nonneg (S H : Finset Eisenstein) : 0 ≤ finiteCubicBound S H :=
  sq_nonneg _

lemma finiteCubicOperator_apply (S H : Finset Eisenstein) (u : Eisenstein → ℂ)
    (h : H) :
    finiteCubicOperator S H (WithLp.toLp 2 (fun a : S => u a.val)) h =
      ∑ a ∈ S, u a * cubicSymbol a h.val := by
  change (∑ a : S, cubicSymbol a.val h.val * u a.val) = _
  rw [← Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => cubicSymbol a h.val * u a)]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma finiteCubicBound_controls_mass (S H : Finset Eisenstein) (u : Eisenstein → ℂ) :
    (∑ h ∈ H, ‖∑ a ∈ S, u a * cubicSymbol a h‖^2) ≤
      finiteCubicBound S H * ∑ a ∈ S, ‖u a‖^2 := by
  let v : EuclideanSpace ℂ S := WithLp.toLp 2 (fun a : S => u a.val)
  have hb := (finiteCubicOperator S H).le_opNorm v
  have hs := pow_le_pow_left₀ (_root_.norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  change (∑ h : H, ‖finiteCubicOperator S H v h‖^2) ≤
      finiteCubicBound S H * ∑ a : S, ‖u a.val‖^2 at hs
  dsimp only [v] at hs
  simp_rw [finiteCubicOperator_apply] at hs
  simpa only [← Finset.sum_subtype H (fun _ => Iff.rfl)
    (fun h => ‖∑ a ∈ S, u a * cubicSymbol a h‖^2),
    ← Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => ‖u a‖^2)] using hs

end CubicFirstMoment

namespace CubicFirstMoment

private lemma euclideanConj_norm {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ‖euclideanConj v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, euclideanConj]

private lemma matrixHilbertOperator_conj {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (v : EuclideanSpace ℂ κ) :
    matrixHilbertOperator (A.map star) v =
      euclideanConj (matrixHilbertOperator A (euclideanConj v)) := by
  apply PiLp.ext
  intro i
  change (∑ j, star (A i j) * v j) = star (∑ j, A i j * star (v j))
  simp [star_sum, star_mul, mul_comm]

private lemma matrixHilbertOperator_conj_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator (A.map star)‖ ≤ ‖matrixHilbertOperator A‖ := by
  apply (ContinuousLinearMap.opNorm_le_iff (f := matrixHilbertOperator (A.map star))
    (_root_.norm_nonneg (matrixHilbertOperator A))).mpr
  intro v
  rw [matrixHilbertOperator_conj, euclideanConj_norm]
  simpa only [euclideanConj_norm] using
    (matrixHilbertOperator A).le_opNorm (euclideanConj v)

private lemma matrixHilbertOperator_conj_norm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator (A.map star)‖ = ‖matrixHilbertOperator A‖ := by
  apply le_antisymm (matrixHilbertOperator_conj_norm_le A)
  have he : (A.map star).map star = A := by ext i j; simp
  have h := matrixHilbertOperator_conj_norm_le (A.map star)
  rwa [he] at h

private lemma matrixHilbertOperator_transpose_norm {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) :
    ‖matrixHilbertOperator A.transpose‖ = ‖matrixHilbertOperator A‖ := by
  have hc : A.transpose = (A.conjTranspose).map star := by
    ext i j
    simp
  rw [hc, matrixHilbertOperator_conj_norm]
  change ‖LinearMap.toContinuousLinearMap A.conjTranspose.toEuclideanLin‖ = _
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem finiteCubicBound_symm (S H : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (hH : ∀ h ∈ H, primary h) :
    finiteCubicBound S H = finiteCubicBound H S := by
  let A : Matrix H S ℂ := fun h a => cubicSymbol a.val h.val
  have hmat : (fun (a : S) (h : H) => cubicSymbol h.val a.val) = A.transpose := by
    funext a h
    exact cubic_reciprocity (hH h.val h.property) (hS a.val a.property)
  unfold finiteCubicBound finiteCubicOperator
  rw [hmat]
  exact congrArg (fun x : ℝ => x^2) (matrixHilbertOperator_transpose_norm A).symm

end CubicFirstMoment

namespace CubicFirstMoment

lemma coefficientVector_norm_sq (S : Finset Eisenstein) (u : Eisenstein → ℂ) :
    ‖(WithLp.toLp 2 (fun a : S => u a.val) : EuclideanSpace ℂ S)‖^2 =
      ∑ a ∈ S, ‖u a‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => ‖u a‖^2)).symm

lemma finiteCubicOperator_norm_sq (S H : Finset Eisenstein) (u : Eisenstein → ℂ) :
    ‖finiteCubicOperator S H (WithLp.toLp 2 (fun a : S => u a.val))‖^2 =
      ∑ h ∈ H, ‖∑ a ∈ S, u a * cubicSymbol a h‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ h : H, ‖finiteCubicOperator S H (WithLp.toLp 2 (fun a : S => u a.val)) h‖^2) = _
  simp_rw [finiteCubicOperator_apply]
  exact (Finset.sum_subtype H (fun _ => Iff.rfl)
    (fun h => ‖∑ a ∈ S, u a * cubicSymbol a h‖^2)).symm

lemma finiteCubicBound_le_iff (S H : Finset Eisenstein) {C : ℝ} (hC : 0 ≤ C) :
    finiteCubicBound S H ≤ C ↔ ∀ u : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ a ∈ S, u a * cubicSymbol a h‖^2) ≤
        C * ∑ a ∈ S, ‖u a‖^2 := by
  constructor
  · intro h u
    exact (finiteCubicBound_controls_mass S H u).trans
      (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  · intro h
    have hn : ‖finiteCubicOperator S H‖ ≤ Real.sqrt C := by
      apply (ContinuousLinearMap.opNorm_le_iff (f := finiteCubicOperator S H)
        (Real.sqrt_nonneg C)).mpr
      intro v
      let u (a : Eisenstein) : ℂ := if ha : a ∈ S then v ⟨a, ha⟩ else 0
      have hv : WithLp.toLp 2 (fun a : S => u a.val) = v := by
        apply PiLp.ext
        intro a
        simp [u]
      have hh : ‖finiteCubicOperator S H v‖^2 ≤ C*‖v‖^2 := by
        rw [← hv, finiteCubicOperator_norm_sq, coefficientVector_norm_sq]
        exact h u
      apply (sq_le_sq₀ (_root_.norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (_root_.norm_nonneg _))).mp
      simpa only [mul_pow, Real.sq_sqrt hC] using hh
    exact (pow_le_pow_left₀ (_root_.norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hC)

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency dyads and summable base Gram recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_ne_zero_of_ne_zero {h : Eisenstein} (hh : h ≠ 0) : normNat h ≠ 0 := by
  intro hz
  apply hh
  apply norm_eq_zero_iff.mp
  rw [← normNat_cast,hz,Nat.cast_zero]

lemma mem_frequencyDyad {j : ℕ} {h : Eisenstein} :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.log 2 (normNat h) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_nonzeroNormBall]
  refine ⟨fun h => ⟨h.1.2,h.2⟩,fun hh => ⟨⟨?_,hh.1⟩,hh.2⟩⟩
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at ht
  rw [← normNat_cast]
  exact_mod_cast ht.le

lemma frequencyDyad_norm {j : ℕ} {h : Eisenstein} (hh : h ∈ frequencyDyad j) :
    (2 : ℝ)^j ≤ norm h ∧ norm h ≤ 2*(2 : ℝ)^j := by
  rw [mem_frequencyDyad] at hh
  have hl := Nat.pow_log_le_self 2 (normNat_ne_zero_of_ne_zero hh.1)
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at hl ht
  rw [← normNat_cast]
  constructor
  · exact_mod_cast hl
  · have ht' : (normNat h : ℝ) ≤ (2 : ℝ)^(j+1) := by exact_mod_cast ht.le
    simpa [pow_succ,mul_comm] using ht'

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primary cube decomposition and finite operator block bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteCubicBound_twist_controls_mass (P S : Finset Eisenstein)
    (u z : Eisenstein → ℂ) (hz : ∀ b ∈ P, ‖z b‖ ≤ 1) :
    (∑ s ∈ S, ‖∑ b ∈ P, u b*z b*cubicSymbol b s‖^2) ≤
      finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 := by
  apply (finiteCubicBound_controls_mass P S (fun b => u b*z b)).trans
  apply mul_le_mul_of_nonneg_left _ (finiteCubicBound_nonneg _ _)
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul, mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (by
    simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (hz b hb) 2)

lemma finiteCubicBound_twist_conjugate_mass (P S : Finset Eisenstein)
    (u z : Eisenstein → ℂ) (hz : ∀ b ∈ P, ‖z b‖ ≤ 1) :
    (∑ s ∈ S, ‖∑ b ∈ P, u b*z b*star (cubicSymbol b s)‖^2) ≤
      finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 := by
  have h := finiteCubicBound_twist_controls_mass P S (fun b => star (u b))
    (fun b => star (z b)) (fun b hb => by simpa using hz b hb)
  have he (s : Eisenstein) :
      (∑ b ∈ P, u b*z b*star (cubicSymbol b s)) =
      star (∑ b ∈ P, star (u b)*star (z b)*cubicSymbol b s) := by
    simp [star_sum, star_mul, mul_comm, mul_assoc]
  simpa only [he, norm_star] using h

end CubicFirstMoment

namespace CubicFirstMoment

lemma cubeBlockMass_le_first (P S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (u : Eisenstein → ℂ) :
    cubeBlockMass P S T C u ≤
      (T.card : ℝ) * C.card * finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 := by
  have hrow (t c : Eisenstein) :
      (∑ s ∈ S, ‖∑ b ∈ P, u b * cubicSymbol b (s*t^2*c^3)‖^2) ≤
      finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 := by
    have h := finiteCubicBound_twist_controls_mass P S u
      (fun b => cubicSymbol b (t^2*c^3)) (fun b hb => norm_cubicSymbol_le_one (hP b hb) _)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro s hs
    congr 2
    apply Finset.sum_congr rfl
    intro b hb
    rw [mul_assoc s, cubicSymbol_mul_upper (hP b hb)]
    ring
  unfold cubeBlockMass
  rw [Finset.sum_comm (s := S) (t := T)]
  simp_rw [Finset.sum_comm (s := S) (t := C)]
  calc
    _ ≤ ∑ t ∈ T, ∑ c ∈ C, finiteCubicBound P S * ∑ b ∈ P, ‖u b‖^2 :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun c _ => hrow t c))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma cubeBlockMass_le_second (P S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (u : Eisenstein → ℂ) :
    cubeBlockMass P S T C u ≤
      (S.card : ℝ) * C.card * finiteCubicBound P T * ∑ b ∈ P, ‖u b‖^2 := by
  have hrow (s c : Eisenstein) :
      (∑ t ∈ T, ‖∑ b ∈ P, u b * cubicSymbol b (s*t^2*c^3)‖^2) ≤
      finiteCubicBound P T * ∑ b ∈ P, ‖u b‖^2 := by
    have h := finiteCubicBound_twist_conjugate_mass P T u
      (fun b => cubicSymbol b (s*c^3)) (fun b hb => norm_cubicSymbol_le_one (hP b hb) _)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro t ht
    congr 2
    apply Finset.sum_congr rfl
    intro b hb
    rw [cubicSymbol_mul_upper (hP b hb), cubicSymbol_mul_upper (hP b hb),
      cubicSymbol_mul_upper (hP b hb), cubicSymbol_pow_upper (hP b hb),
      cubicSymbol_sq_eq_star (hP b hb)]
    ring
  unfold cubeBlockMass
  simp_rw [Finset.sum_comm (s := T) (t := C)]
  calc
    _ ≤ ∑ s ∈ S, ∑ c ∈ C, finiteCubicBound P T * ∑ b ∈ P, ‖u b‖^2 :=
      Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun c _ => hrow s c))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem cubeBlockMass_le_min (P S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (u : Eisenstein → ℂ) :
    cubeBlockMass P S T C u ≤
      min ((T.card : ℝ) * C.card * finiteCubicBound P S)
          ((S.card : ℝ) * C.card * finiteCubicBound P T) * ∑ b ∈ P, ‖u b‖^2 := by
  rw [min_mul_of_nonneg _ _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact le_min (cubeBlockMass_le_first P S T C hP u) (cubeBlockMass_le_second P S T C hP u)

end CubicFirstMoment

namespace CubicFirstMoment

lemma cubeBlockSupport_mass_le (P S T C : Finset Eisenstein) (u : Eisenstein → ℂ) :
    (∑ n ∈ cubeBlockSupport S T C, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      cubeBlockMass P S T C u := by
  calc
    _ ≤ ∑ z ∈ S.product (T.product C),
        ‖∑ b ∈ P, u b*cubicSymbol b (z.1*z.2.1^2*z.2.2^3)‖^2 :=
      Finset.sum_image_le_of_nonneg
        (s := S.product (T.product C)) (g := fun z => z.1*z.2.1^2*z.2.2^3)
        (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) (fun _ _ => sq_nonneg _)
    _ = _ := by
      unfold cubeBlockMass
      exact (Finset.sum_product S (T.product C) _).trans
        (Finset.sum_congr rfl (fun s _ => Finset.sum_product T C _))

theorem finiteCubicBound_cubeBlock (P S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) :
    finiteCubicBound P (cubeBlockSupport S T C) ≤
      min ((T.card : ℝ) * C.card * finiteCubicBound P S)
          ((S.card : ℝ) * C.card * finiteCubicBound P T) := by
  apply (finiteCubicBound_le_iff _ _ (le_min
    (mul_nonneg (by positivity) (finiteCubicBound_nonneg P S))
    (mul_nonneg (by positivity) (finiteCubicBound_nonneg P T)))).mpr
  intro u
  exact (cubeBlockSupport_mass_le P S T C u).trans (cubeBlockMass_le_min P S T C hP u)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramified residual factors and full cube decomposition. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cube_decomposition (n : Eisenstein) :
    ∃ s t c : Eisenstein, Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧ n = s*t^2*c^3 := by
  refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
  · exact ⟨1,1,0,squarefree_one,squarefree_one,isCoprime_one_left,by simp⟩
  · intro u hu
    exact ⟨u,1,1,hu.squarefree,squarefree_one,isCoprime_one_right,by simp⟩
  · intro b p hb hp ih
    obtain ⟨s,t,c,hss,hst,hcop,rfl⟩ := ih
    by_cases hps : p ∣ s
    · obtain ⟨s',rfl⟩ := hps
      have hps' : IsCoprime p s' := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hss).1
      have hpt : IsCoprime p t := hcop.of_mul_left_left
      refine ⟨s',p*t,c,hss.of_mul_right,
        squarefree_mul_iff.mpr ⟨hpt.isRelPrime,hp.squarefree,hst⟩,
        hps'.symm.mul_right hcop.of_mul_left_right,?_⟩
      ring
    · by_cases hpt : p ∣ t
      · obtain ⟨t',rfl⟩ := hpt
        refine ⟨s,t',p*c,hss,hst.of_mul_right,hcop.of_mul_right_right,?_⟩
        ring
      · have hps' := hp.coprime_iff_not_dvd.mpr hps
        have hpt' := hp.coprime_iff_not_dvd.mpr hpt
        refine ⟨p*s,t,c,squarefree_mul_iff.mpr ⟨hps'.isRelPrime,hp.squarefree,hss⟩,
          hst,hpt'.mul_left hcop,?_⟩
        ring

theorem squarefree_ramified_split (n : Eisenstein) (hs : Squarefree n) :
    ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
  have h : ∀ n : Eisenstein, Squarefree n →
      ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
    intro n
    refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
    · intro hs
      have hh := hs 0 (by simp)
      exact (not_isUnit_zero hh).elim
    · intro u hu hs
      refine ⟨1,u,one_dvd _,?_,by simp⟩
      exact (isCoprime_zero_right.mpr hu).of_isCoprime_of_dvd_right (dvd_zero 3)
    · intro b p hb hp ih hs
      obtain ⟨d,e,hd,he,hbe⟩ := ih hs.of_mul_right
      have hpb : IsCoprime p b := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
      by_cases hp3 : p ∣ 3
      · have hpd : IsCoprime p d := (hbe ▸ hpb).of_mul_right_left
        refine ⟨p*d,e,hpd.mul_dvd hp3 hd,he,?_⟩
        rw [hbe]; ring
      · refine ⟨d,p*e,hd,(hp.coprime_iff_not_dvd.mpr hp3).mul_left he,?_⟩
        rw [hbe]; ring
  exact h n hs

lemma unit_residue_of_isCoprime_three {e : Eisenstein} (he : IsCoprime e 3) :
    IsUnit (Ideal.Quotient.mk (modulus 3) e) := by
  have h := he.map (Ideal.Quotient.mk (modulus 3))
  simpa only [residue_three_eq_zero, isCoprime_zero_right] using h

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

theorem squarefree_primary_residual (n : Eisenstein) (hs : Squarefree n) :
    ∃ r s : Eisenstein, r ≠ 0 ∧ norm r ≤ 9 ∧ primary s ∧ Squarefree s ∧ n = r*s := by
  obtain ⟨d,e,hd,he,hde⟩ := squarefree_ramified_split n hs
  obtain ⟨u,hu,hprim⟩ := unit_lift_mod_three (unit_residue_of_isCoprime_three he)
  obtain ⟨v,rfl⟩ := hu
  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, zero_dvd_iff] at hd
    norm_num at hd
  have hvi : norm (↑v⁻¹ : Eisenstein) = 1 := by
    rw [← normNat_cast, normNat_of_isUnit (Units.isUnit _), Nat.cast_one]
  refine ⟨d*(↑v⁻¹ : Eisenstein),e*(↑v : Eisenstein),mul_ne_zero hd0 (Units.ne_zero _),?_,hprim,?_,?_⟩
  · rw [norm_mul_eq, hvi, mul_one]
    have h := norm_le_of_dvd (by norm_num : (3 : Eisenstein) ≠ 0) hd
    have h3 : norm (3 : Eisenstein) = 9 := by
      change Complex.normSq (3 : ℂ) = 9
      norm_num
    simpa only [h3] using h
  · have hes : Squarefree e := (hde ▸ hs).of_mul_right
    exact squarefree_mul_iff.mpr ⟨((isCoprime_zero_left.mpr (Units.isUnit v)).of_isCoprime_of_dvd_left (dvd_zero e)).isRelPrime,hes,
      (Units.isUnit v).squarefree⟩
  · rw [hde]
    simp [mul_assoc, mul_left_comm, mul_comm]

end CubicFirstMoment

namespace CubicFirstMoment

theorem full_cube_decomposition {n : Eisenstein} (hn : n ≠ 0) :
    ∃ r s t c : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      c ≠ 0 ∧ n = r*s*t^2*c^3 := by
  obtain ⟨s₀,t₀,c,hs₀,ht₀,hst,hn'⟩ := cube_decomposition n
  obtain ⟨r,s,hr0,hr,hs,hss,hs'⟩ := squarefree_primary_residual s₀ hs₀
  obtain ⟨q,t,hq0,hq,ht,hst',ht'⟩ := squarefree_primary_residual t₀ ht₀
  have hc0 : c ≠ 0 := by intro hc; simp [hc] at hn'; exact hn hn'
  have hcop : IsCoprime s t :=
    hst.of_isCoprime_of_dvd_left (hs' ▸ dvd_mul_left s r) |>.of_isCoprime_of_dvd_right
      (ht' ▸ dvd_mul_left t q)
  refine ⟨r*q^2,s,t,c,mul_ne_zero hr0 (pow_ne_zero _ hq0),?_,hs,ht,hss,hst',hcop,hc0,?_⟩
  · rw [norm_mul_eq]
    have he : norm (q^2) = norm q ^ 2 := by simp [pow_two]
    rw [he]
    have hq2 : norm q ^ 2 ≤ 81 := by nlinarith [norm_nonneg q]
    nlinarith [norm_nonneg r, sq_nonneg (norm q)]
  · rw [hn',hs',ht']; ring

lemma residualCubeSupport_mass_le (P R S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (u : Eisenstein → ℂ) :
    (∑ n ∈ residualCubeSupport R S T C, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      (R.card : ℝ) *
        min ((T.card : ℝ)*C.card*finiteCubicBound P S)
            ((S.card : ℝ)*C.card*finiteCubicBound P T) * ∑ b ∈ P, ‖u b‖^2 := by
  let L := min ((T.card : ℝ)*C.card*finiteCubicBound P S)
    ((S.card : ℝ)*C.card*finiteCubicBound P T)
  have htw (r : Eisenstein) :
      (∑ n ∈ (cubeBlockSupport S T C).image (r * ·), ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
        L * ∑ b ∈ P, ‖u b‖^2 := by
    have h := finiteCubicBound_twist_controls_mass P (cubeBlockSupport S T C) u
      (fun b => cubicSymbol b r) (fun b hb => norm_cubicSymbol_le_one (hP b hb) r)
    calc
      _ ≤ ∑ n ∈ cubeBlockSupport S T C, ‖∑ b ∈ P, u b*cubicSymbol b (r*n)‖^2 :=
        Finset.sum_image_le_of_nonneg (g := fun n => r*n)
          (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) (fun _ _ => sq_nonneg _)
      _ = ∑ n ∈ cubeBlockSupport S T C, ‖∑ b ∈ P, u b*cubicSymbol b r*cubicSymbol b n‖^2 := by
        apply Finset.sum_congr rfl; intro n hn
        congr 2
        apply Finset.sum_congr rfl; intro b hb
        rw [cubicSymbol_mul_upper (hP b hb)]; ring
      _ ≤ finiteCubicBound P (cubeBlockSupport S T C) * ∑ b ∈ P, ‖u b‖^2 := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (finiteCubicBound_cubeBlock P S T C hP)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hunion : (∑ n ∈ residualCubeSupport R S T C, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      ∑ r ∈ R, ∑ n ∈ (cubeBlockSupport S T C).image (r * ·),
        ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := by
    classical
    induction R using Finset.induction_on with
    | empty => simp [residualCubeSupport]
    | @insert r R hr ih =>
      rw [residualCubeSupport, Finset.biUnion_insert, Finset.sum_insert hr]
      dsimp only [residualCubeSupport] at ih
      have hh : ∀ n ∈ (cubeBlockSupport S T C).image (r * ·) ∩
          R.biUnion (fun r => (cubeBlockSupport S T C).image (r * ·)),
          (0 : ℝ) ≤ ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := fun _ _ => sq_nonneg _
      have he := Finset.sum_union_inter (s₁ := (cubeBlockSupport S T C).image (r * ·))
        (s₂ := R.biUnion (fun r => (cubeBlockSupport S T C).image (r * ·)))
        (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2)
      have hn := Finset.sum_nonneg hh
      linarith
  calc
    _ ≤ ∑ r ∈ R, ∑ n ∈ (cubeBlockSupport S T C).image (r * ·),
        ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := hunion
    _ ≤ ∑ r ∈ R, L * ∑ b ∈ P, ‖u b‖^2 := Finset.sum_le_sum (fun r _ => htw r)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_squarefreePrimaryDyad {n : Eisenstein} {j : ℕ} :
    n ∈ squarefreePrimaryDyad j ↔ n ∈ frequencyDyad j ∧ primary n ∧ Squarefree n := by
  simp [squarefreePrimaryDyad]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact sieve majorants and common-factor energy bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_subset_of_dvd {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hab : a ∣ b) : primaryPrimeFactors a ⊆ primaryPrimeFactors b := by
  intro p hp
  obtain ⟨hpp,hpa⟩ := primaryPrimeFactor_spec ha hp
  exact primaryPrime_mem_factors hb hpp (hpa.trans hab)

lemma primary_divisors_card_le (T : Finset Eisenstein)
    (hT : ∀ k ∈ T, primary k ∧ Squarefree k) {p : Eisenstein} (hp : primary p) :
    ((T.filter (· ∣ p)).card : ℝ) ≤ (2 : ℝ)^(primaryPrimeFactors p).card := by
  have hmaps : ∀ k ∈ T.filter (· ∣ p), primaryPrimeFactors k ∈ (primaryPrimeFactors p).powerset := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact Finset.mem_powerset.mpr (primaryPrimeFactors_subset_of_dvd (hT k hk.1).1 hp hk.2)
  have hinj : Set.InjOn primaryPrimeFactors (↑(T.filter (· ∣ p)) : Set Eisenstein) := by
    intro k hk l hl he
    have hk' := hT k (Finset.mem_filter.mp hk).1
    have hl' := hT l (Finset.mem_filter.mp hl).1
    rw [← primaryPrimeFactors_prod hk'.1 hk'.2,← primaryPrimeFactors_prod hl'.1 hl'.2,he]
  have hc := (Finset.card_image_iff.mpr hinj).symm.le.trans
    (Finset.card_le_card (Finset.image_subset_iff.mpr hmaps))
  rw [Finset.card_powerset] at hc
  exact_mod_cast hc

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveImprovement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification, iteration to exponent four-thirds and the cubic large sieve. -/

section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma small_four_thirds_le_mixed {M N : ℝ} (hN : 0 ≤ N) (hNM : N ≤ M) :
    N^(4/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  calc
    _ = (N*N)^(2/3 : ℝ) := by
      rw [← pow_two,← Real.rpow_natCast_mul hN]
      norm_num
    _ ≤ _ := by gcongr

theorem finiteCubicBound_sharp :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ M → 1 ≤ N →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ b ∈ H, primary b ∧ Squarefree b ∧ norm b ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*(M+N+(M*N)^(2/3 : ℝ)) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := sieveExponent_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro S H M N hM hN hS hH
  have hM0 : 0 ≤ M := (zero_lt_one.trans_le hM).le
  have hN0 : 0 ≤ N := (zero_lt_one.trans_le hN).le
  have hmixed : 0 ≤ (M*N)^(2/3 : ℝ) := by positivity
  rcases le_total N M with hNM | hMN
  · have hs := small_four_thirds_le_mixed hN0 hNM
    have hh : M+(M*N)^(2/3 : ℝ)+N^(4/3 : ℝ) ≤ 2*(M+N+(M*N)^(2/3 : ℝ)) := by linarith
    exact (hbound S H M N hM hN hS hH).trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))
  · rw [finiteCubicBound_symm S H (fun a ha => (hS a ha).1) (fun b hb => (hH b hb).1)]
    have hs := small_four_thirds_le_mixed hM0 hMN
    rw [mul_comm N M] at hs
    have hh : N+(M*N)^(2/3 : ℝ)+M^(4/3 : ℝ) ≤ 2*(M+N+(M*N)^(2/3 : ℝ)) := by linarith
    have hb := hbound H S N M hN hM hH hS
    rw [mul_comm N M] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAdditiveSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published additive large-sieve input over the Eisenstein integers

M. N. Huxley, *The large sieve inequality for algebraic number fields*,
Mathematika 15 (1968), 178–187. The precise imaginary-quadratic form used
here is displayed in P. Gao and L. Zhao, *The large sieve with power moduli
in imaginary quadratic number fields*, IJNT 18 (2022), 1713–1733,
arXiv:2101.00811v2, equation (1.2).

This is an explicit hypothesis type. The primitive multiplicative
character inequality is to be derived by finite Gauss expansion and
orthogonality; it is not assumed here.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxleyModulusMass_nonneg (q : Eisenstein) (N : Finset Eisenstein)
    (v : Eisenstein → ℂ) : 0 ≤ huxleyModulusMass q N v := by
  apply tsum_nonneg
  intro h
  split_ifs <;> positivity

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DispersionAlgebra
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact corrected-dispersion identities

The polynomials below are those in `eq:dispersion-polynomials` of the
manuscript. The factorization is valid even with a common prime factor:
the already proved Gauss-sum multiplication law then makes the summand zero.
The norm estimates here do not assume the new dispersion bounds.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- Finite Cauchy--Schwarz for the actual complex row sum. -/
theorem complex_bilinear_rows_sq {ι : Type*} (A : Finset ι) (α F : ι → ℂ) :
    ‖∑ a ∈ A, α a * F a‖ ^ 2 ≤
      (∑ a ∈ A, ‖α a‖ ^ 2) * ∑ a ∈ A, ‖F a‖ ^ 2 := by
  calc
    _ ≤ (∑ a ∈ A, ‖α a * F a‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (norm_sum_le _ _) 2
    _ = (∑ a ∈ A, ‖α a‖ * ‖F a‖) ^ 2 := by simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq A _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramSchur
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite Gram row-sum bound

This is the linear algebra step in the exceptional-moment argument: a
symmetric absolute Gram kernel bounds its quadratic form by its largest
row sum. Both variables are retained in the estimate.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

theorem nonnegative_schur_bound {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (K : ι → ι → ℝ) (R : ℝ)
    (hK : ∀ p ∈ P, ∀ q ∈ P, 0 ≤ K p q)
    (hsym : ∀ p ∈ P, ∀ q ∈ P, K p q = K q p)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, K p q ≤ R) :
    (∑ p ∈ P, ∑ q ∈ P, x p * x q * K p q) ≤ R * ∑ p ∈ P, (x p)^2 := by
  have hpairs : (∑ p ∈ P, ∑ q ∈ P, 2 * (x p * x q * K p q)) ≤
      ∑ p ∈ P, ∑ q ∈ P, ((x p)^2 + (x q)^2) * K p q := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro q hq
    have h := mul_nonneg (sq_nonneg (x p-x q)) (hK p hp q hq)
    nlinarith only [h]
  have hswap : (∑ p ∈ P, ∑ q ∈ P, (x q)^2 * K p q) =
      ∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hsym q hq p hp]
  have hrow' : (∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q) ≤
      R * ∑ p ∈ P, (x p)^2 := by
    simp only [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow p hp) (sq_nonneg (x p))
  have he : (∑ p ∈ P, ∑ q ∈ P, ((x p)^2 + (x q)^2) * K p q) =
      2 * ∑ p ∈ P, ∑ q ∈ P, (x p)^2 * K p q := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hswap]
    ring
  rw [he] at hpairs
  simp only [← Finset.mul_sum] at hpairs hrow'
  linarith

/-- The complex Gram quadratic form is bounded using only absolute row
sums and Hermitian symmetry of their norms. -/
theorem complex_schur_bound {ι : Type*} (P : Finset ι) (z : ι → ℂ)
    (K : ι → ι → ℂ) (R : ℝ)
    (hsym : ∀ p ∈ P, ∀ q ∈ P, ‖K p q‖ = ‖K q p‖)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖K p q‖ ≤ R) :
    ‖∑ p ∈ P, ∑ q ∈ P, z p * star (z q) * K p q‖ ≤
      R * ∑ p ∈ P, ‖z p‖^2 := by
  calc
    _ ≤ ∑ p ∈ P, ‖∑ q ∈ P, z p * star (z q) * K p q‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ‖z p * star (z q) * K p q‖ :=
      Finset.sum_le_sum (fun p hp => norm_sum_le _ _)
    _ = ∑ p ∈ P, ∑ q ∈ P, ‖z p‖ * ‖z q‖ * ‖K p q‖ := by
      simp only [norm_mul, norm_star]
    _ ≤ _ := nonnegative_schur_bound P (fun p => ‖z p‖) (fun p q => ‖K p q‖) R
      (fun p hp q hq => _root_.norm_nonneg _) hsym hrow

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramOperator
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From Gram row sums to character-polynomial bounds

Finite duality turns the row-sum bound into an operator estimate. This is
the Cauchy/Gram step used after the multiplicity argument in the exceptional-character-moment argument.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

lemma complex_sum_norm_sq_expansion {ι : Type*} (P : Finset ι) (z : ι → ℂ) :
    ((‖∑ p ∈ P, z p‖^2 : ℝ) : ℂ) = ∑ p ∈ P, ∑ q ∈ P, z p * star (z q) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [starRingEnd_apply, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma finiteGram_star {ι κ : Type*} (N : Finset κ) (T : ι → κ → ℂ) (p q : ι) :
    star (finiteGram N T q p) = finiteGram N T p q := by
  simp only [finiteGram, star_sum, star_mul, star_star]

lemma finite_gram_identity {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (z : ι → ℂ) (T : ι → κ → ℂ) :
    ((∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, z p * star (z q) * finiteGram N T p q := by
  have hcast : ((∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) =
      ∑ n ∈ N, ((‖∑ p ∈ P, z p * T p n‖^2 : ℝ) : ℂ) :=
    map_sum Complex.ofRealHom _ _
  rw [hcast]
  simp_rw [complex_sum_norm_sq_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [finiteGram, Finset.mul_sum, star_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem finite_gram_energy_le {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (z : ι → ℂ) (T : ι → κ → ℂ) (R : ℝ)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖finiteGram N T p q‖ ≤ R) :
    (∑ n ∈ N, ‖∑ p ∈ P, z p * T p n‖^2) ≤ R * ∑ p ∈ P, ‖z p‖^2 := by
  have hs : ∀ p ∈ P, ∀ q ∈ P, ‖finiteGram N T p q‖ = ‖finiteGram N T q p‖ := by
    intro p hp q hq
    rw [← finiteGram_star N T p q, norm_star]
  have h := complex_schur_bound P z (finiteGram N T) R hs hrow
  rw [← finite_gram_identity P N z T, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at h
  exact h

/-- Duality exchanges rows and columns without loss. -/
theorem finite_gram_operator_le {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (v : κ → ℂ) (T : ι → κ → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖finiteGram N T p q‖ ≤ R) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n * T p n‖^2) ≤ R * ∑ n ∈ N, ‖v n‖^2 := by
  let f : ι → ℂ := fun p => ∑ n ∈ N, v n * T p n
  let g : κ → ℂ := fun n => ∑ p ∈ P, f p * star (T p n)
  let E : ℝ := ∑ p ∈ P, ‖f p‖^2
  let V : ℝ := ∑ n ∈ N, ‖v n‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdual : (E : ℂ) = ∑ n ∈ N, v n * star (g n) := by
    change ((∑ p ∈ P, ‖f p‖^2 : ℝ) : ℂ) = _
    have hcast : ((∑ p ∈ P, ‖f p‖^2 : ℝ) : ℂ) =
        ∑ p ∈ P, ((‖f p‖^2 : ℝ) : ℂ) := map_sum Complex.ofRealHom _ _
    rw [hcast]
    have he : ∀ p, ((‖f p‖^2 : ℝ) : ℂ) = f p * star (f p) := by
      intro p
      rw [Complex.ofReal_pow]
      exact (Complex.mul_conj' (f p)).symm
    simp_rw [he]
    conv_lhs => arg 2; ext p; lhs; unfold f
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [g, star_sum, star_mul, star_star, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hrow' : ∀ p ∈ P,
      ∑ q ∈ P, ‖finiteGram N (fun p n => star (T p n)) p q‖ ≤ R := by
    intro p hp
    have he : ∀ q, finiteGram N (fun p n => star (T p n)) p q = star (finiteGram N T p q) := by
      intro q
      simp only [finiteGram, star_sum, star_mul, star_star, mul_comm]
    simpa only [he, norm_star] using hrow p hp
  have hg := finite_gram_energy_le P N f (fun p n => star (T p n)) R hrow'
  change (∑ n ∈ N, ‖g n‖^2) ≤ R*E at hg
  have hc := complex_bilinear_rows_sq N v (fun n => star (g n))
  rw [← hdual, Complex.norm_real, Real.norm_of_nonneg hE] at hc
  simp only [norm_star] at hc
  change E^2 ≤ V * (∑ n ∈ N, ‖g n‖^2) at hc
  have hm := mul_le_mul_of_nonneg_left hg hV
  change E ≤ R*V
  by_cases hzero : E = 0
  · rw [hzero]
    exact mul_nonneg hR hV
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MultiplicativeBessel
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite-character orthogonality step in the ordinary large sieve. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {R : Type*} [CommRing R] [Fintype R]

lemma mulChar_gram (χ ψ : MulChar R ℂ) :
    (∑ x : R, χ x*star (ψ x)) = if χ = ψ then (Fintype.card Rˣ:ℂ) else 0 := by
  simp_rw [MulChar.star_apply',← MulChar.mul_apply]
  by_cases h : χ = ψ
  · subst ψ
    rw [mul_inv_cancel,ite_eq_left rfl]
    exact MulChar.sum_one_eq_card_units
  · rw [ite_eq_right h]
    exact MulChar.sum_eq_zero_of_ne_one (fun he => h (mul_inv_eq_one.mp he))

/-- Bessel inequality for any selected finite set of distinct multiplicative
characters, with the exact unit-group cardinality. -/
theorem mulChar_bessel (C : Finset (MulChar R ℂ)) (v : R → ℂ) :
    (∑ χ ∈ C, ‖∑ x : R, v x*χ x‖^2) ≤
      (Fintype.card Rˣ:ℝ)*∑ x : R, ‖v x‖^2 := by
  apply finite_gram_operator_le C Finset.univ v (fun χ x => χ x)
    (show (0:ℝ) ≤ Fintype.card Rˣ by positivity)
  intro χ hχ
  change (∑ ψ ∈ C, ‖∑ x : R, χ x*star (ψ x)‖) ≤ _
  simp_rw [mulChar_gram]
  simp only [apply_ite, norm_zero, Complex.norm_natCast]
  simp [hχ]

/-- Gauss expansion transfers a character family to its additive sums
without a conductor loss. The hypotheses are finite Fourier identities,
not an analytic large-sieve estimate. -/
theorem gauss_transform_bessel {ι : Type*} (N : Finset ι)
    (C : Finset (MulChar R ℂ)) (v : ι → ℂ)
    (phase : R → ι → ℂ) (t : MulChar R ℂ → ι → ℂ)
    (g : MulChar R ℂ → ℂ)
    (hR : 0 < Fintype.card R)
    (hg : ∀ χ ∈ C, ‖g χ‖^2 = Fintype.card R)
    (htransform : ∀ χ ∈ C, ∀ n ∈ N,
      g χ*t χ n = ∑ x : R, χ x*phase x n) :
    (∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) ≤
      ∑ x : R, ‖∑ n ∈ N, v n*phase x n‖^2 := by
  let S (x : R) := ∑ n ∈ N, v n*phase x n
  have hidentity (χ : MulChar R ℂ) (hχ : χ ∈ C) :
      g χ*(∑ n ∈ N, v n*t χ n) = ∑ x : R, S x*χ x := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ n ∈ N, v n*(∑ x : R, χ x*phase x n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [← htransform χ hχ n hn]
        ring
      _ = _ := by
        simp only [S,Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hbound := mulChar_bessel C S
  have he : (Fintype.card R:ℝ)*(∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) =
      ∑ χ ∈ C, ‖∑ x : R, S x*χ x‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [← hidentity χ hχ,norm_mul,mul_pow,hg χ hχ]
  have hcard : Fintype.card Rˣ ≤ Fintype.card R :=
    Fintype.card_le_of_injective (fun x : Rˣ => (x:R)) Units.val_injective
  have hnonneg : 0 ≤ ∑ x : R, ‖S x‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hupper := hbound.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hnonneg)
  rw [← he] at hupper
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast hR : (0:ℝ) < Fintype.card R)).mp hupper

/-- The same transfer with the additive side restricted to units. This is the
restriction appearing in the published additive large sieve. -/
theorem gauss_transform_unit_bessel {ι : Type*} (N : Finset ι)
    (C : Finset (MulChar R ℂ)) (v : ι → ℂ)
    (phase : R → ι → ℂ) (t : MulChar R ℂ → ι → ℂ)
    (g : MulChar R ℂ → ℂ)
    (hR : 0 < Fintype.card R)
    (hg : ∀ χ ∈ C, ‖g χ‖^2 = Fintype.card R)
    (htransform : ∀ χ ∈ C, ∀ n ∈ N,
      g χ*t χ n = ∑ x : R, χ x*phase x n) :
    (∑ χ ∈ C, ‖∑ n ∈ N, v n*t χ n‖^2) ≤
      ∑ x : R, if IsUnit x then ‖∑ n ∈ N, v n*phase x n‖^2 else 0 := by
  let phase' (x : R) (n : ι) := if IsUnit x then phase x n else 0
  have ht : ∀ χ ∈ C, ∀ n ∈ N, g χ*t χ n = ∑ x : R, χ x*phase' x n := by
    intro χ hχ n hn
    rw [htransform χ hχ n hn]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hu : IsUnit x
    · simp only [phase',hu,ite_true, if_true]
    · simp only [phase',hu,ite_false, if_false,MulChar.map_nonunit χ hu,zero_mul]
  have h := gauss_transform_bessel N C v phase' t g hR hg ht
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hu : IsUnit x <;> simp [phase',hu]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MixedCharacterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conductor-by-conductor Gauss transfer for actual squarefree mixed characters. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_mixedGaussFactor {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) :
    ‖((Real.sqrt (norm (a*b)):ℂ)*(gauss a*star (gauss b)) / mixedCubic a b 3)‖^2 =
      norm (a*b) := by
  rw [norm_div,norm_mul,norm_mul,norm_star,norm_gauss_of_squarefree ha hsa,
    norm_gauss_of_squarefree hb hsb,
    mixedCubic_norm_of_coprime ha hb (primary_coprime_three (primary_mul ha hb))]
  simp only [mul_one,div_one,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (norm_nonneg _)

/-- Each actual primitive mixed cubic character is bounded by the unit-residue
additive energy at the same conductor. No analytic hypothesis is used. -/
theorem mixedCharacter_unit_energy (N : Finset Eisenstein) (v : Eisenstein → ℂ)
    {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hsa : Squarefree a) (hsb : Squarefree b) (hab : IsCoprime a b) :
    ‖∑ n ∈ N, v n*star (mixedCubic a b n)‖^2 ≤ huxleyModulusMass (a*b) N v := by
  have hq : a*b ≠ 0 := mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb)
  let : Finite (Residues (a*b)) := finite_residues hq
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let χ := mixedResidueChar a b ha hb
  let phase (x : Residues (a*b)) (n : Eisenstein) :=
    huxleyPhase (a*b) (residueRepresentative (a*b) x) n
  let t (_ : MulChar (Residues (a*b)) ℂ) (n : Eisenstein) := star (mixedCubic a b n)
  let g (_ : MulChar (Residues (a*b)) ℂ) :=
    ((Real.sqrt (norm (a*b)):ℂ)*(gauss a*star (gauss b)) / mixedCubic a b 3)
  have hcard : (Fintype.card (Residues (a*b)):ℝ) = norm (a*b) := by
    rw [← Nat.card_eq_fintype_card,residues_card hq,normNat_cast]
  have hR : 0 < Fintype.card (Residues (a*b)) := by
    apply Nat.pos_of_ne_zero
    rw [← Nat.card_eq_fintype_card,residues_card hq]
    exact normNat_ne_zero hq
  have hg : ∀ ψ ∈ ({χ} : Finset (MulChar (Residues (a*b)) ℂ)),
      ‖g ψ‖^2 = Fintype.card (Residues (a*b)) := by
    intro ψ hψ
    rw [hcard]
    exact norm_mixedGaussFactor ha hb hsa hsb
  have ht : ∀ ψ ∈ ({χ} : Finset (MulChar (Residues (a*b)) ℂ)), ∀ n ∈ N,
      g ψ*t ψ n = ∑ x : Residues (a*b), ψ x*phase x n := by
    intro ψ hψ n hn
    have he : ψ = χ := Finset.mem_singleton.mp hψ
    subst ψ
    exact (mixedResidueChar_fourier ha hb hsa hsb hab n).symm
  have h := gauss_transform_unit_bessel N {χ} v phase t g hR hg ht
  simp only [Finset.sum_singleton,t] at h
  refine h.trans_eq ?_
  rw [huxleyModulusMass,tsum_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hu : IsUnit x <;> simp [hu,phase,additiveSievePolynomial]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OrdinaryMixedSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary mixed cubic character sieve, derived from Huxley's additive
large sieve. The only extra loss is the proved arbitrarily small divisor power. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma pairConductor_primary {p : Eisenstein × Eisenstein} (hp : PrimarySquarefreePair p) :
    primary (pairConductor p) := primary_mul hp.1 hp.2.1

lemma pairConductor_squarefree {p : Eisenstein × Eisenstein} (hp : PrimarySquarefreePair p) :
    Squarefree (pairConductor p) := squarefree_mul_iff.mpr ⟨hp.2.2.2.2.isRelPrime,hp.2.2.1,hp.2.2.2.1⟩

/-- A product determines the second factor, so conductor multiplicity is at
most the number of primary squarefree divisors. -/
lemma pairConductor_fiber_card (P : Finset (Eisenstein × Eisenstein))
    (hP : ∀ p ∈ P, PrimarySquarefreePair p) {q : Eisenstein} (hq : primary q) :
    ((P.filter (fun p => pairConductor p = q)).card : ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors q).card := by
  let F := P.filter (fun p => pairConductor p = q)
  let T := P.image Prod.fst
  have hinj : Set.InjOn Prod.fst (↑F : Set (Eisenstein × Eisenstein)) := by
    intro x hx y hy he
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    apply Prod.ext he
    apply mul_left_cancel₀ (primary_ne_zero (hP x hx'.1).1)
    calc
      x.1*x.2 = q := hx'.2
      _ = y.1*y.2 := hy'.2.symm
      _ = x.1*y.2 := by rw [he]
  have hT : ∀ a ∈ T, primary a ∧ Squarefree a := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨(hP p hp).1,(hP p hp).2.2.1⟩
  have hsub : F.image Prod.fst ⊆ T.filter (· ∣ q) := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hp'.1,
      hp'.2 ▸ dvd_mul_right p.1 p.2⟩
  calc
    (F.card:ℝ) = ((F.image Prod.fst).card:ℝ) := by rw [Finset.card_image_iff.mpr hinj]
    _ ≤ ((T.filter (· ∣ q)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := primary_divisors_card_le T hT hq

/-- Finite collection of the single-conductor energy inequalities. -/
theorem mixedCharacter_energy_collection {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ) (N : Finset Eisenstein)
      (P : Finset (Eisenstein × Eisenstein)), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ N, v n*star (mixedCubic p.1 p.2 n)‖^2) ≤
        K*Q^ε*∑ q ∈ nonzeroNormBall Q, huxleyModulusMass q N v := by
  obtain ⟨K,hK,hweight⟩ := primeDivisorWeight_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro Q N P hQ hP v
  have hmaps : ∀ p ∈ P, pairConductor p ∈ nonzeroNormBall Q := by
    intro p hp
    exact mem_nonzeroNormBall.mpr ⟨(hP p hp).2,
      primary_ne_zero (pairConductor_primary (hP p hp).1)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  let F := P.filter (fun p => pairConductor p = q)
  by_cases hF : F.Nonempty
  · obtain ⟨p,hp⟩ := hF
    have hp' := Finset.mem_filter.mp hp
    have hqp : primary q := hp'.2 ▸ pairConductor_primary (hP p hp'.1).1
    have hqs : Squarefree q := hp'.2 ▸ pairConductor_squarefree (hP p hp'.1).1
    have hqn : norm q ≤ Q := by rw [← hp'.2]; exact (hP p hp'.1).2
    have hcard : (F.card:ℝ) ≤ K*Q^ε :=
      (pairConductor_fiber_card P (fun p hp => (hP p hp).1) hqp).trans
        ((hweight q hqp hqs).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg q) hqn hε.le) hK.le))
    calc
      _ ≤ ∑ _p ∈ F, huxleyModulusMass q N v := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hh := (hP p hp'.1).1
        have hb := mixedCharacter_unit_energy N v hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2
        simpa only [← hp'.2,pairConductor] using hb
      _ = (F.card:ℝ)*huxleyModulusMass q N v := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (huxleyModulusMass_nonneg q N v)
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (∑ p ∈ F, _) ≤ _
    rw [he,Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg (by linarith) _))
      (huxleyModulusMass_nonneg q N v)

/-- The ordinary large sieve for actual squarefree coprime cubic pairs. Its
sole analytic hypothesis is the cited additive `Q²+Z` inequality. -/
theorem ordinary_mixed_cubic_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ nonzeroNormBall Z, v n*star (mixedCubic p.1 p.2 n)‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ nonzeroNormBall Z, ‖v n‖^2 := by
  obtain ⟨K,hK,hcollect⟩ := mixedCharacter_energy_collection hε
  obtain ⟨H,hH,hadd⟩ := hHuxley
  refine ⟨K*H,mul_pos hK hH,?_⟩
  intro Q Z hQ hZ P hP v
  apply (hcollect Q (nonzeroNormBall Z) P hQ hP v).trans
  have hh := mul_le_mul_of_nonneg_left (hadd Q Z hQ hZ v)
    (mul_nonneg hK.le (Real.rpow_nonneg (show 0 ≤ Q by linarith) ε))
  dsimp only [huxleySieveMass] at hh
  convert hh using 1 <;> first | rfl | ring

/-- Conjugating the coefficients gives the other character orientation. -/
theorem ordinary_mixed_cubic_sieve_unstar (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ nonzeroNormBall Z, v n*mixedCubic p.1 p.2 n‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ nonzeroNormBall Z, ‖v n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P hP v
  have h := hbound Q Z hQ hZ P hP (fun n => star (v n))
  simpa only [← star_mul,← star_sum,norm_star,mul_comm] using h

/-- Restriction to an arbitrary finite coefficient support costs nothing. -/
theorem ordinary_mixed_cubic_sieve_finite (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (B : Finset Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Z) → ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ n ∈ B, v n*mixedCubic p.1 p.2 n‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ n ∈ B, ‖v n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_unstar hHuxley hε
  refine ⟨C,hC,?_⟩
  intro Q Z hQ hZ P B hP hB v
  let w (n : Eisenstein) := if n ∈ B then v n else 0
  have hsub : B ⊆ nonzeroNormBall Z := fun n hn =>
    mem_nonzeroNormBall.mpr ⟨(hB n hn).2,(hB n hn).1⟩
  have hsum (p : Eisenstein × Eisenstein) :
      (∑ n ∈ nonzeroNormBall Z, w n*mixedCubic p.1 p.2 n) =
        ∑ n ∈ B, v n*mixedCubic p.1 p.2 n := by
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [w,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [w,hn,ite_true, if_true]
  have henergy : (∑ n ∈ nonzeroNormBall Z, ‖w n‖^2) = ∑ n ∈ B, ‖v n‖^2 := by
    rw [← Finset.sum_subset hsub (fun n _ hn => by simp [w,hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [w,hn,ite_true, if_true]
  simpa only [hsum,henergy] using hbound Q Z hQ hZ P hP w

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordinary mean values after collecting Eisenstein norms

The input `MontgomeryVaughanBound` is the ordinary Dirichlet-polynomial
mean-square theorem of Montgomery--Vaughan, *Hilbert's inequality*,
J. London Math. Soc. (2) 8 (1974), Corollary 3, p. 75, equation (1.11),
in the form explicitly recorded
in the manuscript as `eq:ordinary-mean-value`.

The deductions below collect the actual Eisenstein norms, record their
multiplicity cost, and preserve an arbitrary fixed angular weight and
an arbitrary translated height. These are the ordinary mean-value steps
in `eq:dispersion-height-small` and `eq:angular-completed-height`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma mellinPhase_add (t u x : ℝ) :
    mellinPhase (t + u) x = mellinPhase t x * mellinPhase u x := by
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma normPolynomial_collected (s : Finset Eisenstein) (v : Eisenstein → ℂ)
    (Z : ℕ) (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z) (t : ℝ) :
    eisensteinNormPolynomial s v t = integerNormPolynomial Z (normCollectedCoeff s v) t := by
  unfold eisensteinNormPolynomial integerNormPolynomial normCollectedCoeff
  rw [← Finset.sum_fiberwise_of_maps_to hs]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  have he := (Finset.mem_filter.mp hb).2
  rw [← normNat_cast b, he]

lemma norm_sum_sq_le_card_mul (s : Finset Eisenstein) (v : Eisenstein → ℂ) :
    ‖∑ b ∈ s, v b‖ ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  have hnorm := norm_sum_le s v
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun b => ‖v b‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcauchy
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))).mpr
    hnorm |>.trans hcauchy

lemma normCollectedCoeff_energy (s : Finset Eisenstein) (v : Eisenstein → ℂ)
    (Z : ℕ) (M : ℝ) (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M) :
    (∑ n ∈ Finset.Icc 1 Z, ‖normCollectedCoeff s v n‖ ^ 2) ≤
      M * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Z, M * ∑ b ∈ s with normNat b = n, ‖v b‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact (norm_sum_sq_le_card_mul _ v).trans
        (mul_le_mul_of_nonneg_right (hM n hn) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hs]

/-- The mean-square bound with the exact multiplicity loss from collecting
Eisenstein norms. -/
theorem eisensteinNormPolynomial_meanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖eisensteinNormPolynomial s v t‖ ^ 2) ≤
      C * (b - a + Z) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  simp_rw [normPolynomial_collected s v Z hs]
  have h := hMV Z (normCollectedCoeff s v) a b hab
  have hfactor : 0 ≤ C * (b - a + Z) := mul_nonneg hC (by positivity)
  calc
    _ ≤ C * (b - a + Z) * (M * ∑ c ∈ s, ‖v c‖ ^ 2) :=
      h.trans (mul_le_mul_of_nonneg_left (normCollectedCoeff_energy s v Z M hs hM) hfactor)
    _ = _ := by ring

/-- A fixed angular character and translated height are coefficient phases;
they do not change the original coefficient energy. -/
theorem fixedAngular_translated_meanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2) ≤
      C * (b - a + Z) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  let w := fun c => v c * theta ℓ c * mellinPhase u (norm c)
  have heq : ∀ t, (∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)) =
      eisensteinNormPolynomial s w t := by
    intro t
    unfold eisensteinNormPolynomial
    apply Finset.sum_congr rfl
    intro c hc
    rw [mellinPhase_add]
    dsimp [w]
    ring
  simp_rw [heq]
  have henergy : (∑ c ∈ s, ‖w c‖ ^ 2) = ∑ c ∈ s, ‖v c‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [w, norm_mul, norm_theta (hzero c hc), mellinPhase_norm, mul_one]
  simpa only [henergy] using eisensteinNormPolynomial_meanSquare hMV hC s w Z M hs hM hab

/-- The normalized two-sided height mean used for the small-conductor
noncube contribution. Both positive and negative height intervals occur. -/
theorem fixedAngular_translated_dyadicMeanSquare {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (s : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ) (M : ℝ)
    (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z)
    (hzero : ∀ b ∈ s, b ≠ 0)
    (hM : ∀ n ∈ Finset.Icc 1 Z, ((s.filter (fun b => normNat b = n)).card : ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ t in T..2 * T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2) +
     (∫ t in -2 * T..-T, ‖∑ c ∈ s, v c * theta ℓ c * mellinPhase (t + u) (norm c)‖ ^ 2)) / T ≤
      2 * C * (1 + (Z : ℝ) / T) * M * ∑ c ∈ s, ‖v c‖ ^ 2 := by
  have hpos := fixedAngular_translated_meanSquare hMV hC s v Z M hs hzero hM ℓ u
    (a := T) (b := 2 * T) (by linarith)
  have hneg := fixedAngular_translated_meanSquare hMV hC s v Z M hs hzero hM ℓ u
    (a := -2 * T) (b := -T) (by linarith)
  have hsum := div_le_div_of_nonneg_right (add_le_add hpos hneg) hT.le
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_norm {a : Eisenstein} (ha : a ≠ 0) :
    idealExponentNorm (idealExponentOf a) = norm a := by
  unfold idealExponentNorm
  rw [associated_normNat (idealExponentOf_associated ha), normNat_cast]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_fullIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ fullIdealBall Y ↔ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rw [idealExponentOf_norm (mem_nonzeroNormBall.mp ha).2]
    exact (mem_nonzeroNormBall.mp ha).1
  · intro h
    exact Finset.mem_image.mpr ⟨idealExponentGenerator ν,
      mem_nonzeroNormBall.mpr ⟨by simpa only [idealExponentNorm,normNat_cast] using h,
        idealExponentGenerator_ne_zero ν⟩,idealExponentOf_generator ν⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor and pair-product multiplicities with a bounded number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_inj_primary {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : idealExponentOf a = idealExponentOf b) : a = b := by
  have hA := idealExponentOf_associated (primary_ne_zero ha)
  have hB := idealExponentOf_associated (primary_ne_zero hb)
  rw [h] at hA
  exact primary_associated_eq ha hb (hA.symm.trans hB)

lemma primary_divisor_card_exponents (T : Finset Eisenstein)
    (hT : ∀ a ∈ T, primary a) {b : Eisenstein} (hb : b ≠ 0) :
    (T.filter (fun a => a ∣ b)).card ≤
      ∏ p ∈ (idealExponentOf b).support, (idealExponentOf b p + 1) := by
  let D := T.filter (fun a => a ∣ b)
  have hinj : Set.InjOn idealExponentOf (D : Set Eisenstein) := by
    intro a ha c hc he
    exact idealExponentOf_inj_primary (hT a (Finset.mem_filter.mp ha).1)
      (hT c (Finset.mem_filter.mp hc).1) he
  have hsub : D.image idealExponentOf ⊆ Finset.Iic (idealExponentOf b) := by
    intro ν hν
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hν
    exact Finset.mem_Iic.mpr (idealExponentOf_le_of_dvd
      (primary_ne_zero (hT a (Finset.mem_filter.mp ha).1)) hb (Finset.mem_filter.mp ha).2)
  calc
    D.card = (D.image idealExponentOf).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Iic (idealExponentOf b)).card := Finset.card_le_card hsub
    _ = _ := by rw [Finsupp.card_Iic]; simp

lemma idealPrimeRepresentative_normNat_ge_two (p : EisensteinIdealPrime) :
    2 ≤ normNat (idealPrimeRepresentative p) := by
  have hp := idealPrimeRepresentative_irreducible p
  have hz := normNat_ne_zero hp.ne_zero
  have ho : normNat (idealPrimeRepresentative p) ≠ 1 := by
    intro h
    apply hp.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast, h]
    norm_num
  omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDivisorPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary-exponent ideal divisor bounds for the short-convolution
polynomials. No bound on the number of distinct prime bases is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma exponent_add_one_le_two_pow (n : ℕ) : (n : ℝ)+1 ≤ (2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have hnon : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    nlinarith

private lemma exponent_factor_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n : ℕ, (n:ℝ)+1 ≤ A*(2:ℝ)^(ε*n) := by
  let L : ℝ := ε*Real.log 2
  have hL : 0 < L := mul_pos hε (Real.log_pos (by norm_num))
  refine ⟨1+1/L,by linarith [div_pos (zero_lt_one : (0:ℝ) < 1) hL],?_⟩
  intro n
  have hE1 : 1 ≤ Real.exp (L*n) := Real.one_le_exp_iff.mpr (by positivity)
  have hn : (n:ℝ) ≤ Real.exp (L*n)/L := by
    apply (le_div_iff₀ hL).mpr
    nlinarith [Real.add_one_le_exp (L*n)]
  have hE : Real.exp (L*n) = (2:ℝ)^(ε*n) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    dsimp [L]
    congr 1
    ring
  calc
    _ ≤ Real.exp (L*n)/L+Real.exp (L*n) := add_le_add hn hE1
    _ = (1+1/L)*Real.exp (L*n) := by ring
    _ = _ := by rw [hE]

/-- The full ideal divisor product is bounded by every positive norm
power. Small prime ideals form a finite set, while large prime ideals
absorb every exponent directly. -/
theorem ideal_divisor_product_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : EisensteinIdealExponent,
      (∏ p ∈ ν.support, ((ν p:ℝ)+1)) ≤ C*idealExponentNorm ν^ε := by
  obtain ⟨A,hA,hA_bound⟩ := exponent_factor_uniform hε
  let R : ℝ := (2:ℝ)^(1/ε)
  let T : Finset EisensteinIdealPrime :=
    (fullIdealBall R).biUnion (fun ν => ν.support)
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num),one_div_mul_cancel hε.ne',Real.rpow_one]
  have hT (p : EisensteinIdealPrime) :
      (normNat (idealPrimeRepresentative p):ℝ) ≤ R → p ∈ T := by
    intro hp
    apply Finset.mem_biUnion.mpr
    refine ⟨Finsupp.single p 1,?_,by simp⟩
    apply mem_fullIdealBall.mpr
    simpa only [idealExponentNorm_single,pow_one] using hp
  refine ⟨A^T.card,pow_pos (zero_lt_one.trans_le hA) _,?_⟩
  intro ν
  have hpoint : ∀ p ∈ ν.support, (ν p:ℝ)+1 ≤
      (if p ∈ T then A else 1)*(normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p) := by
    intro p hp
    have hNp : (2:ℝ) ≤ normNat (idealPrimeRepresentative p) := by
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    by_cases hpT : p ∈ T
    · simp only [ite_eq_left hpT]
      exact (hA_bound (ν p)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by norm_num) hNp (by positivity)) (zero_le_one.trans hA))
    · simp only [ite_eq_right hpT,one_mul]
      have hRp : R ≤ (normNat (idealPrimeRepresentative p):ℝ) := le_of_lt
        (lt_of_not_ge (fun h => hpT (hT p h)))
      have hbase : (2:ℝ) ≤ (normNat (idealPrimeRepresentative p):ℝ)^ε := by
        rw [← hRe]
        exact Real.rpow_le_rpow hR.le hRp hε.le
      calc
        _ ≤ (2:ℝ)^ν p := exponent_add_one_le_two_pow _
        _ ≤ ((normNat (idealPrimeRepresentative p):ℝ)^ε)^ν p :=
          pow_le_pow_left₀ (by norm_num) hbase _
        _ = _ := by rw [← Real.rpow_mul_natCast (by positivity)]
  have hprod := Finset.prod_le_prod (s := ν.support)
    (fun p _ => (by positivity : 0 ≤ (ν p:ℝ)+1)) hpoint
  rw [Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ ν.support, if p ∈ T then A else 1) ≤ A^T.card := by
    rw [Finset.prod_ite_mem,Finset.prod_const]
    exact pow_le_pow_right₀ hA (Finset.card_le_card Finset.inter_subset_right)
  have hnorm : (∏ p ∈ ν.support,
      (normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p)) = idealExponentNorm ν^ε := by
    calc
      _ = ∏ p ∈ ν.support, ((normNat (idealPrimeRepresentative p):ℝ)^ν p)^ε := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ = (∏ p ∈ ν.support, (normNat (idealPrimeRepresentative p):ℝ)^ν p)^ε :=
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity) ε
      _ = _ := by rw [idealExponentNorm_eq_prod]
  rw [hnorm] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))

/-- Arbitrary primary divisors, with no squarefree or bounded-prime-support
restriction on the ambient element. -/
theorem primary_divisor_card_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ a ∈ T, primary a) → ∀ b : Eisenstein, b ≠ 0 →
      ((T.filter (fun a => a ∣ b)).card : ℝ) ≤ C*norm b^ε := by
  obtain ⟨C,hC,hbound⟩ := ideal_divisor_product_small_power hε
  refine ⟨C,hC,?_⟩
  intro T hT b hb
  have h : ((T.filter (fun a => a ∣ b)).card : ℝ) ≤
      ((∏ p ∈ (idealExponentOf b).support, (idealExponentOf b p+1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (primary_divisor_card_exponents T hT hb)
  push_cast at h
  exact h.trans ((hbound (idealExponentOf b)).trans_eq (by rw [idealExponentOf_norm hb]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveDualConjugation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation preserves the normalized dual moment and reverses the
Mellin height. Thus the cubic sieve controls the actual dual coefficients. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma star_mellinPhase (u x : ℝ) : star (mellinPhase u x) = mellinPhase (-u) x := by
  change (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,Complex.ofReal_neg]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeFrequencyBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative cubic-sieve bounds on the actual decomposed frequencies.
The residual factor includes the ramified part; the cube variable causes only
an exclusion and therefore costs its cardinality. No exceptional-moment
estimate is assumed here. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

/-- Both orientations of the published cubic large sieve on a frequency
block `r*p*q²*j³`, with the cube and ramified multiplicities explicit. -/
theorem residualFrequency_sieve_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (B R P Q J : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ U) →
      (∀ q ∈ Q, primary q ∧ Squarefree q ∧ norm q ≤ V) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ residualCubeSupport R P Q J, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
        (R.card:ℝ)*J.card*C₀ *
          min ((Q.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((P.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))) *
            ∑ b ∈ B, ‖β b‖^2 := by
  intro ε hε
  obtain ⟨C₀,hC,hsharp⟩ := finiteCubicBound_sharp ε hε
  refine ⟨C₀,hC,?_⟩
  intro B R P Q J N U V hN hU hV hB hP hQ β
  have hp := hsharp B P U N hU hN hB hP
  have hq := hsharp B Q V N hV hN hB hQ
  apply (residualCubeSupport_mass_le B R P Q J (fun b hb => (hB b hb).1) β).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    _ ≤ (R.card:ℝ) *
        min ((Q.card:ℝ)*J.card*(C₀*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))))
            ((P.card:ℝ)*J.card*(C₀*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact min_le_min (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left hq (by positivity))
    _ = _ := by
      have h₁ : (Q.card:ℝ)*J.card*(C₀*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))) =
          (J.card:ℝ)*C₀*((Q.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))) := by ring
      have h₂ : (P.card:ℝ)*J.card*(C₀*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))) =
          (J.card:ℝ)*C₀*((P.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))) := by ring
      rw [h₁,h₂,← mul_min_of_nonneg _ _ (by positivity : 0 ≤ (J.card:ℝ)*C₀)]
      ring

/-- Restricting the actual frequencies, for instance to noncubes and a norm
dyad, can only decrease the positive quadratic mass. -/
theorem frequency_subset_mass_le (H F B : Finset Eisenstein)
    (hHF : H ⊆ F) (β : Eisenstein → ℂ) :
    (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
      ∑ h ∈ F, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2 :=
  Finset.sum_le_sum_of_subset_of_nonneg hHF (fun _ _ _ => sq_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeOrdinaryBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary-sieve orientation on actual ramified/cube frequency blocks. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma residual_mixedCubic_identity {b p q : Eisenstein}
    (hb : primary b) (hp : primary p) (hq : primary q) (r j : Eisenstein) :
    cubicSymbol b (r*p*q^2*j^3) = cubicSymbol b (r*j^3)*mixedCubic p q b := by
  have he : cubicSymbol b (p*q^2) = mixedCubic p q b := by
    rw [cubicSymbol_mul_upper hb,cubicSymbol_pow_upper hb,cubicSymbol_sq_eq_star hb,
      cubic_reciprocity hb hp,cubic_reciprocity hb hq]
    rfl
  rw [show r*p*q^2*j^3 = (r*j^3)*(p*q^2) by ring,cubicSymbol_mul_upper hb,he]

/-- Huxley's inequality controls the third noncube orientation. The ramified
and cube variables contribute only their explicit finite cardinalities. -/
theorem coprimeResidual_ordinary_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B R J : Finset Eisenstein)
      (P : Finset (Eisenstein × Eisenstein)) (Q Z : ℝ), 1 ≤ Q → 1 ≤ Z →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ b ∈ B, primary b ∧ norm b ≤ Z) → ∀ v : Eisenstein → ℂ,
      (∑ h ∈ coprimeResidualSupport R J P, ‖∑ b ∈ B, v b*cubicSymbol b h‖^2) ≤
        (R.card:ℝ)*J.card*C*Q^ε*(Q^2+Z)*∑ b ∈ B, ‖v b‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_finite hHuxley hε
  refine ⟨C,hC,?_⟩
  intro B R J P Q Z hQ hZ hP hB v
  have hrow (r j : Eisenstein) :
      (∑ p ∈ P, ‖∑ b ∈ B, v b*cubicSymbol b (r*p.1*p.2^2*j^3)‖^2) ≤
        C*Q^ε*(Q^2+Z)*∑ b ∈ B, ‖v b‖^2 := by
    have hh := hbound Q Z hQ hZ P B hP
      (fun b hb => ⟨primary_ne_zero (hB b hb).1,(hB b hb).2⟩)
      (fun b => v b*cubicSymbol b (r*j^3))
    have he : (∑ p ∈ P, ‖∑ b ∈ B, v b*cubicSymbol b (r*p.1*p.2^2*j^3)‖^2) =
        ∑ p ∈ P, ‖∑ b ∈ B, (v b*cubicSymbol b (r*j^3))*mixedCubic p.1 p.2 b‖^2 := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 2
      apply Finset.sum_congr rfl
      intro b hb
      rw [residual_mixedCubic_identity (hB b hb).1 (hP p hp).1.1 (hP p hp).1.2.1]
      ring
    rw [he]
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro b hb
    rw [norm_mul,mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (by
      simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hB b hb).1 _) 2)
  calc
    _ ≤ ∑ t ∈ (R.product J).product P,
        ‖∑ b ∈ B, v b*cubicSymbol b (t.1.1*t.2.1*t.2.2^2*t.1.2^3)‖^2 :=
      Finset.sum_image_le_of_nonneg (s := (R.product J).product P)
        (g := fun t => t.1.1*t.2.1*t.2.2^2*t.1.2^3)
        (f := fun h => ‖∑ b ∈ B, v b*cubicSymbol b h‖^2) (fun _ _ => sq_nonneg _)
    _ = ∑ r ∈ R, ∑ j ∈ J, ∑ p ∈ P,
        ‖∑ b ∈ B, v b*cubicSymbol b (r*p.1*p.2^2*j^3)‖^2 := by
      exact (Finset.sum_product (R.product J) P _).trans (Finset.sum_product R J _)
    _ ≤ ∑ _r ∈ R, ∑ _j ∈ J,
        C*Q^ε*(Q^2+Z)*∑ b ∈ B, ‖v b‖^2 :=
      Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun j _ => hrow r j))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeSieveAssembly
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All three sieve orientations on the same concrete noncube frequency block. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeResidualSupport_subset (R J S T : Finset Eisenstein) :
    coprimeResidualSupport R J (coprimePairs S T) ⊆ residualCubeSupport R S T J := by
  intro n hn
  obtain ⟨⟨⟨r,j⟩,⟨s,t⟩⟩,hz,rfl⟩ := Finset.mem_image.mp hn
  have hz' := Finset.mem_product.mp hz
  have hrj := Finset.mem_product.mp hz'.1
  have hst := Finset.mem_product.mp (Finset.mem_filter.mp hz'.2).1
  apply Finset.mem_biUnion.mpr
  refine ⟨r,hrj.1,Finset.mem_image.mpr ⟨s*t^2*j^3,?_,?_⟩⟩
  · exact Finset.mem_image.mpr ⟨(s,t,j),Finset.mem_product.mpr
      ⟨hst.1,Finset.mem_product.mpr ⟨hst.2,hrj.2⟩⟩,rfl⟩
  · ring

/-- The two cubic estimates and the ordinary estimate apply to the same
positive mass; no exceptional-moment hypothesis is used. -/
theorem noncube_three_sieve_bounds (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (B R S T J H : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
        min ((R.card:ℝ)*J.card*C₁ *
          min ((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))))
          ((R.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N)) *
            ∑ b ∈ B, ‖β b‖^2 := by
  obtain ⟨C₁,hC₁,hcubic⟩ := residualFrequency_sieve_bound ε hε
  obtain ⟨C₂,hC₂,hordinary⟩ := coprimeResidual_ordinary_sieve hHuxley hε
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro B R S T J H N U V hN hU hV hB hS hT hH β
  have hc := (frequency_subset_mass_le H (residualCubeSupport R S T J) B
    (hH.trans (coprimeResidualSupport_subset R J S T)) β).trans
    (hcubic B R S T J N U V hN hU hV hB hS hT β)
  have hP : ∀ p ∈ coprimePairs S T,
      PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ U*V := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hst := Finset.mem_product.mp hp'.1
    refine ⟨⟨(hS p.1 hst.1).1,(hT p.2 hst.2).1,(hS p.1 hst.1).2.1,
      (hT p.2 hst.2).2.1,hp'.2⟩,?_⟩
    rw [pairConductor,norm_mul_eq]
    exact mul_le_mul (hS p.1 hst.1).2.2 (hT p.2 hst.2).2.2 (norm_nonneg _) (by linarith)
  have ho := (frequency_subset_mass_le H _ B hH β).trans
    (hordinary B R J (coprimePairs S T) (U*V) N
      (one_le_mul_of_one_le_of_one_le hU hV) hN hP
      (fun b hb => ⟨(hB b hb).1,(hB b hb).2.2⟩) β)
  rw [min_mul_of_nonneg _ _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact le_min hc ho

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform exponent saving applied to the actual finite frequency mass. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primary_support_card_le (S : Finset Eisenstein) {U : ℝ} (hU : 0 ≤ U)
    (hS : ∀ s ∈ S, primary s ∧ norm s ≤ U) : (S.card:ℝ) ≤ 18*U := by
  have hsub : S ⊆ nonzeroNormBall U := fun s hs =>
    mem_nonzeroNormBall.mpr ⟨(hS s hs).2,primary_ne_zero (hS s hs).1⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hU)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredHeightMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite frequency blocks retain the proved height mean, with an explicit
row count for the actual ramified and cube decomposition. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_dyadic_integral_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    ((∫ t in T..2*T, ∑ a ∈ S, f a t) + (∫ t in -2*T..-T, ∑ a ∈ S, f a t))/T =
      ∑ a ∈ S, ((∫ t in T..2*T, f a t)+(∫ t in -2*T..-T, f a t))/T := by
  rw [intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    ← Finset.sum_add_distrib,Finset.sum_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightAveraging
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive, normalized two-sided height averaging. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadicHeightMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ g t) :
    dyadicHeightMean f T ≤ dyadicHeightMean g T := by
  apply div_le_div_of_nonneg_right _ hT.le
  apply add_le_add
  · apply intervalIntegral.integral_mono_on (by linarith : T ≤ 2*T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨by linarith [ht.1],ht.2⟩
  · apply intervalIntegral.integral_mono_on (by linarith : -2*T ≤ -T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨ht.1,by linarith [ht.2]⟩

lemma dyadicHeightMean_const (C : ℝ) {T : ℝ} (hT : T ≠ 0) :
    dyadicHeightMean (fun _ => C) T = 2*C := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const,smul_eq_mul]
  field_simp
  ring

lemma dyadicHeightMean_le_const {f : ℝ → ℝ} (hf : Continuous f)
    {T C : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ C) :
    dyadicHeightMean f T ≤ 2*C :=
  (dyadicHeightMean_mono hf continuous_const hT h).trans_eq
    (dyadicHeightMean_const C hT.ne')

lemma dyadicHeightMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (T : ℝ) :
    dyadicHeightMean (fun t => f t+g t) T = dyadicHeightMean f T+dyadicHeightMean g T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

lemma dyadicHeightMean_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    dyadicHeightMean (fun t => ∑ a ∈ S, f a t) T = ∑ a ∈ S, dyadicHeightMean (f a) T :=
  finite_dyadic_integral_sum S f hf T

lemma dyadicHeightMean_const_mul (c : ℝ) (f : ℝ → ℝ) (T : ℝ) :
    dyadicHeightMean (fun t => c*f t) T = c*dyadicHeightMean f T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightMeanSquare
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite spectral expansion of the height-averaged square.
The diagonal and every off-diagonal pair are retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_normTwist (b : Eisenstein) : Continuous (fun u : ℝ => normTwist u b) := by
  unfold normTwist
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryNormMultiplicity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational norm fibers of arbitrary primary elements. An element of norm
`n` divides the rational integer `n` in the Eisenstein ring. Thus the proved
ideal divisor bound supplies the small multiplicity loss required by the
ordinary Montgomery--Vaughan input, without any prime-factor restriction. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_dvd_of_normNat_eq {b : Eisenstein} {n : ℕ} (hn : normNat b = n) :
    b ∣ (n : Eisenstein) := by
  rw [←hn,normNat_cast_eq_mul_conjugate]
  exact dvd_mul_right _ _

private lemma norm_natCast_eisenstein (n : ℕ) : norm (n : Eisenstein) = (n:ℝ)^2 := by
  change Complex.normSq (n:ℂ) = _
  simpa only [Complex.ofReal_natCast,pow_two] using Complex.normSq_ofReal (n:ℝ)

/-- Uniform small-power bound for positive rational norm fibers. -/
theorem primary_norm_fiber_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ b ∈ T, primary b) → ∀ n : ℕ, 0 < n →
      ((T.filter (fun b => normNat b = n)).card:ℝ) ≤ C*(n:ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power (half_pos hε)
  refine ⟨C,hC,?_⟩
  intro T hT n hn
  have hn0 : (n:Eisenstein) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsub : T.filter (fun b => normNat b = n) ⊆ T.filter (fun b => b ∣ (n:Eisenstein)) := by
    intro b hb
    obtain ⟨hbT,hbn⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hbT,primary_dvd_of_normNat_eq hbn⟩
  have hpower : norm (n:Eisenstein)^(ε/2) = (n:ℝ)^ε := by
    rw [norm_natCast_eisenstein,←Real.rpow_natCast_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    ((hdiv T hT (n:Eisenstein) hn0).trans_eq (by rw [hpower]))

lemma primary_norm_fiber_length_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset Eisenstein),
      (∀ b ∈ T, primary b) → ∀ Z n : ℕ, n ∈ Finset.Icc 1 Z →
      ((T.filter (fun b => normNat b = n)).card:ℝ) ≤ C*(Z:ℝ)^ε := by
  obtain ⟨C,hC,hfiber⟩ := primary_norm_fiber_small_power hε
  refine ⟨C,hC,?_⟩
  intro T hT Z n hn
  obtain ⟨hn1,hnZ⟩ := Finset.mem_Icc.mp hn
  exact (hfiber T hT n (by omega)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnZ) hε.le) hC.le)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArbitraryHeightMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary height means for arbitrary primary coefficient supports,
including sharp norm cells and every translated angular mode. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_finite_character_height (B : Finset Eisenstein)
    (β : Eisenstein → ℂ) (h : Eisenstein) (ℓ : ℤ) (u : ℝ) :
    Continuous (fun t => ∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)) := by
  apply continuous_finsetSum
  intro b hb
  change Continuous (fun t => (β b*cubicSymbol b h*theta ℓ b)*normTwist (t+u) b)
  exact continuous_const.mul ((continuous_normTwist b).comp (continuous_id.add continuous_const))

/-- Exact norm-fiber cost for the finite family. Character factors can
only reduce the coefficient energy. -/
theorem finite_character_height_mean {C M T : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hM : 0 ≤ M) (hT : 0 < T)
    (B H : Finset Eisenstein) (β : Eisenstein → ℂ) (Z : ℕ)
    (hB : ∀ b ∈ B, primary b)
    (hZ : ∀ b ∈ B, normNat b ∈ Finset.Icc 1 Z)
    (hmult : ∀ n ∈ Finset.Icc 1 Z, ((B.filter (fun b => normNat b = n)).card:ℝ) ≤ M)
    (ℓ : ℤ) (u : ℝ) :
    dyadicHeightMean (fun t => ∑ h ∈ H,
      ‖∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*M*H.card*∑ b ∈ B, ‖β b‖^2 := by
  have hc (h : Eisenstein) := (continuous_finite_character_height B β h ℓ u).norm.pow 2
  rw [dyadicHeightMean_sum H (fun h t =>
    ‖∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2)
      (fun h _ => hc h)]
  have hrow (h : Eisenstein) :
      dyadicHeightMean (fun t =>
        ‖∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*M*∑ b ∈ B, ‖β b‖^2 := by
    have hm := fixedAngular_translated_dyadicMeanSquare hMV hC B
      (fun b => β b*cubicSymbol b h) Z M hZ
      (fun b hb => primary_ne_zero (hB b hb)) hmult ℓ u hT
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro b hb
    apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
    rw [norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hB b hb) h)
  calc
    _ ≤ ∑ _h ∈ H, 2*C*(1+(Z:ℝ)/T)*M*∑ b ∈ B, ‖β b‖^2 :=
      Finset.sum_le_sum (fun h _ => hrow h)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- With no fixed number of prime factors, the proved primary norm-fiber
bound gives an arbitrarily small length loss, uniformly in all twists. -/
theorem arbitrary_primary_height_mean {C ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (B H : Finset Eisenstein) (β : Eisenstein → ℂ) (Z : ℕ),
      (∀ b ∈ B, primary b) → (∀ b ∈ B, normNat b ∈ Finset.Icc 1 Z) →
      ∀ (ℓ : ℤ) (u T : ℝ), 0 < T →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
        2*C*D*(1+(Z:ℝ)/T)*(Z:ℝ)^ε*H.card*∑ b ∈ B, ‖β b‖^2 := by
  obtain ⟨D,hD,hfiber⟩ := primary_norm_fiber_length_bound hε
  refine ⟨D,hD,?_⟩
  intro B H β Z hB hZ ℓ u T hT
  have hm := finite_character_height_mean hMV hC
    (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg Z) _)) hT B H β Z hB hZ
    (hfiber B hB Z) ℓ u
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Fourier decay for the fixed wider log-norm cutoff used by the
actual prime convolution. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma wideGramExp_deriv_bound (M : ℝ) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : ℕ), i ≤ n → ∀ u : ℝ, |u| ≤ 2*M →
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ u ∈ Set.Icc (-2*M) (2*M),
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D :=
    isCompact_Icc.exists_bound_of_continuousOn
      (gramExp_contDiff.continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
  choose B hB using hb
  let D := 1 + ∑ i ∈ Finset.range (n+1), |B i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n+1), |B i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro i hi u hu
  have hbi : |B i| ≤ ∑ j ∈ Finset.range (n+1), |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_range.mpr (by omega))
  exact (hB i u ⟨by linarith [(abs_le.mp hu).1], (abs_le.mp hu).2⟩).trans
    ((le_abs_self (B i)).trans (hbi.trans (by dsimp [D]; linarith)))

lemma wideGramExp_scale_growth {M c u : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hu : |u| ≤ 2*M) :
    1+c ≤ Real.exp M * (1+‖c • gramExp u‖) := by
  have hE : 1 ≤ Real.exp M := Real.one_le_exp hM
  have hEu : 1 ≤ Real.exp M * Real.exp (u/2) := by
    rw [← Real.exp_add]
    simpa using Real.exp_le_exp.mpr (show (0:ℝ) ≤ M + u/2 by
      linarith [(abs_le.mp hu).1])
  have hEc := mul_le_mul_of_nonneg_left hEu hc
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, gramExp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith

theorem schwartz_wideGramExp_comp_uniform (M : ℝ) (hM : 0 ≤ M) (F : 𝓢(ℂ, ℂ)) (n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ u : ℝ, |u| ≤ 2*M →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤ C := by
  obtain ⟨D, hD, hderiv⟩ := wideGramExp_deriv_bound M n
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp M)^L * 2^L * S
  have hS : 0 ≤ S := by positivity
  have hH : 0 ≤ H := by positivity
  refine ⟨(n.factorial : ℝ)*H*D^n, by positivity, ?_⟩
  intro c hc u hu
  have hc1 : 0 < 1+c := by positivity
  have hC (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ ≤ H / (1+c)^L := by
    rw [le_div_iff₀' (pow_pos hc1 L)]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (L,n)) (k := L) (n := i) (le_refl L) hi F (c • gramExp u)
    calc
      _ ≤ (Real.exp M * (1+‖c • gramExp u‖))^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ := by
        gcongr
        exact wideGramExp_scale_growth hM hc hu
      _ = (Real.exp M)^L * ((1+‖c • gramExp u‖)^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖) := by rw [mul_pow]; ring
      _ ≤ (Real.exp M)^L * (2^L*S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = H := by dsimp [H]; ring
  have hDb (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun v => c • gramExp v) u‖ ≤ ((1+c)*D)^i := by
    rw [iteratedFDeriv_const_smul_apply' (gramExp_contDiff.of_le (mod_cast le_top)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ ≤ c*D := mul_le_mul_of_nonneg_left (hderiv i hin u hu) hc
      _ ≤ (1+c)*D := by nlinarith
      _ ≤ ((1+c)*D)^i := le_self_pow₀ (by nlinarith) (by omega)
  have hb := norm_iteratedFDeriv_comp_le (F.smooth ⊤) (gramExp_contDiff.const_smul c)
    (n := n) (mod_cast le_top) u hC hDb
  calc
    _ ≤ (1+c)^K * ((n.factorial : ℝ)*(H/(1+c)^L)*((1+c)*D)^n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (n.factorial : ℝ)*H*D^n := by
      dsimp [L]
      rw [pow_add, mul_pow]
      field_simp


lemma wideAnnularLogSchwartz_deriv_zero (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (c u : ℝ) (n : ℕ)
    (hu : ¬ |u| ≤ 2*M) : iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u = 0 := by
  by_contra hn
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := wideAnnularLogSchwartz M hM F c) n hn
  have hb := tsupport_smul_subset_left ((wideGramLogBump M hM) : ℝ → ℝ)
    (fun v => F (c • gramExp v)) hs
  rw [(wideGramLogBump M hM).tsupport_eq] at hb
  exact hu (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, wideGramLogBump] using hb)

theorem wideAnnularLogSchwartz_seminorm_uniform (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤ C := by
  choose C hC hbound using fun i => schwartz_wideGramExp_comp_uniform M hM.le F i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)))
  refine ⟨(2*M)^k * B, by positivity, ?_⟩
  intro c hc
  have hp : 0 < (1+c)^K := pow_pos (by positivity) _
  rw [← le_div_iff₀' hp]
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2*M
  · rw [le_div_iff₀' hp]
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (wideGramLogBump M hM).contDiff
      ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
    have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖ ≤ B := by
      calc
        _ ≤ (1+c)^K * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
              ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖ :=
          mul_le_mul_of_nonneg_left hd hp.le
        _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
              ((1+c)^K * ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ B := by
          apply Finset.sum_le_sum
          intro i hi
          have hb : ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ ≤
              SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) := by
            have hb := SchwartzMap.le_seminorm ℝ 0 i (wideGramBumpSchwartz M hM) u
            rw [show (wideGramBumpSchwartz M hM : ℝ → ℝ) = ((wideGramLogBump M hM) : ℝ → ℝ) from rfl] at hb
            simpa only [pow_zero, one_mul] using hb
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
            (hbound (n-i) c hc u hu) (by positivity) (by positivity)
    calc
      _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖) := by ring
      _ ≤ (2*M)^k * B := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
  · rw [wideAnnularLogSchwartz_deriv_zero M hM F c u n hu, norm_zero, mul_zero]
    positivity

lemma wideAnnularLogSchwartz_eq_wideGramLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ) =
      wideGramLogSchwartz M hM W hW hW' ρ := by
  ext u
  simp only [wideAnnularLogSchwartz_apply M hM, wideGramLogSchwartz_apply, wideGramLogKernel,
    normProfileFourierSchwartz_apply]
  congr 2
  simp only [gramExp, Complex.real_smul, Complex.ofReal_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm denominator in the actual Poisson formula stays in its
Mellin kernel. No real power is inserted into the prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma normDenominatorMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (normDenominatorMellinCoefficient M hM W hW hW' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integrable


lemma normDenominatorLogSchwartz_eq_annular (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ =
      SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ)) := by
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz]
  rfl

lemma normDenominatorFourier_seminorm_uniform (M : ℝ) (hM : 0 < M)
    (F : 𝓢(ℂ,ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c → (1+c)^K * SchwartzMap.seminorm ℝ k n
      (𝓕 (SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM F c))) ≤ C := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun c => (1+c)^K • wideAnnularLogSchwartz M hM F c
  have hb : Bornology.IsVonNBounded ℝ (f '' Ici 0) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,hc⟩ := wideAnnularLogSchwartz_seminorm_uniform M hM F i.1 i.2 K
    refine ⟨C+1,by linarith,?_⟩
    intro c hc0
    have hc0' : 0 ≤ c := hc0
    change SchwartzMap.seminorm ℝ i.1 i.2 ((1+c)^K • wideAnnularLogSchwartz M hM F c) < _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (pow_pos (by linarith [hc0']) _)]
    exact (hc c hc0).trans_lt (by linarith)
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)).comp
      ((SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)).restrictScalars ℝ)
  have hA := hb.image A
  obtain ⟨C,hC,hc⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hA (k,n)
  refine ⟨C,hC,?_⟩
  intro c hc0
  have h := hc (A (f c)) ⟨f c,⟨c,hc0,rfl⟩,rfl⟩
  change SchwartzMap.seminorm ℝ k n (A ((1+c)^K • wideAnnularLogSchwartz M hM F c)) < C at h
  rw [map_smul,map_smul_eq_mul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (by linarith) _)] at h
  exact h.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormMellinMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrated decay with polynomial Mellin-height weights. This controls
truncated shifts in the dispersion kernel. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem normDenominatorMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ C := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k * ∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun t => by positivity))
  obtain ⟨C₀,hC₀,hc₀⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') 0 0 (2*A)
  obtain ⟨C₁,hC₁,hc₁⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') (B+k) 0 (2*A)
  refine ⟨D*(C₀+C₁)+1,by positivity,?_⟩
  intro ρ hρ
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have h₀ := hc₀ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  have h₁ := hc₁ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [← normDenominatorLogSchwartz_eq_annular] at h₀ h₁
  have hb : (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ D*(C₀+C₁) := by
    calc
      _ ≤ (1+Real.sqrt ρ)^(2*A) * (D *
          (SchwartzMap.seminorm ℝ 0 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
           SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)))) :=
        mul_le_mul hs h (integral_nonneg (fun t => by positivity)) (by positivity)
      _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
        (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) hD
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the Fourier-transform frequency to the arithmetic height in
N(n)^(it). The fixed factor 2π stays in the actual kernel. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

lemma arithmeticMellinCoefficient_continuous (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Continuous (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).continuous.comp
    (continuous_id.div_const _)

lemma arithmeticMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Integrable (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).comp_div
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial integral moments after the exact 2π rescaling. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace CubicFirstMoment

lemma arithmetic_mellin_moment_scale (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) (k : ℕ) (t : ℝ) :
    ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖ =
      (2*Real.pi)^k*(‖t/(2*Real.pi)‖^k*
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ (t/(2*Real.pi))‖) := by
  have hc : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  simp only [arithmeticMellinCoefficient,norm_div,Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi),div_pow]
  field_simp

theorem arithmeticMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖) ≤ C := by
  obtain ⟨C,hC,hb⟩ := normDenominatorMellinCoefficient_moment_decay M hM V hV hV' q k
  refine ⟨(2*Real.pi)^(k+1)*C,by positivity,?_⟩
  intro ρ hρ
  simp_rw [arithmetic_mellin_moment_scale]
  have he := Measure.integral_comp_div
    (fun t : ℝ => ‖t‖^k*‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖) (2*Real.pi)
  rw [integral_const_mul,he,abs_of_pos (by positivity : 0 < 2*Real.pi),smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (hb ρ hρ) (pow_nonneg (by positivity : 0 ≤ 2*Real.pi) (k+1))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite low-conductor frequency support: a small
nonzero core times a bounded cube, with precisely the cubes removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma lowNoncubeSupport_card {V J : ℝ} (hV : 0 ≤ V) (hJ : 0 ≤ J) :
    ((lowNoncubeSupport V J).card:ℝ) ≤ 324*V*J := by
  have hc : (lowNoncubeSupport V J).card ≤
      ((nonzeroNormBall V).product (nonzeroNormBall J)).card :=
    (Finset.card_filter_le _ _).trans (Finset.card_image_le)
  have hb : (((nonzeroNormBall V).product (nonzeroNormBall J)).card:ℝ) =
      ((nonzeroNormBall V).card:ℝ)*((nonzeroNormBall J).card:ℝ) := by
    exact_mod_cast Finset.card_product (nonzeroNormBall V) (nonzeroNormBall J)
  calc
    _ ≤ (((nonzeroNormBall V).product (nonzeroNormBall J)).card:ℝ) := Nat.cast_le.mpr hc
    _ = _ := hb
    _ ≤ (18*V)*(18*J) := mul_le_mul (nonzeroNormBall_card_le hV) (nonzeroNormBall_card_le hJ)
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicCoreCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coverage of a noncube frequency by either the low-core set or
a ramified/squarefree pair of large conductor. No decomposition is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_cube (j : Eisenstein) : norm (j^3) = norm j^3 := by
  simp only [pow_succ,norm_mul_eq,pow_zero,norm_one_eq]

lemma cube_part_norm_bound {h v j : Eisenstein} {H : ℝ}
    (hv : v ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H) :
    norm j ≤ H^(1/3:ℝ) := by
  have hcube : norm j^3 ≤ H := by
    calc
      _ ≤ norm v*norm j^3 := le_mul_of_one_le_left (pow_nonneg (norm_nonneg j) _) (one_le_norm hv)
      _ = norm h := by rw [heq,norm_mul_eq,norm_cube]
      _ ≤ H := hh
  have hp := Real.rpow_le_rpow (pow_nonneg (norm_nonneg j) 3) hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (norm j^3)^(1/3:ℝ) = norm j := by
    rw [← Real.rpow_natCast (norm j) 3,← Real.rpow_mul (norm_nonneg j)]
    norm_num
  rwa [he] at hp

lemma mem_lowNoncubeSupport_of_core {h v j : Eisenstein} {V H : ℝ}
    (hv : v ≠ 0) (hj : j ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H)
    (hsmall : norm v ≤ V) (hn : ¬∃ a : Eisenstein, a^3 = h) :
    h ∈ lowNoncubeSupport V (H^(1/3:ℝ)) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(v,j),?_,heq.symm⟩,hn⟩
  exact Finset.mem_product.mpr ⟨mem_nonzeroNormBall.mpr ⟨hsmall,hv⟩,
    mem_nonzeroNormBall.mpr ⟨cube_part_norm_bound hv heq hh,hj⟩⟩

theorem noncube_large_core_decomposition {h : Eisenstein} {V H : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ H) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (H^(1/3:ℝ))) :
    ∃ r s t j : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      j ≠ 0 ∧ h = r*s*t^2*j^3 ∧
      V/729 < norm s*norm t^2 ∧ norm s*norm t^2 ≤ H ∧ norm j ≤ H^(1/3:ℝ) := by
  obtain ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq⟩ := full_cube_decomposition hh0
  have hv : r*s*t^2 ≠ 0 := mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs))
    (pow_ne_zero _ (primary_ne_zero ht))
  have hcore : h = (r*s*t^2)*j^3 := heq
  have hlarge : V < norm (r*s*t^2) := lt_of_not_ge (fun hsmall => hnot
    (mem_lowNoncubeSupport_of_core hv hj hcore hh hsmall hn))
  have hc : norm (r*s*t^2) = norm r*(norm s*norm t^2) := by
    rw [norm_mul_eq,norm_mul_eq]
    have ht2 : norm (t^2) = norm t^2 := by simp only [pow_two,norm_mul_eq]
    rw [ht2]
    ring
  have hD0 : 0 ≤ norm s*norm t^2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hsmall : norm (r*s*t^2) ≤ norm h := by
    calc
      _ ≤ norm (r*s*t^2)*norm (j^3) :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_norm (pow_ne_zero _ hj))
      _ = norm h := by simp only [hcore,norm_mul_eq]
  refine ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq,?_,?_,cube_part_norm_bound hv hcore hh⟩
  · apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 729)).mpr
    rw [hc] at hlarge
    nlinarith [mul_le_mul_of_nonneg_right hrN hD0]
  · apply le_trans _ (hsmall.trans hh)
    rw [hc]
    exact le_mul_of_one_le_left hD0 (one_le_norm hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of all noncube frequencies outside the small-core set
by the actual coprime ramified/squarefree blocks used in the moment bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coreDyadicConductor_pos (i j : ℕ) : 0 < coreDyadicConductor i j := by
  unfold coreDyadicConductor
  positivity

lemma squarefreePrimaryDyad_gramDyad {i : ℕ} {s : Eisenstein}
    (hs : s ∈ squarefreePrimaryDyad i) : gramDyad ((2:ℝ)^i) s := by
  obtain ⟨hf,hp,hq⟩ := mem_squarefreePrimaryDyad.mp hs
  have hlog := (mem_frequencyDyad.mp hf).2
  refine ⟨hp,hq,(frequencyDyad_norm hf).1,?_⟩
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (normNat s)
  rw [hlog] at hlt
  have hcast : norm s < (2:ℝ)^(i+1) := by
    rw [← normNat_cast]
    exact_mod_cast hlt
  simpa only [pow_succ,mul_comm] using hcast

lemma real_cube_scale_bound {x B D : ℝ} (hx : 0 ≤ x) (hD : 0 < D)
    (h : x^3*D ≤ B) : x ≤ (B/D)^(1/3:ℝ) := by
  have hc : x^3 ≤ B/D := (le_div_iff₀ hD).mpr h
  have hp := Real.rpow_le_rpow (pow_nonneg hx 3) hc (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (x^3)^(1/3:ℝ) = x := by
    rw [← Real.rpow_natCast x 3,← Real.rpow_mul hx]
    norm_num
  rwa [he] at hp

theorem noncube_mem_coreDyadicBlock {h : Eisenstein} {V B : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ B) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) :
    ∃ z ∈ largeCoreDyadicIndices V B, h ∈ coreDyadicBlock B z.1 z.2 := by
  obtain ⟨r,s,t,c,hr,hrN,hs,ht,hss,hst,hcop,hc,heq,hlarge,hcore,hcN⟩ :=
    noncube_large_core_decomposition hh0 hh hn hnot
  let i := Nat.log 2 (normNat s)
  let j := Nat.log 2 (normNat t)
  have hsD : s ∈ squarefreePrimaryDyad i := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩,hs,hss⟩
  have htD : t ∈ squarefreePrimaryDyad j := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩,ht,hst⟩
  have hsG := squarefreePrimaryDyad_gramDyad hsD
  have htG := squarefreePrimaryDyad_gramDyad htD
  have hDlo : coreDyadicConductor i j ≤ norm s*norm t^2 := by
    exact mul_le_mul hsG.2.2.1 (pow_le_pow_left₀ (by positivity) htG.2.2.1 2)
      (by positivity) (norm_nonneg s)
  have hDhi : norm s*norm t^2 < 8*coreDyadicConductor i j := by
    have ht2 : norm t^2 < (2*(2:ℝ)^j)^2 :=
      (pow_lt_pow_left₀ htG.2.2.2 (norm_nonneg t) (by norm_num : (2:ℕ) ≠ 0))
    calc
      _ < (2*(2:ℝ)^i)*((2*(2:ℝ)^j)^2) := mul_lt_mul hsG.2.2.2 ht2.le
        (sq_pos_of_pos (zero_lt_one.trans_le (one_le_norm (primary_ne_zero ht)))) (by positivity)
      _ = _ := by unfold coreDyadicConductor; ring
  have hDb : coreDyadicConductor i j ≤ B := hDlo.trans hcore
  have hidx : ∀ (a : Eisenstein), primary a → norm a ≤ B →
      Nat.log 2 (normNat a) < Nat.log 2 ⌊B⌋₊+1 := by
    intro a ha haB
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    rwa [normNat_cast]
  have hsB : norm s ≤ B := (le_mul_of_one_le_right (norm_nonneg s)
    (one_le_pow₀ (one_le_norm (primary_ne_zero ht)))).trans hcore
  have htB : norm t ≤ B := by
    have htt : norm t ≤ norm t^2 := by
      nlinarith [one_le_norm (primary_ne_zero ht)]
    exact htt.trans ((le_mul_of_one_le_left (sq_nonneg _) (one_le_norm (primary_ne_zero hs))).trans hcore)
  have hcube : norm c^3*coreDyadicConductor i j ≤ B := by
    have hn : norm h = norm r*(norm s*norm t^2)*norm c^3 := by
      simp only [heq,norm_mul_eq,norm_cube,pow_two]
      ring
    calc
      _ ≤ norm c^3*(norm s*norm t^2) := mul_le_mul_of_nonneg_left hDlo (pow_nonneg (norm_nonneg c) _)
      _ ≤ norm r*(norm s*norm t^2)*norm c^3 := by
        nlinarith [mul_le_mul_of_nonneg_right
          (one_le_norm hr) (mul_nonneg (mul_nonneg (norm_nonneg s) (sq_nonneg (norm t)))
            (pow_nonneg (norm_nonneg c) 3))]
      _ = norm h := hn.symm
      _ ≤ B := hh
  refine ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (hidx s hs hsB),Finset.mem_range.mpr (hidx t ht htB)⟩,
    ⟨by dsimp only; linarith,hDb⟩⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨((r,c),(s,t)),Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨mem_nonzeroNormBall.mpr ⟨hrN,hr⟩,mem_nonzeroNormBall.mpr
      ⟨real_cube_scale_bound (norm_nonneg c) (coreDyadicConductor_pos i j) hcube,hc⟩⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsD,htD⟩,hcop⟩⟩,heq.symm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicFrequencyMassSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete small-core / dyadic-core partition of a finite noncube
mass. Multiple arithmetic decompositions cost no frequency multiplicity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem noncube_frequency_mass_split (H : Finset Eisenstein) {V B : ℝ}
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h)
    (f : Eisenstein → ℝ) (hf : ∀ h, 0 ≤ f h) :
    (∑ h ∈ H, f h) ≤
      (∑ h ∈ H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))), f h)+
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
  let I := (largeCoreDyadicIndices V B).sigma (fun z => coreDyadicBlock B z.1 z.2)
  let F : Sigma (fun _ : ℕ × ℕ => Eisenstein) → Eisenstein := Sigma.snd
  have hcover : H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) ⊆ I.image F := by
    intro h hh
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hh
    obtain ⟨z,hz,hb⟩ := noncube_mem_coreDyadicBlock (hH h hm).1
      (hH h hm).2.1 (hH h hm).2.2 hn
    exact Finset.mem_image.mpr ⟨⟨z,h⟩,Finset.mem_sigma.mpr ⟨hz,hb⟩,rfl⟩
  have hsum : (∑ h ∈ H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))), f h) ≤
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hf h)).trans
    apply (Finset.sum_image_le_of_nonneg (s := I) (g := F) (f := f) (fun h _ => hf h)).trans_eq
    exact Finset.sum_sigma _ _ _
  rw [← Finset.sum_filter_add_sum_filter_not H
    (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))) f]
  exact add_le_add le_rfl hsum

lemma coreDyadicCubeFactors_card_weight {B : ℝ} (hB : 0 ≤ B) (i j : ℕ) :
    ((coreDyadicCubeFactors B i j).card:ℝ)*(coreDyadicConductor i j)^(1/3:ℝ) ≤
      18*B^(1/3:ℝ) := by
  have hD := coreDyadicConductor_pos i j
  calc
    _ ≤ (18*(B/coreDyadicConductor i j)^(1/3:ℝ))*
        (coreDyadicConductor i j)^(1/3:ℝ) :=
      mul_le_mul_of_nonneg_right (nonzeroNormBall_card_le (Real.rpow_nonneg (div_nonneg hB hD.le) _))
        (Real.rpow_nonneg hD.le _)
    _ = _ := by
      rw [Real.div_rpow hB hD.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hD (1/3:ℝ))]

lemma largeCoreDyadicIndices_card (V B : ℝ) :
    (largeCoreDyadicIndices V B).card ≤ (Nat.log 2 ⌊B⌋₊+1)^2 := by
  unfold largeCoreDyadicIndices
  apply (Finset.card_filter_le _ _).trans
  exact le_of_eq ((Finset.card_product _ _).trans (by simp only [Finset.card_range,pow_two]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoreBlockGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric cube cutoff in each actual core block has precisely
the mass scale needed by the noncube moment estimates. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma rpow_eight_third : (8:ℝ)^(1/3:ℝ) = 2 := by
  rw [show (8:ℝ) = (2:ℝ)^3 by norm_num,← Real.rpow_natCast (2:ℝ) 3,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit absorption of the retained norm-dyad count and arbitrarily
small arithmetic losses in a fixed polynomial scale range. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_dyad_count_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log J) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := 1+Real.log 3/Real.log 2+1/Real.log 2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J hJ
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hfloor : (1:ℕ) ≤ ⌊3*J⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    norm_num
    linarith
  have hfloorpos : (0:ℝ) < (⌊3*J⌋₊:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hlog := Real.log_le_log hfloorpos (Nat.floor_le (by positivity : 0 ≤ 3*J))
  have hn := Real.natLog_le_logb ⌊3*J⌋₊ 2
  simp only [Real.logb,Nat.cast_ofNat] at hn
  have hjlog := Real.log_nonneg hJ
  have hh : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ) ≤
      (Real.log 3+Real.log J)/Real.log 2 := by
    apply hn.trans
    apply (div_le_div_iff_of_pos_right h2).mpr
    simpa only [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hJp.ne'] using hlog
  rw [Nat.cast_add,Nat.cast_one]
  have hhp : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ)+1 ≤
      (Real.log 3+Real.log J)/Real.log 2+1 := by linarith only [hh]
  apply hhp.trans
  dsimp [C]
  have hx := mul_nonneg (show 0 ≤ 1+Real.log 3/Real.log 2 by positivity) hjlog
  simp only [div_eq_mul_inv] at *
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoreIndexLogCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete two-dimensional core partition costs only two powers
of the logarithm, uniformly throughout the required frequency range. -/
noncomputable section
namespace CubicFirstMoment

theorem core_dyadic_index_log_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (V B L : ℝ), 1 ≤ B → 1 ≤ L → B ≤ L^2 →
      ((largeCoreDyadicIndices V B).card:ℝ) ≤ C*(1+Real.log L)^2 := by
  obtain ⟨C,hC,hcount⟩ := metaplectic_dyad_count_log_bound
  refine ⟨4*C^2,by positivity,?_⟩
  intro V B L hB hL hBL
  have hmono : Nat.log 2 ⌊B⌋₊+1 ≤ Nat.log 2 ⌊3*B⌋₊+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by linarith))) 1
  have hn : ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log B) :=
    (Nat.cast_le.mpr hmono).trans (hcount B hB)
  have hlog : Real.log B ≤ 2*Real.log L := by
    have h := Real.log_le_log (zero_lt_one.trans_le hB) hBL
    rw [← Real.rpow_natCast L 2,Real.log_rpow (zero_lt_one.trans_le hL)] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hn' : ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ) ≤ 2*C*(1+Real.log L) :=
    hn.trans (by nlinarith)
  calc
    _ ≤ ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ)^2 := by
      exact_mod_cast largeCoreDyadicIndices_card V B
    _ ≤ (2*C*(1+Real.log L))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hn' 2
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveMobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Möbius coefficient below the sieve truncation

The union convolution of the squarefree Möbius weights is the same
Möbius weight. This proves the exact low-divisor coefficient identity,
which is stronger than a divisor bound and is needed in the residue.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_finset_prod (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) :
    primaryPrimeFactors (∏ p ∈ U, p) = U := by
  have hprod := primary_finset_prod U (fun p : Eisenstein => p) (fun p hp => (hU p hp).1)
  ext p
  rw [primaryPrime_mem_factors_iff hprod]
  constructor
  · rintro ⟨hp,hd⟩
    obtain ⟨q,hq,hpq⟩ := (hp.2.dvd_finsetProd_iff (fun p : Eisenstein => p)).mp hd
    have he : p = q := primary_associated_eq hp.1 (hU q hq).1
      (hp.2.associated_of_dvd (hU q hq).2 hpq)
    exact he ▸ hq
  · intro hp
    exact ⟨hU p hp,Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp⟩

lemma primaryPrimeFactors_prod_injective {U : Finset Eisenstein}
    (hU : ∀ p ∈ U, primaryPrime p) :
    Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s, p) (↑U.powerset : Set (Finset Eisenstein)) := by
  intro s hs t ht he
  have hs' := Finset.mem_powerset.mp hs
  have ht' := Finset.mem_powerset.mp ht
  have hh := congrArg primaryPrimeFactors he
  simpa only [primaryPrimeFactors_finset_prod s (fun p hp => hU p (hs' hp)),
    primaryPrimeFactors_finset_prod t (fun p hp => hU p (ht' hp))] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorRowEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total energy of all rows in the genuine coprimality expansion.
Every coefficient occurs once per squarefree primary divisor, so the
loss is bounded by an arbitrarily small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem divisor_row_energy_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S U : Finset Eisenstein) (β : Eisenstein → ℂ) (N : ℝ),
      (∀ p ∈ U, primaryPrime p) →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖β a‖^2) ≤
        C*N^ε*∑ a ∈ S, ‖β a‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro S U β N hU hS
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hcount : ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card : ℝ) ≤ C*N^ε := by
    let P := U.powerset.image (fun d => ∏ p ∈ d, p)
    have hP : ∀ d ∈ P, primary d := by
      intro d hd
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
      exact primary_finset_prod s (fun p : Eisenstein => p)
        (fun p hp => (hU p (Finset.mem_powerset.mp hs hp)).1)
    have hc : (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card ≤
        (P.filter (fun d => d ∣ a)).card := by
      apply Finset.card_le_card_of_injOn (fun d : Finset Eisenstein => ∏ p ∈ d, p)
      · intro d hd
        obtain ⟨hd,hda⟩ := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d,hd,rfl⟩,hda⟩
      · intro d hd e he hde
        exact primaryPrimeFactors_prod_injective hU
          (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp he).1 hde
    have hc' : ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card : ℝ) ≤
        ((P.filter (fun d => d ∣ a)).card : ℝ) := by exact_mod_cast hc
    exact hc'.trans ((hdiv P hP a (primary_ne_zero (hS a ha).1)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg a) (hS a ha).2.2 hε.le) hC.le))
  calc
    _ = ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card : ℝ)*‖β a‖^2 := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramMellinTwist
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of the existing Poisson/Mellin kernel's Fourier
frequency to the norm heights used by the proved structured moments. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramMellinPhase_eq_mellinPhase (t x : ℝ) :
    gramMellinPhase t x = mellinPhase (2*Real.pi*t) x := by
  rw [gramMellinPhase,Real.fourierChar_apply]
  unfold mellinPhase
  congr 1
  push_cast
  ring

lemma mellinPhase_add_height (u v x : ℝ) :
    mellinPhase (u+v) x = mellinPhase u x*mellinPhase v x := by
  unfold mellinPhase
  rw [show (((u+v)*Real.log x:ℝ):ℂ)*Complex.I =
    ((u*Real.log x:ℝ):ℂ)*Complex.I+((v*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

lemma gramMellinPhase_ratio (t : ℝ) {x N : ℝ} (hx : 0 < x) (hN : 0 < N) :
    gramMellinPhase t (x/N) =
      mellinPhase (2*Real.pi*t) x*mellinPhase (-(2*Real.pi*t)) N := by
  rw [gramMellinPhase_eq_mellinPhase]
  unfold mellinPhase
  rw [Real.log_div hx.ne' hN.ne']
  rw [show (((2*Real.pi*t)*(Real.log x-Real.log N):ℝ):ℂ)*Complex.I =
    (((2*Real.pi*t)*Real.log x:ℝ):ℂ)*Complex.I+
      ((-(2*Real.pi*t)*Real.log N:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramStructuredRows
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rows in the Poisson kernel are exactly the full structured prime
sums, including the squarefree restriction and the reversal of Mellin height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gramMellinPhase_neg (t x : ℝ) :
    gramMellinPhase (-t) x = star (gramMellinPhase t x) := by
  rw [gramMellinPhase_eq_mellinPhase,gramMellinPhase_eq_mellinPhase,star_mellinPhase]
  congr 1
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightCubeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube frequencies in a height average use the ordinary polynomial
mean, rather than the low-height cube lattice asymptotic. -/
noncomputable section
open scoped BigOperators
open Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mem_nonzeroCubeNormBall {B : ℝ} {h : Eisenstein}
    (hh : h ≠ 0) (hB : norm h ≤ B) (hc : ∃ z : Eisenstein, z^3 = h) :
    h ∈ nonzeroCubeNormBall B := by
  obtain ⟨z,hz⟩ := hc
  have hz0 : z ≠ 0 := by intro he; apply hh; rw [←hz,he]; simp
  have hr := cube_part_norm_bound (h := h) (v := 1) (j := z) one_ne_zero
    (by simpa using hz.symm) hB
  exact Finset.mem_image.mpr ⟨z,mem_nonzeroNormBall.mpr ⟨hr,hz0⟩,hz⟩

lemma nonzeroCubeNormBall_card {B : ℝ} (hB : 0 ≤ B) :
    ((nonzeroCubeNormBall B).card:ℝ) ≤ 18*B^(1/3:ℝ) :=
  (Nat.cast_le.mpr Finset.card_image_le).trans
    (nonzeroNormBall_card_le (Real.rpow_nonneg hB (1/3:ℝ)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBHeightPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit absolute exponents for the arbitrary-coefficient height
bound. The small core is cut at 5832*N^(1/1000). -/
noncomputable section
namespace CubicFirstMoment

lemma smallB_log_square_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N →
    (1+Real.log N)^2 ≤ C*N^(1/40000:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := log_power_normalization_bound 2
    (by norm_num : (0:ℝ) < 1/40000)
  refine ⟨C,hC,?_⟩
  intro N hN
  have hp : 0 < N := zero_lt_one.trans_le hN
  have h := mul_le_mul_of_nonneg_left (hbound N hN) (Real.rpow_nonneg hp.le (1/40000:ℝ))
  rw [← mul_assoc,← Real.rpow_add hp] at h
  norm_num at h
  simpa only [mul_comm C] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBAllFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The absolute power saving includes cube frequencies. Their height
mean uses the same ordinary theorem, with the actual cube count. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma smallB_cube_height_scale {N T : ℝ} (hN : 1 ≤ N) (hT : N^(1/50:ℝ) ≤ T) :
    N^(1/10000:ℝ)*(1+N/T) ≤ 2*N^(1-1/20000:ℝ) := by
  have hp : 0 < N := zero_lt_one.trans_le hN
  have hf : N/T ≤ N^(49/50:ℝ) := by
    calc
      _ ≤ N/N^(1/50:ℝ) := div_le_div_of_nonneg_left hp.le (Real.rpow_pos_of_pos hp _) hT
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub hp]; norm_num
  have hsum : 1+N/T ≤ 2*N^(49/50:ℝ) := by
    linarith [Real.one_le_rpow hN (by norm_num : (0:ℝ) ≤ 49/50)]
  calc
    _ ≤ N^(1/10000:ℝ)*(2*N^(49/50:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hp.le _)
    _ = 2*N^((1/10000:ℝ)+49/50) := by rw [Real.rpow_add hp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) (by norm_num)

theorem arbitrary_cube_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 0 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ norm b ≤ (Z:ℝ)) →
      H ⊆ nonzeroCubeNormBall B →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨D,hD,hmean⟩ := arbitrary_primary_height_mean hMV hC
    (by norm_num : (0:ℝ) < 1/10000)
  refine ⟨72*C*D+1,by positivity,?_⟩
  intro S H β Z B T u ℓ hZ hB hT hS hH
  have hp : 0 < (Z:ℝ) := zero_lt_one.trans_le hZ
  have hTp : 0 < T := (Real.rpow_pos_of_pos hp _).trans_le hT
  have hNorm : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z := by
    intro b hb
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero (hS b hb).1)),?_⟩
    have h := (hS b hb).2
    rw [← normNat_cast b] at h
    exact_mod_cast h
  have hm := hmean S H β Z (fun b hb => (hS b hb).1) hNorm ℓ u T hTp
  have hcard : (H.card:ℝ) ≤ 18*B^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hH)).trans (nonzeroCubeNormBall_card hB)
  have hs := smallB_cube_height_scale hZ hT
  let E := ∑ b ∈ S, ‖β b‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ 2*C*D*(1+(Z:ℝ)/T)*(Z:ℝ)^(1/10000:ℝ)*H.card*E := hm
    _ ≤ 2*C*D*(1+(Z:ℝ)/T)*(Z:ℝ)^(1/10000:ℝ)*(18*B^(1/3:ℝ))*E := by gcongr
    _ = 36*C*D*B^(1/3:ℝ)*E*((Z:ℝ)^(1/10000:ℝ)*(1+(Z:ℝ)/T)) := by ring
    _ ≤ 36*C*D*B^(1/3:ℝ)*E*(2*(Z:ℝ)^(1-1/20000:ℝ)) := by gcongr
    _ ≤ _ := by
      have hn : 0 ≤ (Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*E := by positivity
      nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Fubini for a bounded height polynomial and an integrable
Mellin weight. No mean estimate or interchange is assumed. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma continuous_height_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) :
    Continuous (fun t => ∫ s : ℝ, f s*G (t+u+s)) := by
  apply continuous_of_dominated (bound := fun s => ‖f s‖*M)
  · intro t
    exact (hf.mul (hG.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro t
    filter_upwards with s
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (_root_.norm_nonneg _)
  · exact hfi.norm.mul_const M
  · filter_upwards with s
    exact continuous_const.mul (hG.comp ((continuous_id.add continuous_const).add continuous_const))

lemma integrable_height_convolution_kernel {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun p : ℝ × ℝ => f p.1*G (p.2+u+p.1))
      (volume.prod (volume.restrict (Icc a b))) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let K : ℝ × ℝ → ℝ := fun p => f p.1*G (p.2+u+p.1)
  have hc : Continuous K :=
    (hf.comp continuous_fst).mul (hG.comp ((continuous_snd.add continuous_const).add continuous_fst))
  have hm : AEStronglyMeasurable K (volume.prod μ) := hc.aestronglyMeasurable
  have hb (s : ℝ) : (∫ t, ‖K (s,t)‖ ∂μ) ≤ (b-a)*M*‖f s‖ := by
    have hki : IntervalIntegrable (fun t => ‖K (s,t)‖) volume a b :=
      ((hc.comp (continuous_const.prodMk continuous_id)).norm).intervalIntegrable a b
    have hi := intervalIntegral.integral_mono_on hab hki
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖f s‖*M) volume a b)
      (fun t _ => by
        dsimp [K]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg (f s)))
    rw [intervalIntegral.integral_const,smul_eq_mul] at hi
    simpa only [μ,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
      mul_comm,mul_left_comm,mul_assoc] using hi
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun s =>
    (hc.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc),?_⟩
  apply (hfi.norm.const_mul ((b-a)*M)).mono' hm.norm.integral_prod_right'
  exact Filter.Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => _root_.norm_nonneg _))]
    exact hb s)

lemma height_convolution_interval_swap {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ∫ s : ℝ, f s*G (t+u+s)) =
      ∫ s : ℝ, f s*(∫ t in a..b, G (t+u+s)) := by
  have hi := integrable_height_convolution_kernel hf hfi hG hbound u hab
  have hs := (integral_integral_swap (f := fun s t : ℝ => f s*G (t+u+s)) hi).symm
  simp only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab] at hs
  rw [hs]
  apply integral_congr_ae
  filter_upwards with s
  exact intervalIntegral.integral_const_mul _ _

lemma integrable_height_convolution_interval {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {a b : ℝ} (hab : a ≤ b) :
    Integrable (fun s : ℝ => f s*(∫ t in a..b, G (t+u+s))) := by
  have hi := (integrable_height_convolution_kernel hf hfi hG hbound u hab).integral_prod_left
  simp only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_const_mul] at hi
  exact hi

theorem dyadicHeightMean_convolution {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hG : Continuous G)
    {M : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M) (u : ℝ) {T : ℝ} (hT : 0 < T) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T =
      ∫ s : ℝ, f s*dyadicHeightMean (fun t => G (t+u+s)) T := by
  have hp : T ≤ 2*T := by linarith
  have hn : -2*T ≤ -T := by linarith
  have hip := integrable_height_convolution_interval hf hfi hG hbound u hp
  have hin := integrable_height_convolution_interval hf hfi hG hbound u hn
  rw [dyadicHeightMean,height_convolution_interval_swap hf hfi hG hbound u hp,
    height_convolution_interval_swap hf hfi hG hbound u hn,← integral_add hip hin,← integral_div]
  apply integral_congr_ae
  filter_upwards with s
  dsimp [dyadicHeightMean]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformHeightMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A translation-uniform height mean passes through the whole Mellin
line without truncation. All interchanges follow from absolute Fubini. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma dyadicHeightMean_convolution_uniform {f G : ℝ → ℝ}
    (hf : Continuous f) (hfi : Integrable f) (hf0 : ∀ s, 0 ≤ f s)
    (hG : Continuous G) {M B T : ℝ} (hbound : ∀ t, ‖G t‖ ≤ M)
    (hT : 0 < T) (hmean : ∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ B) (u : ℝ) :
    dyadicHeightMean (fun t => ∫ s : ℝ, f s*G (t+u+s)) T ≤ B*(∫ s : ℝ, f s) := by
  rw [dyadicHeightMean_convolution hf hfi hG hbound u hT]
  have hp := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : T ≤ 2*T)
  have hn := integrable_height_convolution_interval hf hfi hG hbound u
    (by linarith : -2*T ≤ -T)
  have hi : Integrable (fun s => f s*dyadicHeightMean (fun t => G (t+u+s)) T) := by
    convert (hp.add hn).div_const T using 1
    all_goals try with_reducible_and_instances rfl
    funext s
    dsimp [dyadicHeightMean]
    ring
  have hm := integral_mono hi (hfi.mul_const B) (fun s => by
    apply mul_le_mul_of_nonneg_left _ (hf0 s)
    simpa only [add_assoc] using hmean (u+s))
  exact hm.trans_eq (by rw [integral_mul_const]; ring)

/-- Both signs of the arithmetic Mellin coefficient have the same full
line bound. The sole cost is its already proved zeroth moment. -/
theorem arithmeticMellin_signed_height_uniform (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (G : ℝ → ℝ), Continuous G → ∀ (E B T u ε : ℝ),
      (ε = 1 ∨ ε = -1) → 0 ≤ B → 0 < T → (∀ t, ‖G t‖ ≤ E) →
      (∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖arithmeticMellinCoefficient M hM V hV hV' ρ (ε*s)‖*G (t+u+s)) T ≤ D*B := by
  obtain ⟨D,hD,hdecay⟩ := arithmeticMellinCoefficient_moment_decay M hM V hV hV' q 0
  refine ⟨D,hD,?_⟩
  intro ρ hρ G hG E B T u ε hε hB hT hbound hmean
  let A := arithmeticMellinCoefficient M hM V hV hV' ρ
  have hc : Continuous A := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hi : Integrable A := arithmeticMellinCoefficient_integrable M hM V hV hV' ρ
  have hfi : Integrable (fun s => ‖A (ε*s)‖) := by
    rcases hε with rfl | rfl
    · simpa only [one_mul] using hi.norm
    · simpa only [neg_one_mul] using hi.norm.comp_neg
  have heq : (∫ s : ℝ, ‖A (ε*s)‖) = ∫ s : ℝ, ‖A s‖ := by
    rcases hε with rfl | rfl
    · simp only [one_mul]
    · simpa only [neg_one_mul] using integral_neg_eq_self (fun s : ℝ => ‖A s‖) volume
  have hd : (1+ρ)^q*(∫ s : ℝ, ‖A (ε*s)‖) ≤ D := by
    rw [heq]
    simpa only [pow_zero,one_mul] using hdecay ρ hρ
  have hb := dyadicHeightMean_convolution_uniform
    (hc.comp (show Continuous (fun s : ℝ => ε*s) from continuous_const.mul continuous_id)).norm
    hfi (fun _ => _root_.norm_nonneg _) hG hbound hT hmean u
  calc
    _ ≤ (1+ρ)^q*(B*(∫ s : ℝ, ‖A (ε*s)‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = B*((1+ρ)^q*(∫ s : ℝ, ‖A (ε*s)‖)) := by ring
    _ ≤ B*D := mul_le_mul_of_nonneg_left hd hB
    _ = _ := mul_comm _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arbitrary-coefficient small-B mass over the entire Mellin
line. The height bound is uniform in translation, so no tail is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma finite_character_mass_bound (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ b ∈ S, primary b) (ℓ : ℤ) (t : ℝ) :
    ‖∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase t (norm b)‖^2‖ ≤
      (H.card:ℝ)*S.card*∑ b ∈ S, ‖β b‖^2 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  have hrow (h : Eisenstein) :
      ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase t (norm b)‖^2 ≤
      (S.card:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    apply (norm_sum_sq_le_card_mul S _).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro b hb
    apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
    simp only [norm_mul,norm_theta (primary_ne_zero (hS b hb)),mellinPhase_norm,mul_one]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS b hb) h)
  apply (Finset.sum_le_sum (fun h _ => hrow h)).trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteCharacterMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary finite cubic-character rows and their exact Mellin twists. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finiteCharacterMass_continuous (S H : Finset Eisenstein) (β : Eisenstein → ℂ) :
    Continuous (finiteCharacterMass S H β) := by
  unfold finiteCharacterMass
  apply continuous_finsetSum
  intro h hh
  convert (continuous_finite_character_height S β h 0 0).norm.pow 2 using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  simp only [Pi.pow_apply,theta_zero,mul_one,add_zero]

lemma finiteCharacterMass_bound (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (u : ℝ) :
    ‖finiteCharacterMass S H β u‖ ≤ (H.card:ℝ)*S.card*∑ a ∈ S, ‖β a‖^2 := by
  simpa only [finiteCharacterMass,theta_zero,mul_one] using
    finite_character_mass_bound S H β hS 0 u

lemma finite_character_gram_row_norm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (h : Eisenstein) (u s : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      star (gramMellinPhase s (norm a/N))*star (cubicSymbol a h)‖ =
    ‖∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u+2*Real.pi*s) (norm a)‖ := by
  have he : (∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      star (gramMellinPhase s (norm a/N))*star (cubicSymbol a h)) =
      star (mellinPhase (-(2*Real.pi*s)) N*
        ∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u+2*Real.pi*s) (norm a)) := by
    rw [star_mul,star_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [gramMellinPhase_ratio s (norm_pos_of_ne_zero (primary_ne_zero (hS a ha))) hN,
      mellinPhase_add_height]
    simp only [star_mul]
    ring
  rw [he,norm_star,norm_mul,mellinPhase_norm,one_mul]

lemma finite_character_gram_reverse_row_norm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (h : Eisenstein) (u s : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      gramMellinPhase s (norm a/N)*star (cubicSymbol a h)‖ =
    ‖∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u-2*Real.pi*s) (norm a)‖ := by
  have he := finite_character_gram_row_norm S β hS h u (-s) hN
  simpa only [gramMellinPhase_neg,star_star,mul_neg,← sub_eq_add_neg] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCharacterMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact divisor mass behind the genuine coprimality kernel, with
arbitrary squarefree coefficients and both Fourier signs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorCharacterMass_continuous (S H U : Finset Eisenstein) (β : Eisenstein → ℂ) :
    Continuous (divisorCharacterMass S H U β) := by
  unfold divisorCharacterMass
  exact continuous_finsetSum _ (fun _ _ => finiteCharacterMass_continuous _ _ _)

lemma divisorCharacterMass_bound (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (u : ℝ) :
    ‖divisorCharacterMass S H U β u‖ ≤
      ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d, p) ∣ a)).card*
        ∑ a ∈ S.filter (fun a => (∏ p ∈ d, p) ∣ a), ‖β a‖^2 := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  exact finiteCharacterMass_bound _ _ _ (fun a ha => hS a (Finset.mem_filter.mp ha).1) u

lemma twistedCoprimeMellinMass_eq_divisor_mass (S H U : Finset Eisenstein)
    (β : Eisenstein → ℂ) (hS : ∀ a ∈ S, primary a) (u s : ℝ)
    {N : ℝ} (hN : 0 < N) :
    twistedCoprimeMellinMass S H U β (fun a => norm a/N) u s =
      (divisorCharacterMass S H U β (u+2*Real.pi*s)+
        divisorCharacterMass S H U β (u-2*Real.pi*s))/2 := by
  unfold twistedCoprimeMellinMass coprimeMellinMass divisorCharacterMass finiteCharacterMass
  rw [← Finset.sum_add_distrib,← Finset.sum_div]
  apply congrArg (fun x : ℝ => x/2)
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply Finset.sum_congr rfl
    intro h hh
    rw [finite_character_gram_row_norm _ β (fun a ha => hS a (Finset.mem_filter.mp ha).1) h u s hN]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [finite_character_gram_reverse_row_norm _ β (fun a ha => hS a (Finset.mem_filter.mp ha).1) h u s hN]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSignedIntegration
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact changes of variable for the two signs of the Poisson rows.
The Jacobian 2π is retained. -/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
namespace CubicFirstMoment

lemma integral_scaled_mass (f g : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, f t*g (c*t)) = c⁻¹*(∫ t : ℝ, f (t/c)*g t) := by
  have he := Measure.integral_comp_mul_left (fun t : ℝ => f (t/c)*g t) c
  simp only [abs_inv,abs_of_pos hc,smul_eq_mul,mul_div_cancel_left₀ _ hc.ne'] at he
  exact he

lemma integral_scaled_signed_mass (f g : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (hplus : Integrable (fun t : ℝ => f t*g (c*t)))
    (hminus : Integrable (fun t : ℝ => f t*g (-(c*t)))) :
    (∫ t : ℝ, f t*((g (c*t)+g (-(c*t)))/2)) =
      ((∫ t : ℝ, f (t/c)*g t)+(∫ t : ℝ, f (-(t/c))*g t))/(2*c) := by
  have hminus' : (∫ t : ℝ, f t*g (-(c*t))) =
      c⁻¹*(∫ t : ℝ, f (-(t/c))*g t) := by
    have hn := integral_neg_eq_self (fun t : ℝ => f t*g (-(c*t)))
    simp only [mul_neg,neg_neg] at hn
    rw [← hn]
    exact integral_scaled_mass (fun t => f (-t)) g hc
  have hs (t : ℝ) : f t*((g (c*t)+g (-(c*t)))/2) =
      (f t*g (c*t))/2+(f t*g (-(c*t)))/2 := by ring
  simp_rw [hs]
  rw [integral_add (hplus.div_const 2) (hminus.div_const 2),
    integral_div,integral_div,integral_scaled_mass f g hc,hminus']
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailNumerical
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform elementary sieve gap for conductor up to N^(19/20).
The root variables isolate the algebra: p=P^(1/3), q=Q^(1/3),
r=N^(1/120). Only one cubic orientation and the ordinary sieve are needed. -/
noncomputable section
namespace CubicFirstMoment

lemma primeGroupTail_polynomial_min {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hD : p*q^2 ≤ r^38) :
    min (q^3*(p^3+r^120+p^2*r^80)) ((p^3*q^3)^2+r^120) ≤
      r^120+3*r^119*(p*q^2) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hD0 : 0 ≤ p*q^2 := mul_nonneg hp0 (sq_nonneg q)
  have hr76 : r^76 ≤ r^119 := pow_le_pow_right₀ hr (by decide)
  have hr118 : r^118 ≤ r^119 := pow_le_pow_right₀ hr (by decide)
  have hr116 : r^116 ≤ r^119 := pow_le_pow_right₀ hr (by decide)
  rcases le_total (r*q) p with hlarge | hsmall
  · have hq4 : q ≤ q^4 := by
      have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hq (n := 3)) hq0
      nlinarith
    have hpq : p^2*q ≤ r^119 := by
      calc
        _ ≤ p^2*q^4 := mul_le_mul_of_nonneg_left hq4 (sq_nonneg p)
        _ = (p*q^2)^2 := by ring
        _ ≤ (r^38)^2 := pow_le_pow_left₀ hD0 hD 2
        _ = r^76 := by ring
        _ ≤ _ := hr76
    have hfirst : q^3*p^3 ≤ r^119*(p*q^2) := by
      have h := mul_le_mul_of_nonneg_left hpq hD0
      nlinarith
    have hmiddle : q^3*r^120 ≤ r^119*(p*q^2) := by
      have h := mul_le_mul_of_nonneg_left hlarge (mul_nonneg (pow_nonneg hr0 119) (sq_nonneg q))
      nlinarith
    have hpq' : p*q ≤ r^38 := by
      have h := mul_le_mul_of_nonneg_left (show q ≤ q^2 by nlinarith) hp0
      exact h.trans hD
    have hlast : q^3*p^2*r^80 ≤ r^119*(p*q^2) := by
      calc
        _ = (p*q^2)*(p*q)*r^80 := by ring
        _ ≤ (p*q^2)*(r^38)*r^80 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpq' hD0) (pow_nonneg hr0 _)
        _ = (p*q^2)*r^118 := by ring
        _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr118 hD0
    apply (min_le_left _ _).trans
    nlinarith [pow_nonneg hr0 120]
  · have hp3 : p^3 ≤ r^2*(p*q^2) := by
      have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hsmall 2) hp0
      nlinarith
    have hD3 : (p*q^2)^3 ≤ r^114 := by
      convert pow_le_pow_left₀ hD0 hD 3 using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hmain : (p^3*q^3)^2 ≤ r^119*(p*q^2) := by
      calc
        _ = (p*q^2)^3*p^3 := by ring
        _ ≤ (p*q^2)^3*(r^2*(p*q^2)) :=
          mul_le_mul_of_nonneg_left hp3 (pow_nonneg hD0 _)
        _ = (p*q^2)*r^2*(p*q^2)^3 := by ring
        _ ≤ (p*q^2)*r^2*r^114 := mul_le_mul_of_nonneg_left hD3
          (mul_nonneg hD0 (sq_nonneg r))
        _ = (p*q^2)*r^116 := by ring
        _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr116 hD0
    apply (min_le_right _ _).trans
    nlinarith [mul_nonneg (pow_nonneg hr0 119) hD0]

/-- Below conductor N^(19/20), the two relevant sieve bounds have an
absolute gap, apart from the explicit ordinary-sieve diagonal N. -/
lemma primeGroupTail_sieve_min {P Q N : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hN : 1 ≤ N) (hD : P*Q^2 ≤ N^(19/20:ℝ)) :
    min (Q*(P+N+(P*N)^(2/3:ℝ))) ((P*Q)^2+N) ≤
      N+3*N^(119/120:ℝ)*(P*Q^2)^(1/3:ℝ) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let p := P^(1/3:ℝ)
  let q := Q^(1/3:ℝ)
  let r := N^(1/120:ℝ)
  have hp : 1 ≤ p := Real.one_le_rpow hP (by norm_num)
  have hq : 1 ≤ q := Real.one_le_rpow hQ (by norm_num)
  have hr : 1 ≤ r := Real.one_le_rpow hN (by norm_num)
  have hp3 : p^3 = P := by rw [← Real.rpow_mul_natCast hP0]; norm_num
  have hq3 : q^3 = Q := by rw [← Real.rpow_mul_natCast hQ0]; norm_num
  have hr120 : r^120 = N := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have hr38 : r^38 = N^(19/60:ℝ) := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have hr80 : r^80 = N^(2/3:ℝ) := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have hr119 : r^119 = N^(119/120:ℝ) := by rw [← Real.rpow_mul_natCast hN0]; norm_num
  have hp2 : p^2 = P^(2/3:ℝ) := by rw [← Real.rpow_mul_natCast hP0]; norm_num
  have hroot : (P*Q^2)^(1/3:ℝ) = p*q^2 := by
    rw [Real.mul_rpow hP0 (sq_nonneg Q),← Real.rpow_pow_comm hQ0]
  have hrootD : p*q^2 ≤ r^38 := by
    rw [← hroot,hr38]
    have h := Real.rpow_le_rpow (mul_nonneg hP0 (sq_nonneg Q)) hD (by norm_num : (0:ℝ) ≤ 1/3)
    rw [← Real.rpow_mul hN0] at h
    norm_num at h
    exact h
  have h := primeGroupTail_polynomial_min hp hq hr hrootD
  rw [hp3,hq3,hr120,hr80,hr119,hp2,← hroot,← Real.mul_rpow hP0 hN0] at h
  exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual finite frequency-block estimate for arbitrary squarefree
coefficients. There is no prime-convolution or height restriction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem primeGroupTail_frequency_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (B R S T J H : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V → U*V^2 ≤ N^(19/20:ℝ) →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      (T.card:ℝ) ≤ 18*V →
      H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
        (R.card:ℝ)*J.card*C*N^(2*ε)*
          (N+3*N^(119/120:ℝ)*(U*V^2)^(1/3:ℝ))*∑ b ∈ B, ‖β b‖^2 := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hbound⟩ := noncube_three_sieve_bounds hHuxley hε
  refine ⟨18*C₁+C₂,by positivity,?_⟩
  intro B R S T J H N U V hN hU hV hD hB hS hT hcard hH β
  let C := 18*C₁+C₂
  let F : ℝ := R.card*J.card
  let E := ∑ b ∈ B, ‖β b‖^2
  let K := F*C*N^(2*ε)*E
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hDN : U*V^2 ≤ N := hD.trans (by
    nth_rw 2 [← Real.rpow_one N]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
  have hUN : U ≤ N := (le_mul_of_one_le_right hU0 (one_le_pow₀ hV)).trans hDN
  have hVN : V ≤ N := (show V ≤ V^2 by nlinarith).trans
    ((le_mul_of_one_le_left (sq_nonneg V) hU).trans hDN)
  have hpow (x : ℝ) (hx : 0 ≤ x) (hxN : x ≤ N^2) : x^ε ≤ N^(2*ε) := by
    apply (Real.rpow_le_rpow hx hxN hε.le).trans_eq
    rw [← Real.rpow_natCast N 2,← Real.rpow_mul hN0]
    norm_num
  have hpowU : (U*N)^ε ≤ N^(2*ε) := hpow _ (mul_nonneg hU0 hN0) (by nlinarith)
  have hpowUV : (U*V)^ε ≤ N^(2*ε) := hpow _ (mul_nonneg hU0 hV0) (by nlinarith)
  have hcoeff : C₁*(T.card:ℝ)*(U*N)^ε ≤ C*V*N^(2*ε) := by
    calc
      _ ≤ C₁*(18*V)*N^(2*ε) := by gcongr
      _ = (18*C₁)*V*N^(2*ε) := by ring
      _ ≤ _ := by gcongr; dsimp [C]; linarith
  have hcoeff' : C₂*(U*V)^ε ≤ C*N^(2*ε) := by
    gcongr
    · dsimp [C]; linarith
  have hraw := hbound B R S T J H N U V hN hU hV hB hS hT hH β
  have hcubic : (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
      K*(V*(U+N+(U*N)^(2/3:ℝ))) := by
    calc
      _ ≤ _ := hraw
      _ ≤ (F*C₁*((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ))))*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity))
      _ = F*(C₁*(T.card:ℝ)*(U*N)^ε)*(U+N+(U*N)^(2/3:ℝ))*E := by ring
      _ ≤ F*(C*V*N^(2*ε))*(U+N+(U*N)^(2/3:ℝ))*E := by gcongr
      _ = _ := by dsimp [K]; ring
  have hord : (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
      K*((U*V)^2+N) := by
    calc
      _ ≤ _ := hraw
      _ ≤ ((R.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N))*E :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hE
      _ = F*(C₂*(U*V)^ε)*((U*V)^2+N)*E := by dsimp [F]; ring
      _ ≤ F*(C*N^(2*ε))*((U*V)^2+N)*E := by gcongr
      _ = _ := by dsimp [K]; ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ min (K*(V*(U+N+(U*N)^(2/3:ℝ)))) (K*((U*V)^2+N)) := le_min hcubic hord
    _ = K*min (V*(U+N+(U*N)^(2/3:ℝ))) ((U*V)^2+N) := (mul_min_of_nonneg _ _ hK).symm
    _ ≤ K*(N+3*N^(119/120:ℝ)*(U*V^2)^(1/3:ℝ)) :=
      mul_le_mul_of_nonneg_left (primeGroupTail_sieve_min hU hV hN hD) hK
    _ = _ := by dsimp [K,F,C,E]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailCore
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-B conductor bounds on the actual ramified/cube/squarefree blocks.
All coefficients remain arbitrary and the cube multiplicity is summed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem primeGroupTail_core_block_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N B : ℝ) (i j : ℕ), 1 ≤ N → 0 ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      8*coreDyadicConductor i j ≤ N^(19/20:ℝ) →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h‖^2) ≤
        C*N^(2*ε)*B^(1/3:ℝ)*
          (N/(coreDyadicConductor i j)^(1/3:ℝ)+N^(119/120:ℝ))*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨C,hC,hbound⟩ := primeGroupTail_frequency_sieve hHuxley hε
  let K : ℝ := (nonzeroNormBall 729).card
  have hK : 0 < K := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    exact ⟨1,mem_nonzeroNormBall.mpr ⟨by norm_num [norm_one_eq],one_ne_zero⟩⟩
  refine ⟨108*K*C,by positivity,?_⟩
  intro S H β N B i j hN hB hS hD hH
  have hU : 1 ≤ 2*(2:ℝ)^i := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := i)]
  have hV : 1 ≤ 2*(2:ℝ)^j := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
  have hST (n : ℕ) : ∀ s ∈ squarefreePrimaryDyad n,
      primary s ∧ Squarefree s ∧ norm s ≤ 2*(2:ℝ)^n := by
    intro s hs
    have hg := squarefreePrimaryDyad_gramDyad hs
    exact ⟨hg.1,hg.2.1,hg.2.2.2.le⟩
  have hcard : ((squarefreePrimaryDyad j).card:ℝ) ≤ 18*(2*(2:ℝ)^j) :=
    primary_support_card_le (squarefreePrimaryDyad j) (by positivity)
      (fun s hs => ⟨(hST j s hs).1,(hST j s hs).2.2⟩)
  have hD' : (2*(2:ℝ)^i)*(2*(2:ℝ)^j)^2 = 8*coreDyadicConductor i j := by
    unfold coreDyadicConductor
    ring
  have hh := hbound S (nonzeroNormBall 729) (squarefreePrimaryDyad i)
    (squarefreePrimaryDyad j) (coreDyadicCubeFactors B i j) H N
    (2*(2:ℝ)^i) (2*(2:ℝ)^j) hN hU hV (by rwa [hD']) hS (hST i) (hST j) hcard hH β
  rw [hD',Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (coreDyadicConductor_pos i j).le,
    rpow_eight_third] at hh
  let D := (coreDyadicConductor i j)^(1/3:ℝ)
  have hDp : 0 < D := Real.rpow_pos_of_pos (coreDyadicConductor_pos i j) _
  have hweight : ((coreDyadicCubeFactors B i j).card:ℝ)*D ≤ 18*B^(1/3:ℝ) :=
    coreDyadicCubeFactors_card_weight hB i j
  have hfirst : ((coreDyadicCubeFactors B i j).card:ℝ)*N ≤ 18*B^(1/3:ℝ)*(N/D) := by
    have hc : ((coreDyadicCubeFactors B i j).card:ℝ) ≤ 18*B^(1/3:ℝ)/D :=
      (le_div_iff₀ hDp).mpr hweight
    convert mul_le_mul_of_nonneg_right hc (zero_le_one.trans hN) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsecond := mul_le_mul_of_nonneg_right hweight (show 0 ≤ 6*N^(119/120:ℝ) by positivity)
  have htotal : ((coreDyadicCubeFactors B i j).card:ℝ)*(N+3*N^(119/120:ℝ)*(2*D)) ≤
      108*B^(1/3:ℝ)*(N/D+N^(119/120:ℝ)) := by
    have hx : 0 ≤ B^(1/3:ℝ)*(N/D) := by positivity
    nlinarith [hfirst,hsecond]
  apply hh.trans
  have hE : 0 ≤ ∑ b ∈ S, ‖β b‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htotal (show 0 ≤ K*C*N^(2*ε) by positivity)) hE
  convert hm using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [K,D] <;> ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailHeightBlocks
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the actual small-core height mean and the uniform remaining
core estimate. Sharp coefficient supports and arbitrary height shifts remain. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem primeGroupTail_noncube_height_blocks
    {C ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B V T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 0 ≤ B → 0 < V → 0 < T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*B^(1/3:ℝ)*(∑ b ∈ S, ‖β b‖^2)*
        ((Z:ℝ)^ε*V*(1+(Z:ℝ)/T)+
          ((largeCoreDyadicIndices V B).card:ℝ)*(Z:ℝ)^(2*ε)*
            ((Z:ℝ)/(V/5832)^(1/3:ℝ)+(Z:ℝ)^(119/120:ℝ))) := by
  obtain ⟨D,hD,hmean⟩ := arbitrary_primary_height_mean hMV hC hε
  obtain ⟨K,hK,hcore⟩ := primeGroupTail_core_block_sieve hHuxley hε
  let K₀ := 648*C*D+2*K
  refine ⟨K₀,by dsimp [K₀]; positivity,?_⟩
  intro S H β Z B V T u ℓ hZ hB hV hT hS hsize hH
  let N : ℝ := Z
  let E := ∑ b ∈ S, ‖β b‖^2
  let I := largeCoreDyadicIndices V B
  let HS := H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ)))
  let P := fun h t => ∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)
  let F := fun (J : Finset Eisenstein) t => ∑ h ∈ J, ‖P h t‖^2
  have hN : 0 ≤ N := Nat.cast_nonneg Z
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcont (J : Finset Eisenstein) : Continuous (F J) := by
    exact continuous_finsetSum J (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)
  have hNorm : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z := by
    intro b hb
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero (hS b hb).1))
    · have hbN := (hS b hb).2.2
      rw [← normNat_cast b] at hbN
      exact_mod_cast hbN
  have hsmall : dyadicHeightMean (F HS) T ≤
      (648*C*D)*B^(1/3:ℝ)*E*(N^ε*V*(1+N/T)) := by
    have hm := hmean S HS β Z (fun b hb => (hS b hb).1) hNorm ℓ u T hT
    have hcard : (HS.card:ℝ) ≤ 324*V*B^(1/3:ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card (fun h hh => (Finset.mem_filter.mp hh).2))).trans
        (lowNoncubeSupport_card hV.le (Real.rpow_nonneg hB _))
    have hm' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (show 0 ≤ 2*C*D*(1+N/T)*N^ε by positivity)) hE
    apply hm.trans
    convert hm' using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [N,E]
    ring
  have hrow (z : ℕ × ℕ) (hz : z ∈ I) :
      dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T ≤
        2*K*N^(2*ε)*B^(1/3:ℝ)*
          (N/(V/5832)^(1/3:ℝ)+N^(119/120:ℝ))*E := by
    have hd := (Finset.mem_filter.mp hz).2
    have hp : 0 < V/5832 := by positivity
    have hroot := Real.rpow_le_rpow hp.le hd.1.le (by norm_num : (0:ℝ) ≤ 1/3)
    have hratio : N/(coreDyadicConductor z.1 z.2)^(1/3:ℝ) ≤ N/(V/5832)^(1/3:ℝ) :=
      div_le_div_of_nonneg_left hN (Real.rpow_pos_of_pos hp _) hroot
    have havg : dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T ≤
        2*(K*N^(2*ε)*B^(1/3:ℝ)*(N/(V/5832)^(1/3:ℝ)+N^(119/120:ℝ))*E) := by
      apply dyadicHeightMean_le_const (hcont _) hT
      intro t _
      let γ := fun b => β b*theta ℓ b*mellinPhase (t+u) (norm b)
      have hγ : (∑ b ∈ S, ‖γ b‖^2) = E := by
        apply Finset.sum_congr rfl
        intro b hb
        simp only [γ,norm_mul,norm_theta (primary_ne_zero (hS b hb).1),mellinPhase_norm,mul_one]
      have heq (h : Eisenstein) : (∑ b ∈ S, γ b*cubicSymbol b h) = P h t := by
        apply Finset.sum_congr rfl
        intro b hb
        dsimp [γ,P]
        ring
      have hh := hcore S (coreDyadicBlock B z.1 z.2) γ N B z.1 z.2 hZ hB hS
        ((mul_le_mul_of_nonneg_left hd.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
        (Finset.Subset.refl _)
      simp_rw [heq] at hh
      rw [hγ] at hh
      change F (coreDyadicBlock B z.1 z.2) t ≤ _ at hh
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hratio (le_refl (N^(119/120:ℝ))))
          (show 0 ≤ K*N^(2*ε)*B^(1/3:ℝ) by positivity)) hE
      exact hh.trans hm
    exact havg.trans_eq (by ring)
  have hlarge : (∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T) ≤
      (2*K)*B^(1/3:ℝ)*E*((I.card:ℝ)*N^(2*ε)*(N/(V/5832)^(1/3:ℝ)+N^(119/120:ℝ))) := by
    apply (Finset.sum_le_sum (fun z hz => hrow z hz)).trans_eq
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  have hsplit : dyadicHeightMean (F H) T ≤ dyadicHeightMean (F HS) T+
      ∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T := by
    have hm := dyadicHeightMean_mono (hcont H)
      ((hcont HS).add (continuous_finsetSum I (fun z _ => hcont _))) hT
      (g := fun t => F HS t+∑ z ∈ I, F (coreDyadicBlock B z.1 z.2) t)
      (fun t _ => noncube_frequency_mass_split H hH (fun h => ‖P h t‖^2) (fun _ => sq_nonneg _))
    rw [dyadicHeightMean_add (hcont HS) (continuous_finsetSum I (fun z _ => hcont _)),
      dyadicHeightMean_sum I (fun z => F (coreDyadicBlock B z.1 z.2)) (fun z _ => hcont _)] at hm
    exact hm
  have hc₁ : 648*C*D ≤ K₀ := by dsimp [K₀]; linarith
  have hc₂ : 2*K ≤ K₀ := by dsimp [K₀]; nlinarith
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₁ (Real.rpow_nonneg hB (1/3:ℝ))) hE)
    (show 0 ≤ N^ε*V*(1+N/T) by positivity)
  have hl := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₂ (Real.rpow_nonneg hB (1/3:ℝ))) hE)
    (show 0 ≤ (I.card:ℝ)*N^(2*ε)*(N/(V/5832)^(1/3:ℝ)+N^(119/120:ℝ)) by positivity)
  have hbound := (add_le_add hs hl).trans_eq (by
    show K₀*B^(1/3:ℝ)*E*(N^ε*V*(1+N/T))+
      K₀*B^(1/3:ℝ)*E*((I.card:ℝ)*N^(2*ε)*(N/(V/5832)^(1/3:ℝ)+N^(119/120:ℝ))) =
      K₀*B^(1/3:ℝ)*E*(N^ε*V*(1+N/T)+
        (I.card:ℝ)*N^(2*ε)*(N/(V/5832)^(1/3:ℝ)+N^(119/120:ℝ)))
    ring)
  exact hsplit.trans ((add_le_add hsmall hlarge).trans hbound)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailHeightPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The enlarged conductor range retains the same final absolute height saving. -/
noncomputable section
namespace CubicFirstMoment

lemma primeGroupTail_height_bracket_power {N T n CI CL : ℝ}
    (hN : 1 ≤ N) (hT : N^(1/50:ℝ) ≤ T) (hCI : 0 ≤ CI) (hCL : 0 ≤ CL)
    (hn : n ≤ CI*(1+Real.log N)^2)
    (hlog : (1+Real.log N)^2 ≤ CL*N^(1/40000:ℝ)) :
    N^(1/10000:ℝ)*(5832*N^(1/1000:ℝ))*(1+N/T)+
      n*N^(2*(1/10000):ℝ)*
        (N/((5832*N^(1/1000:ℝ))/5832)^(1/3:ℝ)+N^(119/120:ℝ)) ≤
      (11664+2*CI*CL)*N^(1-1/20000:ℝ) := by
  have hp : 0 < N := zero_lt_one.trans_le hN
  have hTp : 0 < T := (Real.rpow_pos_of_pos hp _).trans_le hT
  have hfrac : N/T ≤ N^(49/50:ℝ) := by
    calc
      _ ≤ N/N^(1/50:ℝ) := div_le_div_of_nonneg_left hp.le (Real.rpow_pos_of_pos hp _) hT
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub hp]; norm_num
  have hone : 1+N/T ≤ 2*N^(49/50:ℝ) := by
    linarith [Real.one_le_rpow hN (by norm_num : (0:ℝ) ≤ 49/50)]
  have hsmall : N^(1/10000:ℝ)*(5832*N^(1/1000:ℝ))*(1+N/T) ≤
      11664*N^(1-1/20000:ℝ) := by
    calc
      _ ≤ N^(1/10000:ℝ)*(5832*N^(1/1000:ℝ))*(2*N^(49/50:ℝ)) :=
        mul_le_mul_of_nonneg_left hone (by positivity)
      _ = 11664*N^((1/10000:ℝ)+1/1000+49/50) := by
        repeat rw [Real.rpow_add hp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) (by norm_num)
  have hroot : ((5832*N^(1/1000:ℝ))/5832)^(1/3:ℝ) = N^(1/3000:ℝ) := by
    rw [show (5832*N^(1/1000:ℝ))/5832 = N^(1/1000:ℝ) by ring,
      ← Real.rpow_mul hp.le]
    norm_num
  have hdivide : N/N^(1/3000:ℝ) = N^(1-1/3000:ℝ) := by
    nth_rw 1 [← Real.rpow_one N]
    rw [← Real.rpow_sub hp]
  have hn' : n ≤ (CI*CL)*N^(1/40000:ℝ) :=
    hn.trans ((mul_le_mul_of_nonneg_left hlog hCI).trans_eq (by ring))
  have hbig : n*N^(2*(1/10000):ℝ)*
      (N/((5832*N^(1/1000:ℝ))/5832)^(1/3:ℝ)+N^(119/120:ℝ)) ≤
      2*CI*CL*N^(1-1/20000:ℝ) := by
    rw [hroot,hdivide]
    calc
      _ ≤ ((CI*CL)*N^(1/40000:ℝ))*N^(2*(1/10000):ℝ)*
          (N^(1-1/3000:ℝ)+N^(119/120:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn' (by positivity)) (by positivity)
      _ = (CI*CL)*(N^((1/40000:ℝ)+2*(1/10000)+(1-1/3000))+
          N^((1/40000:ℝ)+2*(1/10000)+119/120)) := by
        repeat rw [Real.rpow_add hp]
        ring
      _ ≤ (CI*CL)*(N^(1-1/20000:ℝ)+N^(1-1/20000:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCI hCL)
        exact add_le_add (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
          (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
      _ = _ := by ring
  exact (add_le_add hsmall hbig).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailHeightSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine absolute power saving for the noncube height mass of an
arbitrary squarefree coefficient sequence in the small-frequency range. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem primeGroupTail_noncube_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_noncube_height_blocks hMV hC hHuxley
    (by norm_num : (0:ℝ) < 1/10000)
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨CL,hCL,hlog⟩ := smallB_log_square_bound
  refine ⟨K*(11664+2*CI*CL),by positivity,?_⟩
  intro S H β Z B T u ℓ hZ hB hT hS hsize hH
  let V := 5832*(Z:ℝ)^(1/1000:ℝ)
  have hZp : 0 < (Z:ℝ) := zero_lt_one.trans_le hZ
  have hTp : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  have hB2 : B ≤ (Z:ℝ)^2 := by
    calc
      B ≤ 8*B := by linarith
      _ ≤ (Z:ℝ)^(19/20:ℝ) := hsize
      _ ≤ _ := by
        rw [← Real.rpow_natCast (Z:ℝ) 2]
        exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  have hb := hbound S H β Z B V T u ℓ hZ (zero_le_one.trans hB)
    (by dsimp [V]; positivity) hTp hS hsize hH
  have hs := primeGroupTail_height_bracket_power hZ hT hCI.le hCL
    (hcount V B Z hB hZ hB2) (hlog Z hZ)
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ K*B^(1/3:ℝ)*(∑ b ∈ S, ‖β b‖^2) by positivity)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailAllFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All nonzero frequencies through N^(19/20), including cubes, at arbitrary translated heights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Every nonzero frequency in the small-B cutoff has a power-saving
height average, with arbitrary coefficients and no restriction on u. -/
theorem primeGroupTail_all_frequency_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ) (ℓ : ℤ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K₁,hK₁,hnc⟩ := primeGroupTail_noncube_height_power hMV hC hHuxley
  obtain ⟨K₂,hK₂,hc⟩ := arbitrary_cube_height_power hMV hC
  refine ⟨K₁+K₂,by positivity,?_⟩
  intro S H β Z B T u ℓ hZ hB hT hS hsize hH
  let HC := H.filter (fun h => ∃ a : Eisenstein, a^3 = h)
  let HN := H.filter (fun h => ¬∃ a : Eisenstein, a^3 = h)
  let F := fun (J : Finset Eisenstein) t => ∑ h ∈ J,
    ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2
  have hCsub : HC ⊆ nonzeroCubeNormBall B := by
    intro h hh
    obtain ⟨hh,hcube⟩ := Finset.mem_filter.mp hh
    exact mem_nonzeroCubeNormBall (hH h hh).1 (hH h hh).2 hcube
  have hn := hnc S HN β Z B T u ℓ hZ hB hT hS hsize (fun h hh =>
    ⟨(hH h (Finset.mem_filter.mp hh).1).1,(hH h (Finset.mem_filter.mp hh).1).2,
      (Finset.mem_filter.mp hh).2⟩)
  have hcube := hc S HC β Z B T u ℓ hZ (zero_le_one.trans hB) hT
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.2⟩) hCsub
  have hcont (J : Finset Eisenstein) : Continuous (F J) :=
    continuous_finsetSum J (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)
  have heq : F H = fun t => F HC t+F HN t := by
    funext t
    exact (Finset.sum_filter_add_sum_filter_not H (fun h => ∃ a : Eisenstein, a^3 = h) _).symm
  change dyadicHeightMean (F H) T ≤ _
  rw [heq,dyadicHeightMean_add (hcont HC) (hcont HN)]
  exact (add_le_add hcube hn).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformNormHeight
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two actual Poisson signs, with the Fourier Jacobian retained,
for a translation-uniform arbitrary height mass. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

theorem normMellin_signed_height_uniform (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ (G : ℝ → ℝ), Continuous G → ∀ (E B T u : ℝ),
      0 ≤ B → 0 < T → (∀ t, ‖G t‖ ≤ E) →
      (∀ v, dyadicHeightMean (fun t => G (t+v)) T ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
          ((G (t+u+2*Real.pi*s)+G (t+u-(2*Real.pi*s)))/2)) T ≤ D*B := by
  obtain ⟨D,hD,hmean⟩ := arithmeticMellin_signed_height_uniform M hM V hV hV' q
  refine ⟨D/(2*Real.pi),by positivity,?_⟩
  intro ρ hρ G hG E B T u hB hT hbound havg
  let A := arithmeticMellinCoefficient M hM V hV hV' ρ
  let f := fun s => ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖
  let P := fun t => ∫ s : ℝ, ‖A s‖*G (t+u+s)
  let Q := fun t => ∫ s : ℝ, ‖A (-s)‖*G (t+u+s)
  have hi : Integrable f := (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
  have he (t : ℝ) : (∫ s : ℝ, f s*((G (t+u+2*Real.pi*s)+
      G (t+u-(2*Real.pi*s)))/2)) = (4*Real.pi)⁻¹*(P t+Q t) := by
    have hp : Integrable (fun s : ℝ => f s*G (t+u+2*Real.pi*s)) :=
      hi.mul_bdd (hG.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun s => hbound _))
    have hn : Integrable (fun s : ℝ => f s*G (t+u-(2*Real.pi*s))) :=
      hi.mul_bdd (hG.comp (continuous_const.sub (continuous_const.mul continuous_id))).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun s => hbound _))
    have hs := integral_scaled_signed_mass f (fun s => G (t+u+s))
      (by positivity : 0 < 2*Real.pi) hp (by simpa only [sub_eq_add_neg] using hn)
    calc
      _ = ((∫ s : ℝ, f (s/(2*Real.pi))*G (t+u+s))+
          (∫ s : ℝ, f (-(s/(2*Real.pi)))*G (t+u+s)))/(2*(2*Real.pi)) := by
        simpa only [sub_eq_add_neg] using hs
      _ = _ := by
        dsimp [P,Q,A,f,arithmeticMellinCoefficient]
        simp only [neg_div]
        ring
  have hac : Continuous A := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hai : Integrable A := arithmeticMellinCoefficient_integrable M hM V hV hV' ρ
  have hpc : Continuous P := continuous_height_convolution hac.norm hai.norm hG hbound u
  have hqc : Continuous Q := continuous_height_convolution (hac.comp continuous_neg).norm
    hai.norm.comp_neg hG hbound u
  have hp := hmean ρ hρ G hG E B T u 1 (Or.inl rfl) hB hT hbound havg
  have hq := hmean ρ hρ G hG E B T u (-1) (Or.inr rfl) hB hT hbound havg
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hq
  change (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
    f s*((G (t+u+2*Real.pi*s)+G (t+u-(2*Real.pi*s)))/2)) T ≤ _
  simp_rw [he]
  rw [dyadicHeightMean_const_mul,dyadicHeightMean_add hpc hqc]
  calc
    _ = ((1+ρ)^q*dyadicHeightMean P T+(1+ρ)^q*dyadicHeightMean Q T)/(4*Real.pi) := by ring
    _ ≤ (D*B+D*B)/(4*Real.pi) := div_le_div_of_nonneg_right (add_le_add hp hq) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeGroupTailCoprimeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-B power saving with every common divisor retained. The only
loss in the genuine coprimality expansion is the proved divisor energy. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeGroupTail_divisor_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B → (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hpower⟩ := primeGroupTail_all_frequency_height_power hMV hC hHuxley
  obtain ⟨D,hD,henergy⟩ := divisor_row_energy_small_power (by norm_num : (0:ℝ) < 1/40000)
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro S H U β Z B T u hZ hB hT hU hS hsize hH
  have hz : 0 < (Z:ℝ) := zero_lt_one.trans_le hZ
  let F := fun d : Finset Eisenstein => S.filter (fun a => (∏ p ∈ d, p) ∣ a)
  have hrow (d : Finset Eisenstein) :
      dyadicHeightMean (fun t => finiteCharacterMass (F d) H β (t+u)) T ≤
        K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ a ∈ F d, ‖β a‖^2 := by
    simpa only [finiteCharacterMass,theta_zero,mul_one] using
      hpower (F d) H β Z B T u 0 hZ hB hT
        (fun a ha => hS a (Finset.mem_filter.mp ha).1) hsize hH
  have hsum : dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*
        (∑ d ∈ U.powerset, ∑ a ∈ F d, ‖β a‖^2) := by
    unfold divisorCharacterMass
    rw [dyadicHeightMean_sum U.powerset
      (fun d t => finiteCharacterMass (F d) H β (t+u))
      (fun d _ => (finiteCharacterMass_continuous (F d) H β).comp
        (continuous_id.add continuous_const)),Finset.mul_sum]
    exact Finset.sum_le_sum (fun d _ => hrow d)
  have he := henergy S U β (Z:ℝ) hU hS
  calc
    _ ≤ K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*
        (D*(Z:ℝ)^(1/40000:ℝ)*∑ a ∈ S, ‖β a‖^2) :=
      hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ = (K*D)*((Z:ℝ)^(1-1/20000:ℝ)*(Z:ℝ)^(1/40000:ℝ))*
        B^(1/3:ℝ)*∑ a ∈ S, ‖β a‖^2 := by ring
    _ = _ := by rw [← Real.rpow_add hz]; norm_num

theorem primeGroupTail_coprime_mellin_height_power_oai
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u ρ N : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 ≤ ρ → 0 < N →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
          twistedCoprimeMellinMass S H U β (fun a => norm a/N) (t+u) s) T ≤
        K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hpower⟩ := primeGroupTail_divisor_height_power hMV hC hHuxley
  obtain ⟨D,hD,hmean⟩ := normMellin_signed_height_uniform M hM V hV hV' q
  refine ⟨D*K,mul_pos hD hK,?_⟩
  intro S H U β Z B T u ρ N hZ hB hT hρ hN hU hS hsize hH
  let G := divisorCharacterMass S H U β
  let A := K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ a ∈ S, ‖β a‖^2
  let E := ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d, p) ∣ a)).card*
    ∑ a ∈ S.filter (fun a => (∏ p ∈ d, p) ∣ a), ‖β a‖^2
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hT
  have hh := hmean ρ hρ G (divisorCharacterMass_continuous S H U β) E A T u
    (by dsimp [A]; positivity) hTp
    (fun t => divisorCharacterMass_bound S H U β (fun a ha => (hS a ha).1) t)
    (fun v => hpower S H U β Z B T v hZ hB hT hU hS hsize hH)
  have he (t s : ℝ) := twistedCoprimeMellinMass_eq_divisor_mass S H U β
    (fun a ha => (hS a ha).1) (t+u) s hN
  simp_rw [he]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [A]
  ring

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power_oai := @OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power_oai
