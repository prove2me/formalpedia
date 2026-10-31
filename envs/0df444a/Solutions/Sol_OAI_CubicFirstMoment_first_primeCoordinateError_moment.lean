-- Prove2me | solution 1 for OAI.CubicFirstMoment.first_primeCoordinateError_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:37:29.197978+00:00
-- url     : https://prove2.me/submissions/7ea0a9aa-06be-46c8-a461-c1afb29ff7aa

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_sieveExponent_four_thirds

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

namespace CubicFirstMoment

lemma finiteCubicBound_mono {S T H J : Finset Eisenstein} (hST : S ⊆ T) (hHJ : H ⊆ J) :
    finiteCubicBound S H ≤ finiteCubicBound T J := by
  apply (finiteCubicBound_le_iff S H (finiteCubicBound_nonneg T J)).mpr
  intro u
  let v (a : Eisenstein) := if a ∈ S then u a else 0
  have hi (h : Eisenstein) : (∑ a ∈ T, v a * cubicSymbol a h) =
      ∑ a ∈ S, u a * cubicSymbol a h := by
    calc
      _ = ∑ a ∈ S, v a * cubicSymbol a h :=
        (Finset.sum_subset hST (fun a _ ha => by simp [v, ha])).symm
      _ = _ := Finset.sum_congr rfl (fun a ha => by simp [v, ha])
  have hv : (∑ a ∈ T, ‖v a‖^2) = ∑ a ∈ S, ‖u a‖^2 := by
    calc
      _ = ∑ a ∈ S, ‖v a‖^2 :=
        (Finset.sum_subset hST (fun a _ ha => by simp [v, ha])).symm
      _ = _ := Finset.sum_congr rfl (fun a ha => by simp [v, ha])
  have hb := finiteCubicBound_controls_mass T J v
  simp_rw [hi, hv] at hb
  exact (Finset.sum_le_sum_of_subset_of_nonneg hHJ (fun _ _ _ => sq_nonneg _)).trans hb

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

namespace CubicFirstMoment

lemma finiteCubicBound_le_card_mul (S H : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) :
    finiteCubicBound S H ≤ (S.card : ℝ)*H.card := by
  apply (finiteCubicBound_le_iff S H (by positivity)).mpr
  intro u
  have hrow (h : Eisenstein) :
      ‖∑ a ∈ S, u a*cubicSymbol a h‖^2 ≤ (S.card : ℝ)*∑ a ∈ S, ‖u a‖^2 := by
    have ht : ‖∑ a ∈ S, u a*cubicSymbol a h‖ ≤ ∑ a ∈ S, ‖u a‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS a ha) h)
    have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun a => ‖u a‖)
    simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
    exact (pow_le_pow_left₀ (_root_.norm_nonneg _) ht 2).trans hc
  calc
    _ ≤ ∑ _h ∈ H, (S.card : ℝ)*∑ a ∈ S, ‖u a‖^2 := Finset.sum_le_sum (fun h _ => hrow h)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

lemma dyadic_decay_step {c : ℝ} (hc : 0 < c) (j : ℕ) :
    (2 : ℝ)^j / (1+c*2^j)^2 ≤
      (2/c)*(1/(1+c*2^j)-1/(1+c*2^(j+1))) := by
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have h1 : 0 < 1+c*2^j := by positivity
  have h2 : 0 < 1+2*c*2^j := by positivity
  calc
    _ ≤ 2*2^j / ((1+c*2^j)*(1+2*c*2^j)) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
      nlinarith [sq_nonneg (c*2^j),sq_nonneg ((2 : ℝ)^j), mul_pos hc hJ]
    _ = _ := by
      rw [pow_succ]
      have h2' : 1+c*((2 : ℝ)^j*2) ≠ 0 := by positivity
      field_simp
      ring

lemma dyadic_decay_partial_sum {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℝ)^j/(1+c*2^j)^2) ≤ 2/c := by
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => dyadic_decay_step hc j)
  rw [← Finset.mul_sum] at h
  have ht : (∑ j ∈ Finset.range n, (1/(1+c*2^j)-1/(1+c*2^(j+1)))) =
      1/(1+c) - 1/(1+c*2^n) := by
    have hh := Finset.sum_range_sub (fun j => (1 : ℝ)/(1+c*2^j)) n
    rw [Finset.sum_sub_distrib] at hh ⊢
    simp only [pow_zero,mul_one] at hh
    linarith
  rw [ht] at h
  have hc0 : 0 ≤ 2/c := by positivity
  have hfirst : 1/(1+c) ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by linarith)
  have hlast : (0 : ℝ) ≤ 1/(1+c*2^n) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith : 1/(1+c)-1/(1+c*2^n) ≤ 1) hc0).trans_eq (mul_one _))

lemma dyadic_decay_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => (2 : ℝ)^j/(1+c*2^j)^2) :=
  summable_of_sum_range_le (fun _ => by positivity) (dyadic_decay_partial_sum hc)

end CubicFirstMoment

namespace CubicFirstMoment

lemma frequencyDyad_card_le (j : ℕ) :
    ((frequencyDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  have hs : frequencyDyad j ⊆ nonzeroNormBall ((2 : ℝ)^(j+1)) := Finset.filter_subset _ _
  have hh : ((frequencyDyad j).card : ℝ) ≤ (nonzeroNormBall ((2 : ℝ)^(j+1))).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hh.trans ((nonzeroNormBall_card_le (by positivity)).trans_eq (by rw [pow_succ]; ring))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

theorem finiteCubicBound_residualCube (P R S T C : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) :
    finiteCubicBound P (residualCubeSupport R S T C) ≤
      (R.card : ℝ) * min ((T.card : ℝ)*C.card*finiteCubicBound P S)
          ((S.card : ℝ)*C.card*finiteCubicBound P T) := by
  apply (finiteCubicBound_le_iff _ _ (mul_nonneg (by positivity)
    (le_min (by positivity [finiteCubicBound_nonneg P S])
      (by positivity [finiteCubicBound_nonneg P T])))).mpr
  exact residualCubeSupport_mass_le P R S T C hP

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma geometric_decay_step {q d : ℝ} (hq : 1 < q) (hd : 0 < d) (j : ℕ) :
    q^j/(1+d*q^j)^2 ≤
      (q/(d*(q-1)))*(1/(1+d*q^j)-1/(1+d*q^(j+1))) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have ht : 0 < q^j := by positivity
  have h1 : 0 < 1+d*q^j := by positivity
  have h2 : 0 < 1+d*q^j*q := by positivity
  have hdq : 0 < d*(q-1) := by positivity
  have he : (q/(d*(q-1)))*(1/(1+d*q^j)-1/(1+d*q^(j+1))) =
      q*q^j/((1+d*q^j)*(1+d*q^j*q)) := by
    rw [pow_succ]
    have hqm : q-1 ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
  have ht' : 0 ≤ q^j*(1+d*q^j) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) ht']

lemma geometric_decay_partial_sum {q d : ℝ} (hq : 1 < q) (hd : 0 < d) (n : ℕ) :
    (∑ j ∈ Finset.range n, q^j/(1+d*q^j)^2) ≤ q/(d*(q-1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have h := Finset.sum_le_sum (s := Finset.range n) (fun j _ => geometric_decay_step hq hd j)
  rw [← Finset.mul_sum] at h
  have ht : (∑ j ∈ Finset.range n, (1/(1+d*q^j)-1/(1+d*q^(j+1)))) =
      1/(1+d) - 1/(1+d*q^n) := by
    have hh := Finset.sum_range_sub (fun j => (1 : ℝ)/(1+d*q^j)) n
    rw [Finset.sum_sub_distrib] at hh ⊢
    simp only [pow_zero,mul_one] at hh
    linarith
  rw [ht] at h
  have hdq : 0 ≤ q/(d*(q-1)) := by positivity
  have hfirst : 1/(1+d) ≤ (1 : ℝ) := (div_le_one (by positivity)).mpr (by linarith)
  have hlast : (0 : ℝ) ≤ 1/(1+d*q^n) := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left (by linarith : 1/(1+d)-1/(1+d*q^n) ≤ 1) hdq).trans_eq (mul_one _))

lemma geometric_decay_tsum {q d : ℝ} (hq : 1 < q) (hd : 0 < d) :
    Summable (fun j : ℕ => q^j/(1+d*q^j)^2) ∧
      (∑' j : ℕ, q^j/(1+d*q^j)^2) ≤ q/(d*(q-1)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hs := summable_of_sum_range_le (fun j => by positivity : ∀ j : ℕ, 0 ≤ q^j/(1+d*q^j)^2)
    (geometric_decay_partial_sum hq hd)
  exact ⟨hs,hs.tsum_le_of_sum_range_le (geometric_decay_partial_sum hq hd)⟩

lemma rpow_cutoff_comparison {α x : ℝ} (hα : 0 < α) (hα4 : α ≤ 4) (hx : 0 ≤ x) :
    (1+x^α)^2 ≤ 4*(1+x)^8 := by
  by_cases hx1 : x ≤ 1
  · have hp := Real.rpow_le_rpow hx hx1 hα.le
    rw [Real.one_rpow] at hp
    have hn := Real.rpow_nonneg hx α
    have hb : 1 ≤ (1+x)^8 := one_le_pow₀ (by linarith)
    nlinarith
  · have hx1 : 1 ≤ x := le_of_not_ge hx1
    have hp : x^α ≤ x^4 := by simpa using Real.rpow_le_rpow_of_exponent_le hx1 hα4
    have hn := Real.rpow_nonneg hx α
    have he : (1+x^α)^2 ≤ (1+x^4)^2 := by gcongr
    have hpow : 1+x^4 ≤ (1+x)^4 := by simpa using pow_add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hx (by norm_num : (4 : ℕ) ≠ 0)
    have he' : (1+x^4)^2 ≤ (1+x)^8 := by
      have := pow_le_pow_left₀ (by positivity) hpow 2
      simpa only [← pow_mul] using this
    have hb : 0 ≤ (1+x)^8 := by positivity
    linarith

lemma real_dyadic_decay (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 4) {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α/(1+c*2^j)^8) ∧
      (∑' j : ℕ, ((2 : ℝ)^j)^α/(1+c*2^j)^8) ≤
        (4*2^α/(2^α-1))*c^(-α) := by
  have hq : (1 : ℝ) < 2^α := Real.one_lt_rpow (by norm_num) hα
  have hd : 0 < c^α := Real.rpow_pos_of_pos hc α
  have he (j : ℕ) : ((2 : ℝ)^j)^α = (2^α)^j := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  have hmajor (j : ℕ) : ((2 : ℝ)^j)^α/(1+c*2^j)^8 ≤
      4*((2^α)^j/(1+c^α*(2^α)^j)^2) := by
    have hnum : 0 ≤ ((2 : ℝ)^j)^α := by positivity
    have hi : (1+(c*2^j)^α)^2 ≤ 4*(1+c*2^j)^8 := rpow_cutoff_comparison hα hα4 (by positivity)
    rw [Real.mul_rpow hc.le (by positivity),he] at hi
    rw [he]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < (1+c*2^j)^8)
      (by positivity : 0 < (1+c^α*(2^α)^j)^2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ (2^α)^j by positivity)]
  have hs := (geometric_decay_tsum hq hd).1.mul_left 4
  have hs' := hs.of_nonneg_of_le (fun _ => by positivity) hmajor
  refine ⟨hs',?_⟩
  calc
    _ ≤ ∑' j : ℕ, 4*((2^α)^j/(1+c^α*(2^α)^j)^2) := hs'.tsum_le_tsum hmajor hs
    _ = 4*∑' j : ℕ, (2^α)^j/(1+c^α*(2^α)^j)^2 := tsum_mul_left
    _ ≤ 4*(2^α/(c^α*(2^α-1))) := mul_le_mul_of_nonneg_left (geometric_decay_tsum hq hd).2 (by norm_num)
    _ = _ := by rw [Real.rpow_neg hc.le]; field_simp

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_squarefreePrimaryDyad {n : Eisenstein} {j : ℕ} :
    n ∈ squarefreePrimaryDyad j ↔ n ∈ frequencyDyad j ∧ primary n ∧ Squarefree n := by
  simp [squarefreePrimaryDyad]

lemma mem_cubeDyadTriples {j i t c : ℕ} :
    (i,t,c) ∈ cubeDyadTriples j ↔ i+2*t+3*c ≤ j+1 := by
  simp [cubeDyadTriples,Finset.mem_product,Finset.mem_range]
  omega

lemma cubeDyadTriples_card (j : ℕ) : (cubeDyadTriples j).card ≤ (j+2)^3 := by
  have h := Finset.card_filter_le (s := (Finset.range (j+2)).product
    ((Finset.range (j+2)).product (Finset.range (j+2))))
    (p := fun z : ℕ×ℕ×ℕ => z.1+2*z.2.1+3*z.2.2 ≤ j+1)
  simpa [cubeDyadTriples,Finset.card_product,Finset.card_range,pow_succ,mul_assoc] using h

lemma frequencyDyad_subset_cubeCover (j : ℕ) : frequencyDyad j ⊆ cubeFrequencyCover j := by
  intro n hn
  obtain ⟨r,s,t,c,hr0,hr,hs,ht,hss,hst,hcop,hc0,he⟩ :=
    full_cube_decomposition (mem_frequencyDyad.mp hn).1
  let i := Nat.log 2 (normNat s)
  let l := Nat.log 2 (normNat t)
  let k := Nat.log 2 (normNat c)
  have hsi : s ∈ frequencyDyad i := mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩
  have htl : t ∈ frequencyDyad l := mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩
  have hck : c ∈ frequencyDyad k := mem_frequencyDyad.mpr ⟨hc0,rfl⟩
  have hprod : (2 : ℝ)^i*((2 : ℝ)^l)^2*((2 : ℝ)^k)^3 ≤ norm n := by
    calc
      _ ≤ norm s*(norm t)^2*(norm c)^3 := by
        have hsn := norm_nonneg s
        have htn := norm_nonneg t
        have hcn := norm_nonneg c
        gcongr <;> exact (frequencyDyad_norm ‹_›).1
      _ ≤ norm r*norm s*(norm t)^2*(norm c)^3 := by
        have hsn := norm_nonneg s
        have hcn := norm_nonneg c
        have hprim : 0 ≤ norm s*(norm t)^2*(norm c)^3 := by positivity [norm_nonneg s]
        have hmul := le_mul_of_one_le_left hprim (one_le_norm hr0)
        nlinarith
      _ = norm n := by rw [he]; simp only [norm_mul_eq,eisenstein_norm_pow]
  have hexp : i+2*l+3*k ≤ j+1 := by
    apply (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
    have heq : (2 : ℝ)^(i+2*l+3*k) = 2^i*(2^l)^2*(2^k)^3 := by
      simp only [pow_add,pow_mul,mul_comm 2 l,mul_comm 3 k]
    rw [heq]
    exact hprod.trans ((frequencyDyad_norm hn).2.trans_eq (by rw [pow_succ]; ring))
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,l,k),mem_cubeDyadTriples.mpr hexp,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r,mem_nonzeroNormBall.mpr ⟨hr,hr0⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨s*t^2*c^3,Finset.mem_image.mpr ⟨(s,t,c),?_ ,rfl⟩,?_⟩
  · exact Finset.mem_product.mpr ⟨mem_squarefreePrimaryDyad.mpr ⟨hsi,hs,hss⟩,
      Finset.mem_product.mpr ⟨mem_squarefreePrimaryDyad.mpr ⟨htl,ht,hst⟩,hck⟩⟩
  · rw [he]; ring

lemma finiteCubicBound_biUnion {ι : Type*} (I : Finset ι) (P : Finset Eisenstein)
    (H : ι → Finset Eisenstein) :
    finiteCubicBound P (I.biUnion H) ≤ ∑ i ∈ I, finiteCubicBound P (H i) := by
  apply (finiteCubicBound_le_iff _ _ (Finset.sum_nonneg (fun _ _ => finiteCubicBound_nonneg _ _))).mpr
  intro u
  have hmass : (∑ n ∈ I.biUnion H, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2) ≤
      ∑ i ∈ I, ∑ n ∈ H i, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      rw [Finset.biUnion_insert,Finset.sum_insert hi]
      have he := Finset.sum_union_inter (s₁ := H i) (s₂ := I.biUnion H)
        (f := fun n => ‖∑ b ∈ P, u b*cubicSymbol b n‖^2)
      have hn : 0 ≤ ∑ n ∈ H i ∩ I.biUnion H, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      linarith
  calc
    _ ≤ ∑ i ∈ I, ∑ n ∈ H i, ‖∑ b ∈ P, u b*cubicSymbol b n‖^2 := hmass
    _ ≤ ∑ i ∈ I, finiteCubicBound P (H i)*∑ b ∈ P, ‖u b‖^2 :=
      Finset.sum_le_sum (fun i _ => finiteCubicBound_controls_mass _ _ _)
    _ = _ := by rw [Finset.sum_mul]

theorem finiteCubicBound_frequency_cube (P : Finset Eisenstein)
    (hP : ∀ b ∈ P, primary b) (j : ℕ) :
    finiteCubicBound P (frequencyDyad j) ≤
      (nonzeroNormBall 729).card * ∑ z ∈ cubeDyadTriples j,
        min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
               finiteCubicBound P (squarefreePrimaryDyad z.1))
            (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
               finiteCubicBound P (squarefreePrimaryDyad z.2.1)) := by
  apply (finiteCubicBound_mono (Finset.Subset.refl P) (frequencyDyad_subset_cubeCover j)).trans
  apply (finiteCubicBound_biUnion (cubeDyadTriples j) P _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun z hz => finiteCubicBound_residualCube _ _ _ _ _ hP)

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x^(1/3 : ℝ))^3 = x := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

lemma rpow_two_thirds_cube {x : ℝ} (hx : 0 ≤ x) : (x^(2/3 : ℝ))^3 = x^2 := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx]
  norm_num

lemma cube_block_numerical {S T K N J ξ : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hK : 1 ≤ K) (hN : 0 ≤ N)
    (hJ : S*T^2*K^3 ≤ J) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    min (K*T*(N+(N*S)^(2/3 : ℝ)+S^ξ))
        (K*S*(N+(N*T)^(2/3 : ℝ)+T^ξ)) ≤
      N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J := by
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ0 : 0 ≤ J := (by positivity : 0 ≤ S*T^2*K^3).trans hJ
  have hJξ : 0 ≤ J^ξ := Real.rpow_nonneg hJ0 _
  have hcrossLeft : K*T*(N*S)^(2/3 : ℝ) ≤ (J*N)^(2/3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*T*(N*S)^(2/3 : ℝ))
      (by positivity : 0 ≤ (J*N)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [mul_pow,mul_pow,rpow_two_thirds_cube (by positivity),rpow_two_thirds_cube (by positivity)]
    calc
      _ = S^2*T^3*K^3*N^2 := by ring
      _ ≤ S^2*T^4*K^6*N^2 := by
        have ht : T^3 ≤ T^4 := pow_le_pow_right₀ hT (by norm_num)
        have hk : K^3 ≤ K^6 := pow_le_pow_right₀ hK (by norm_num)
        gcongr
      _ = (S*T^2*K^3*N)^2 := by ring
      _ ≤ _ := by gcongr
  by_cases hST : T ≤ S
  · have hsmall : K*T ≤ J^(1/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*T)
        (by positivity : 0 ≤ J^(1/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [rpow_third_cube hJ0]
      calc
        _ = T*T^2*K^3 := by ring
        _ ≤ S*T^2*K^3 := by gcongr
        _ ≤ J := hJ
    have hp : K*T*S^ξ ≤ J^ξ := by
      have hTK : K*T ≤ T^2*K^3 := by
        calc
          _ = T*K := mul_comm _ _
          _ ≤ T^2*K^3 := by
            gcongr
            · nlinarith [sq_nonneg (T-1)]
            · exact (le_self_pow₀ hK (by norm_num : (3 : ℕ) ≠ 0))
      have hTK1 : 1 ≤ T^2*K^3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) (one_le_pow₀ hK)
      have htξ := Real.self_le_rpow_of_one_le hTK1 hξ
      calc
        _ ≤ (T^2*K^3)^ξ*S^ξ := mul_le_mul_of_nonneg_right (hTK.trans htξ) (by positivity)
        _ = (S*T^2*K^3)^ξ := by rw [← Real.mul_rpow (by positivity) hS0]; congr 1; ring
        _ ≤ J^ξ := Real.rpow_le_rpow (by positivity) hJ (by linarith)
    apply (min_le_left _ _).trans
    have hn := mul_le_mul_of_nonneg_right hsmall hN
    nlinarith
  · have hST : S ≤ T := (le_of_not_ge hST)
    have hsmall : K*S ≤ J^(1/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*S)
        (by positivity : 0 ≤ J^(1/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [rpow_third_cube hJ0]
      calc
        _ = S*S^2*K^3 := by ring
        _ ≤ S*T^2*K^3 := by gcongr
        _ ≤ J := hJ
    have hc : K*S*(N*T)^(2/3 : ℝ) ≤ (J*N)^(2/3 : ℝ) := by
      apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ K*S*(N*T)^(2/3 : ℝ))
        (by positivity : 0 ≤ (J*N)^(2/3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [mul_pow,mul_pow,rpow_two_thirds_cube (by positivity),rpow_two_thirds_cube (by positivity)]
      have hST2 : S ≤ T^2 := hST.trans (by nlinarith [sq_nonneg (T-1)])
      calc
        _ = S^2*S*T^2*K^3*N^2 := by ring
        _ ≤ S^2*T^2*T^2*K^6*N^2 := by
          have hk : K^3 ≤ K^6 := pow_le_pow_right₀ hK (by norm_num)
          gcongr
        _ = (S*T^2*K^3*N)^2 := by ring
        _ ≤ _ := by gcongr
    have hp : K*S*T^ξ ≤ J := by
      have htξ : T^ξ ≤ T^2 := by simpa using Real.rpow_le_rpow_of_exponent_le hT hξ2
      calc
        _ ≤ K^3*S*T^2 := by
          gcongr
          exact le_self_pow₀ hK (by norm_num : (3 : ℕ) ≠ 0)
        _ = S*T^2*K^3 := by ring
        _ ≤ J := hJ
    apply (min_le_right _ _).trans
    have hn := mul_le_mul_of_nonneg_right hsmall hN
    nlinarith

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_GlobalRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summed dual norms and full smoothed sieve recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma summable_dualDyadicNorm (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) {c : ℝ} (hc : 0 < c) {A : ℕ} (hA : 2 ≤ A) :
    Summable (fun j : ℕ => finiteCubicBound S (frequencyDyad j) / (1+c*2^j)^A) := by
  have hs := (dyadic_decay_summable hc).mul_left (36*(S.card : ℝ))
  apply hs.of_nonneg_of_le
  · intro j
    exact div_nonneg (finiteCubicBound_nonneg _ _) (by positivity)
  · intro j
    have hd : 0 < (1+c*(2 : ℝ)^j)^2 := by positivity
    have hp : (1+c*(2 : ℝ)^j)^2 ≤ (1+c*2^j)^A :=
      pow_le_pow_right₀ (by linarith [show 0 ≤ c*(2 : ℝ)^j by positivity]) hA
    calc
      _ ≤ finiteCubicBound S (frequencyDyad j)/(1+c*2^j)^2 :=
        div_le_div_of_nonneg_left (finiteCubicBound_nonneg _ _) hd hp
      _ ≤ (36*S.card*2^j)/(1+c*2^j)^2 := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact (finiteCubicBound_le_card_mul S _ hS).trans
          ((mul_le_mul_of_nonneg_left (frequencyDyad_card_le j) (by positivity)).trans_eq (by ring))
      _ = _ := by ring

lemma dualDyadicNorm_nonneg (S : Finset Eisenstein) {c : ℝ} (hc : 0 ≤ c) (A : ℕ) :
    0 ≤ dualDyadicNorm S c A :=
  tsum_nonneg (fun j => div_nonneg (finiteCubicBound_nonneg _ _) (by positivity))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_SieveExponent
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative cube and dual bounds under a sieve exponent. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma dyadic_polynomial_small_power (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ((j : ℝ)+2)^d ≤ C*((2 : ℝ)^j)^ε := by
  let r : ℝ := (2^ε)⁻¹
  have hp : (1 : ℝ) < 2^ε := Real.one_lt_rpow (by norm_num) hε
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ hp
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d (r := r) (by simpa only [Real.norm_eq_abs,abs_of_pos hr] using hr1)
  let D : ℝ := (∑' n : ℕ, (n : ℝ)^d*r^n)+1
  have hD : 0 < D := by
    have hh : 0 ≤ ∑' n : ℕ, (n : ℝ)^d*r^n := tsum_nonneg (fun n => by positivity)
    dsimp [D]; linarith
  refine ⟨D*(2^ε)^2,by positivity,?_⟩
  intro j
  have hh := hs.le_tsum (j+2) (fun n _ => by positivity)
  have hh' : (((j : ℝ)+2)^d*r^j)*r^2 ≤ D := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,pow_add,mul_assoc] using hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  have he : (2^ε)^j = ((2 : ℝ)^j)^ε := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num)]
  have he' : r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε) = 1 := by
    rw [← he]
    dsimp [r]
    rw [inv_pow,inv_pow]
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ (2^ε)^2*((2 : ℝ)^j)^ε)
  have he'' : ((j : ℝ)+2)^d*r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε) = ((j : ℝ)+2)^d := by
    calc
      _ = ((j : ℝ)+2)^d*(r^j*r^2*((2^ε)^2*((2 : ℝ)^j)^ε)) := by ring
      _ = _ := by rw [he',mul_one]
  rw [he''] at hmul
  exact hmul.trans_eq (by ring)

lemma squarefreePrimaryDyad_card_le (j : ℕ) :
    ((squarefreePrimaryDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (frequencyDyad_card_le j)

lemma cubeDyad_sizes {j : ℕ} {z : ℕ×ℕ×ℕ} (hz : z ∈ cubeDyadTriples j) :
    (2 : ℝ)^z.1*((2 : ℝ)^z.2.1)^2*((2 : ℝ)^z.2.2)^3 ≤ 2*(2 : ℝ)^j := by
  have hh := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mem_cubeDyadTriples.mp hz))
  calc
    _ = (2 : ℝ)^(z.1+2*z.2.1+3*z.2.2) := by
      simp only [pow_add,pow_mul,mul_comm 2 z.2.1,mul_comm 3 z.2.2]
    _ ≤ 2^(j+1) := hh
    _ = _ := by rw [pow_succ]; ring

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_block_scaled {S T K N J ξ C : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hK : 1 ≤ K) (hN : 0 ≤ N)
    (hJ : S*T^2*K^3 ≤ J) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) (hC : 0 ≤ C) :
    min (T*K*(C*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
      (S*K*(C*(N+(N*T)^(2/3 : ℝ)+T^ξ))) ≤
      C*(N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J) := by
  have he (a b : ℝ) : a*K*(C*b) = C*(K*a*b) := by ring
  simp only [he,← mul_min_of_nonneg _ _ hC]
  exact mul_le_mul_of_nonneg_left (cube_block_numerical hS hT hK hN hJ hξ hξ2) hC

lemma cube_scaled_sizes {j : ℕ} {z : ℕ×ℕ×ℕ} (hz : z ∈ cubeDyadTriples j) :
    (2*(2 : ℝ)^z.1)*(2*(2 : ℝ)^z.2.1)^2*(2*(2 : ℝ)^z.2.2)^3 ≤ 128*(2 : ℝ)^j := by
  have h := mul_le_mul_of_nonneg_left (cubeDyad_sizes hz) (by norm_num : (0 : ℝ) ≤ 64)
  nlinarith only [h]

lemma SieveExponent.cube_bound {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      ∀ j : ℕ,
      finiteCubicBound P (frequencyDyad j) ≤ D*(N*(128*(2 : ℝ)^j))^ε*
        (N*(128*(2 : ℝ)^j)^(1/3 : ℝ)+(128*(2 : ℝ)^j*N)^(2/3 : ℝ)+
         (128*(2 : ℝ)^j)^ξ+128*(2 : ℝ)^j) := by
  obtain ⟨C,hC,hbound⟩ := hExp (ε/2) (by linarith)
  obtain ⟨E,hE,hpoly⟩ := dyadic_polynomial_small_power 3 (show 0 < ε/2 by linarith)
  refine ⟨((nonzeroNormBall 729).card+1)*324*C*E,by positivity,?_⟩
  intro P N hN hP j
  let J : ℝ := 128*(2 : ℝ)^j
  let F : ℝ := N*J^(1/3 : ℝ)+(J*N)^(2/3 : ℝ)+J^ξ+J
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hJ : 1 ≤ J := by dsimp [J]; have : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num); linarith
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpp := fun b hb => (hP b hb).1
  have hsf (i : ℕ) : ∀ a ∈ squarefreePrimaryDyad i, primary a ∧ Squarefree a ∧ norm a ≤ 2*(2 : ℝ)^i := by
    intro a ha
    have hh := mem_squarefreePrimaryDyad.mp ha
    exact ⟨hh.2.1,hh.2.2,(frequencyDyad_norm hh.1).2⟩
  have hn (i : ℕ) : 1 ≤ 2*(2 : ℝ)^i := by have : (1 : ℝ) ≤ 2^i := one_le_pow₀ (by norm_num); linarith
  have hsieve (i : ℕ) (hi : 2*(2 : ℝ)^i ≤ J) :
      finiteCubicBound P (squarefreePrimaryDyad i) ≤ C*(N*J)^(ε/2)*
        (N+(N*(2*(2 : ℝ)^i))^(2/3 : ℝ)+(2*(2 : ℝ)^i)^ξ) := by
    rw [finiteCubicBound_symm P _ hpp (fun a ha => (hsf i a ha).1)]
    apply (hbound _ _ N (2*(2 : ℝ)^i) hN (hn i) (hsf i) hP).trans
    gcongr
  have hblock (z : ℕ×ℕ×ℕ) (hz : z ∈ cubeDyadTriples j) :
      min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
        finiteCubicBound P (squarefreePrimaryDyad z.1))
        (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
        finiteCubicBound P (squarefreePrimaryDyad z.2.1)) ≤
          324*C*(N*J)^(ε/2)*F := by
    let S : ℝ := 2*(2 : ℝ)^z.1
    let T : ℝ := 2*(2 : ℝ)^z.2.1
    let K : ℝ := 2*(2 : ℝ)^z.2.2
    have hS : 1 ≤ S := hn _
    have hT : 1 ≤ T := hn _
    have hK : 1 ≤ K := hn _
    have hprod : S*T^2*K^3 ≤ J := cube_scaled_sizes hz
    have hSle : S ≤ J := (le_mul_of_one_le_right (by linarith : 0 ≤ S)
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT) (one_le_pow₀ hK))).trans
      (by simpa only [mul_assoc] using hprod)
    have hTle : T ≤ J := by
      have ht : T ≤ T^2 := le_self_pow₀ hT (by norm_num : (2 : ℕ) ≠ 0)
      have ht' : T^2 ≤ S*T^2*K^3 := by
        calc
          _ ≤ S*T^2 := le_mul_of_one_le_left (sq_nonneg _) hS
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hK)
      exact ht.trans (ht'.trans hprod)
    have hcardS : ((squarefreePrimaryDyad z.1).card : ℝ) ≤ 18*S := by dsimp [S]; nlinarith [squarefreePrimaryDyad_card_le z.1]
    have hcardT : ((squarefreePrimaryDyad z.2.1).card : ℝ) ≤ 18*T := by dsimp [T]; nlinarith [squarefreePrimaryDyad_card_le z.2.1]
    have hcardK : ((frequencyDyad z.2.2).card : ℝ) ≤ 18*K := by dsimp [K]; nlinarith [frequencyDyad_card_le z.2.2]
    calc
      _ ≤ min ((18*T)*(18*K)*(C*(N*J)^(ε/2)*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
          ((18*S)*(18*K)*(C*(N*J)^(ε/2)*(N+(N*T)^(2/3 : ℝ)+T^ξ))) := by
        have hbs := hsieve _ hSle
        have hbt := hsieve _ hTle
        have hbs0 := finiteCubicBound_nonneg P (squarefreePrimaryDyad z.1)
        have hbt0 := finiteCubicBound_nonneg P (squarefreePrimaryDyad z.2.1)
        apply min_le_min <;> gcongr
      _ = min (T*K*((324*C*(N*J)^(ε/2))*(N+(N*S)^(2/3 : ℝ)+S^ξ)))
          (S*K*((324*C*(N*J)^(ε/2))*(N+(N*T)^(2/3 : ℝ)+T^ξ))) := by congr 1 <;> ring
      _ ≤ _ := cube_block_scaled hS hT hK hN0.le hprod hξ hξ2 (by positivity)
  have hcount : ((cubeDyadTriples j).card : ℝ) ≤ E*J^(ε/2) := by
    have hc : ((cubeDyadTriples j).card : ℝ) ≤ ((j : ℝ)+2)^3 := by exact_mod_cast cubeDyadTriples_card j
    apply (hc.trans (hpoly j)).trans
    gcongr
    dsimp [J]
    have hh : (0 : ℝ) ≤ 2^j := by positivity
    linarith
  have hpow : J^(ε/2)*(N*J)^(ε/2) ≤ (N*J)^ε := by
    calc
      _ ≤ (N*J)^(ε/2)*(N*J)^(ε/2) := by
        gcongr
        exact le_mul_of_one_le_left hJ0.le hN
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  calc
    _ ≤ (nonzeroNormBall 729).card*∑ z ∈ cubeDyadTriples j,
        min (((squarefreePrimaryDyad z.2.1).card : ℝ)*(frequencyDyad z.2.2).card*
          finiteCubicBound P (squarefreePrimaryDyad z.1))
          (((squarefreePrimaryDyad z.1).card : ℝ)*(frequencyDyad z.2.2).card*
          finiteCubicBound P (squarefreePrimaryDyad z.2.1)) := finiteCubicBound_frequency_cube P hpp j
    _ ≤ (nonzeroNormBall 729).card*(((cubeDyadTriples j).card : ℝ)*(324*C*(N*J)^(ε/2)*F)) :=
      mul_le_mul_of_nonneg_left ((Finset.sum_le_card_nsmul _ _ _ hblock).trans_eq (by rw [nsmul_eq_mul])) (by positivity)
    _ ≤ (nonzeroNormBall 729).card*(E*J^(ε/2)*(324*C*(N*J)^(ε/2)*F)) := by gcongr
    _ = ((nonzeroNormBall 729).card*324*C*E)*(J^(ε/2)*(N*J)^(ε/2))*F := by ring
    _ ≤ ((nonzeroNormBall 729).card*324*C*E)*(N*J)^ε*F := by gcongr
    _ ≤ _ := by dsimp only [F,J]; gcongr; linarith

end CubicFirstMoment
end
end

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma decayConstant_pos {α : ℝ} (hα : 0 < α) : 0 < decayConstant α := by
  have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hα
  dsimp [decayConstant]; positivity

lemma finite_polynomial_dyadic_bound {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (ha : ∀ i, 0 < a i ∧ a i ≤ 4) (hv : ∀ i, 0 ≤ v i)
    (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hb : ∀ j, f j ≤ ∑ i, v i*((2 : ℝ)^j)^(a i))
    {c : ℝ} (hc : 0 < c) :
    (∑' j : ℕ, f j/(1+c*2^j)^8) ≤ ∑ i, v i*decayConstant (a i)*c^(-(a i)) := by
  have hs (i : ι) := (real_dyadic_decay (a i) (ha i).1 (ha i).2 hc).1.mul_left (v i)
  have hsum : Summable (fun j : ℕ => ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8)) :=
    summable_sum (fun i _ => hs i)
  have hmajor (j : ℕ) : f j/(1+c*2^j)^8 ≤ ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8) := by
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hb j) (by positivity)
  have hf' := hsum.of_nonneg_of_le (fun j => div_nonneg (hf j) (by positivity)) hmajor
  calc
    _ ≤ ∑' j : ℕ, ∑ i, v i*(((2 : ℝ)^j)^(a i)/(1+c*2^j)^8) := hf'.tsum_le_tsum hmajor hsum
    _ = ∑ i, v i*∑' j : ℕ, ((2 : ℝ)^j)^(a i)/(1+c*2^j)^8 := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
      simp only [tsum_mul_left]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => (mul_le_mul_of_nonneg_left
      (real_dyadic_decay (a i) (ha i).1 (ha i).2 hc).2 (hv i)).trans_eq (by dsimp [decayConstant]; ring))

lemma SieveExponent.dual_bound {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N c : ℝ), 1 ≤ N → 0 < c →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      dualDyadicNorm P c 8 ≤ C*N^δ*
        (N*c^(-(δ+1/3 : ℝ))+N^(2/3 : ℝ)*c^(-(δ+2/3 : ℝ))+
          c^(-(δ+ξ))+c^(-(δ+1))) := by
  obtain ⟨D,hD,hcube⟩ := hExp.cube_bound hξ hξ2 hδ
  let a : Fin 4 → ℝ := ![δ+1/3,δ+2/3,δ+ξ,δ+1]
  have ha : ∀ i, 0 < a i ∧ a i ≤ 4 := by intro i; fin_cases i <;> dsimp [a] <;> constructor <;> linarith
  let E : ℝ := ∑ i : Fin 4, (128 : ℝ)^(a i)*decayConstant (a i)
  have htermpos (i : Fin 4) : 0 < (128 : ℝ)^(a i)*decayConstant (a i) :=
    mul_pos (by positivity) (decayConstant_pos (ha i).1)
  have hE : 0 < E := by
    exact Finset.sum_pos (fun i _ => htermpos i) (Finset.univ_nonempty)
  refine ⟨D*E,by positivity,?_⟩
  intro P N c hN hc hP
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  let w : Fin 4 → ℝ := ![N,N^(2/3 : ℝ),1,1]
  have hw : ∀ i, 0 ≤ w i := by intro i; fin_cases i <;> dsimp [w] <;> positivity
  let v : Fin 4 → ℝ := fun i => D*N^δ*w i*(128 : ℝ)^(a i)
  have hv : ∀ i, 0 ≤ v i := by intro i; dsimp [v]; exact mul_nonneg (mul_nonneg (by positivity) (hw i)) (by positivity)
  have hexpand (j : ℕ) : D*(N*(128*(2 : ℝ)^j))^δ*
        (N*(128*(2 : ℝ)^j)^(1/3 : ℝ)+(128*(2 : ℝ)^j*N)^(2/3 : ℝ)+
         (128*(2 : ℝ)^j)^ξ+128*(2 : ℝ)^j) =
      ∑ i : Fin 4, v i*((2 : ℝ)^j)^(a i) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,Matrix.cons_val_zero,
      Matrix.cons_val_succ,v,w,a,add_zero]
    simp only [Real.mul_rpow (by positivity : (0 : ℝ) ≤ N) (by positivity : (0 : ℝ) ≤ 128*(2 : ℝ)^j),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 128) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^j),
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 128*(2 : ℝ)^j) (by positivity : (0 : ℝ) ≤ N),
      Real.rpow_add (by norm_num : (0 : ℝ) < 128),Real.rpow_add (by positivity : (0 : ℝ) < (2 : ℝ)^j),Real.rpow_one]
    ring
  have hh := finite_polynomial_dyadic_bound a v ha hv (fun j => finiteCubicBound P (frequencyDyad j))
    (fun j => finiteCubicBound_nonneg _ _)
    (fun j => (hcube P N hN hP j).trans_eq (hexpand j)) hc
  have hEi (i : Fin 4) : (128 : ℝ)^(a i)*decayConstant (a i) ≤ E :=
    Finset.single_le_sum (fun i _ => (htermpos i).le) (Finset.mem_univ i)
  calc
    _ ≤ ∑ i : Fin 4, v i*decayConstant (a i)*c^(-(a i)) := hh
    _ = ∑ i : Fin 4, (D*N^δ)*(w i*c^(-(a i)))*((128 : ℝ)^(a i)*decayConstant (a i)) := by
      apply Finset.sum_congr rfl; intro i _; dsimp [v]; ring
    _ ≤ ∑ i : Fin 4, (D*N^δ)*(w i*c^(-(a i)))*E := by
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (hEi i) (mul_nonneg (by positivity) (mul_nonneg (hw i) (by positivity)))
    _ = _ := by
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,a,w,Matrix.cons_val_zero,
        Matrix.cons_val_succ,add_zero,one_mul]
      ring

end CubicFirstMoment
end
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergent norm series on the Eisenstein lattice

These elementary lattice bounds provide a quantitative tail for the
Möbius residue sum after square-divisor truncation.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment

lemma norm_rpow_tail_pointwise {D s t : ℝ} (hD : 0 < D) (hst : s < t)
    {a : Eisenstein} (ha : D < norm a) :
    norm a^(-t) ≤ D^(s-t)*norm a^(-s) := by
  have hn : 0 < norm a := hD.trans ha
  calc
    _ = norm a^(s-t)*norm a^(-s) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hD ha.le (by linarith))
      (Real.rpow_nonneg hn.le _)

/-- A stronger convergent exponent gives a power tail without losing a
factor to the norm fibers. -/
theorem eisenstein_norm_rpow_tail {D s t : ℝ} (hD : 0 < D)
    (hs : 1 < s) (hst : s < t) :
    (∑' a : Eisenstein, if D < norm a then norm a^(-t) else 0) ≤
      D^(s-t)*(∑' a : Eisenstein, norm a^(-s)) := by
  have ht := summable_eisenstein_norm_rpow (hs.trans hst)
  have htail := ht.indicator (fun a => D < norm a)
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ htail ((summable_eisenstein_norm_rpow hs).mul_left _)
  intro a
  change (if D < norm a then norm a^(-t) else 0) ≤ D^(s-t)*norm a^(-s)
  by_cases ha : D < norm a
  · simpa only [ha,ite_true, if_true] using norm_rpow_tail_pointwise hD hst ha
  · simp only [ha,ite_false, if_false]
    exact mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (norm_nonneg a) _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeSquareSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse support from a large square divisor, used to remove repeated
large primes in the exceptional character moments. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma square_multiples_normBall {Y : ℝ} {d b : Eisenstein}
    (hd : d ≠ 0) (hb : b ∈ nonzeroNormBall Y) (hdiv : d^2 ∣ b) :
    b ∈ (nonzeroNormBall (Y/(norm d)^2)).image (fun c => d^2*c) := by
  obtain ⟨c,rfl⟩ := hdiv
  have hspec := mem_nonzeroNormBall.mp hb
  have hc : c ≠ 0 := by intro h; simp [h] at hspec
  have hnorm : norm (d^2*c) = (norm d)^2*norm c := by
    simp [pow_two,mul_assoc]
  apply Finset.mem_image.mpr
  refine ⟨c,mem_nonzeroNormBall.mpr ⟨?_,hc⟩,rfl⟩
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_of_ne_zero hd))).mpr
  have h := hspec.1
  rw [hnorm] at h
  nlinarith

/-- Cardinality is at most `C Y / sqrt D`, uniformly for positive `D`.
The proof uses only planar lattice counting and a convergent norm series. -/
theorem largeSquareSupport_card_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ Y D : ℝ, 0 ≤ Y → 0 < D →
      ((largeSquareSupport Y D).card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) := by
  let Z := ∑' d : Eisenstein, norm d^(-(3/2:ℝ))
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  refine ⟨18*Z+1,by positivity,?_⟩
  intro Y D hY hD
  let T := (nonzeroNormBall Y).filter (fun d => D < norm d)
  let F (d : Eisenstein) := (nonzeroNormBall (Y/(norm d)^2)).image (fun c => d^2*c)
  have hcover : largeSquareSupport Y D ⊆ T.biUnion F := by
    intro b hb
    obtain ⟨hball,d,hd,hdiv⟩ := Finset.mem_filter.mp hb
    have hd0 : d ≠ 0 := norm_eq_zero_iff.not.mp (ne_of_gt (hD.trans hd))
    have hdvd : d ∣ b := (dvd_pow_self d (by norm_num : 2 ≠ 0)).trans hdiv
    have hdb : norm d ≤ norm b := norm_le_of_dvd (mem_nonzeroNormBall.mp hball).2 hdvd
    apply Finset.mem_biUnion.mpr
    refine ⟨d,Finset.mem_filter.mpr ⟨mem_nonzeroNormBall.mpr
      ⟨hdb.trans (mem_nonzeroNormBall.mp hball).1,hd0⟩,hd⟩,?_⟩
    exact square_multiples_normBall hd0 hball hdiv
  have hcard : ((largeSquareSupport Y D).card:ℝ) ≤ ∑ d ∈ T, ((F d).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsum : (∑ d ∈ T, 1/(norm d)^2) ≤ D^(-(1/2:ℝ))*Z := by
    have htail := eisenstein_norm_rpow_tail (s := (3/2:ℝ)) (t := 2) hD
      (by norm_num) (by norm_num)
    norm_num only at htail
    apply le_trans _ htail
    have hs := (summable_eisenstein_norm_rpow (s := 2) (by norm_num)).indicator
      (fun d => D < norm d)
    calc
      _ = ∑ d ∈ T, if D < norm d then norm d^(-(2:ℝ)) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hn := (Finset.mem_filter.mp hd).2
        rw [ite_eq_left hn,Real.rpow_neg (norm_nonneg d),Real.rpow_two,one_div]
      _ ≤ _ := hs.sum_le_tsum T (fun d _ => by
        split_ifs
        · exact Real.rpow_nonneg (norm_nonneg d) _
        · exact le_rfl)
  calc
    _ ≤ ∑ d ∈ T, ((F d).card:ℝ) := hcard
    _ ≤ ∑ d ∈ T, 18*(Y/(norm d)^2) := by
      apply Finset.sum_le_sum
      intro d hd
      have hi : ((F d).card:ℝ) ≤ ((nonzeroNormBall (Y/(norm d)^2)).card:ℝ) := by
        exact_mod_cast Finset.card_image_le
      exact hi.trans (nonzeroNormBall_card_le (by positivity))
    _ = 18*Y*(∑ d ∈ T, 1/(norm d)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 18*Y*(D^(-(1/2:ℝ))*Z) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg hD.le (-(1/2:ℝ))]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher prime powers in the von Mangoldt replacement have sparse support,
even when the underlying prime is small. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primePower_norm_pow (p : Eisenstein) (j : ℕ) : norm (p^j) = norm p^j := by
  induction j with
  | zero => simp [norm]
  | succ j ih => rw [pow_succ,norm_mul_eq,ih,pow_succ]

/-- Extracting half the exponent produces a genuinely large square divisor.
The bound depends on the prime-power norm, not the prime norm. -/
lemma large_square_of_prime_power {p b : Eisenstein} (hp : p ≠ 0) {j : ℕ}
    (hj : 2 ≤ j) {Y c : ℝ} (hY : 0 < Y)
    (hlarge : Y^c < norm (p^j)) (hdiv : p^j ∣ b) :
    ∃ d : Eisenstein, Y^(c/4) < norm d ∧ d^2 ∣ b := by
  refine ⟨p^(j/2),?_,?_⟩
  · have he : j ≤ 4*(j/2) := by omega
    have hpow : norm (p^j) ≤ norm (p^(j/2))^4 := by
      rw [primePower_norm_pow,primePower_norm_pow,← pow_mul]
      rw [Nat.mul_comm (j/2) 4]
      exact pow_le_pow_right₀ (one_le_norm hp) he
    have hYpow : (Y^(c/4))^4 = Y^c := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hY.le]
      congr 1
      norm_num
    by_contra! hn
    have hd := pow_le_pow_left₀ (norm_nonneg _) hn 4
    rw [hYpow] at hd
    exact (hlarge.trans_le hpow).not_ge hd
  · apply dvd_trans _ hdiv
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)

lemma largePrimePowerSupport_subset {Y c : ℝ} (hY : 0 < Y) :
    largePrimePowerSupport Y c ⊆ largeSquareSupport Y (Y^(c/4)) := by
  intro b hb
  obtain ⟨hball,p,j,hp,hj,hlarge,hdiv⟩ := Finset.mem_filter.mp hb
  obtain ⟨d,hd,hdvd⟩ := large_square_of_prime_power hp.2.ne_zero hj hY hlarge hdiv
  exact Finset.mem_filter.mpr ⟨hball,d,hd,hdvd⟩

/-- A fixed positive power is saved for every higher-prime-power error support. -/
theorem largePrimePowerSupport_card_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y c : ℝ), 0 < Y →
      ((largePrimePowerSupport Y c).card:ℝ) ≤ K*Y^(1-c/8) := by
  obtain ⟨K,hK,hbound⟩ := largeSquareSupport_card_bound
  refine ⟨K,hK,?_⟩
  intro Y c hY
  have h := hbound Y (Y^(c/4)) hY.le (Real.rpow_pos_of_pos hY _)
  have hcard : ((largePrimePowerSupport Y c).card:ℝ) ≤
      ((largeSquareSupport Y (Y^(c/4))).card:ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (largePrimePowerSupport_subset hY))
  have he : K*Y*(Y^(c/4))^(-(1/2:ℝ)) = K*Y^(1-c/8) := by
    rw [mul_assoc]
    congr 1
    calc
      _ = Y^(1:ℝ)*Y^(c/4*(-(1/2:ℝ))) := by
        rw [Real.rpow_one,← Real.rpow_mul hY.le]
      _ = Y^(1+c/4*(-(1/2:ℝ))) := (Real.rpow_add hY _ _).symm
      _ = _ := by congr 1; ring
  exact hcard.trans (h.trans_eq he)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean values of the squarefree prime-convolution discrepancy

The ordinary Montgomery--Vaughan input is specialized to the actual
coefficients obtained from independent prime factors.  The full polynomial
factors exactly; removing repeated primes costs the energy already proved
in `RepeatedPrimeSupport`.  The maximum multiplicity of an integer norm is
kept explicit, so no divisor estimate is hidden in this deduction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A character bounded by one does not increase coefficient energy,
including at primes dividing its conductor, where it may vanish. -/
lemma coefficient_twist_energy_le (B : Finset Eisenstein)
    (β χ : Eisenstein → ℂ) (hχ : ∀ b ∈ B, ‖χ b‖ ≤ 1) :
    (∑ b ∈ B, ‖β b * χ b‖ ^ 2) ≤ ∑ b ∈ B, ‖β b‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro b hb
  apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
  rw [norm_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hχ b hb) (_root_.norm_nonneg (β b))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UnrestrictedCubicSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved cubic large sieve with an unrestricted inner coefficient
support. The cube decomposition is already in the baseline; here its
summed dyadic bound is transferred to a sharp norm cutoff. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteCubicBound_le_dualDyadicNorm (P H : Finset Eisenstein)
    (hP : ∀ p ∈ P, primary p) {Z : ℝ} (hZ : 0 < Z)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Z) :
    finiteCubicBound P H ≤ 256*dualDyadicNorm P (1/Z) 8 := by
  let J := H.image (fun h => Nat.log 2 (normNat h))
  have hz : 0 < 1/Z := by positivity
  have hs := summable_dualDyadicNorm P hP hz (by norm_num : 2 ≤ 8)
  apply (finiteCubicBound_le_iff _ _ (mul_nonneg (by norm_num)
    (dualDyadicNorm_nonneg P hz.le 8))).mpr
  intro v
  let E := ∑ p ∈ P, ‖v p‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdyad (j : ℕ) (hj : j ∈ J) :
      finiteCubicBound P (frequencyDyad j) ≤
        256*(finiteCubicBound P (frequencyDyad j)/(1+(1/Z)*2^j)^8) := by
    obtain ⟨h,hh,hlog⟩ := Finset.mem_image.mp hj
    have hhj : h ∈ frequencyDyad j := mem_frequencyDyad.mpr ⟨(hH h hh).1,hlog⟩
    have hpow : (2:ℝ)^j ≤ Z := (frequencyDyad_norm hhj).1.trans (hH h hh).2
    have hsmall : (1/Z)*(2:ℝ)^j ≤ 1 := by
      rw [one_div,mul_comm,← div_eq_mul_inv]
      exact (div_le_one hZ).mpr hpow
    have hden : 0 < (1+(1/Z)*(2:ℝ)^j)^8 := by positivity
    have hdenle : (1+(1/Z)*(2:ℝ)^j)^8 ≤ 256 := by
      have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(1/Z)*(2:ℝ)^j)
        (show 1+(1/Z)*(2:ℝ)^j ≤ 2 by linarith) 8
      norm_num at h ⊢
      exact h
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    exact (mul_le_mul_of_nonneg_left hdenle (finiteCubicBound_nonneg _ _)).trans_eq (mul_comm _ _)
  calc
    (∑ h ∈ H, ‖∑ p ∈ P, v p*cubicSymbol p h‖^2) =
        ∑ j ∈ J, ∑ h ∈ H with Nat.log 2 (normNat h) = j,
          ‖∑ p ∈ P, v p*cubicSymbol p h‖^2 :=
      (Finset.sum_fiberwise_of_maps_to (fun h hh => Finset.mem_image_of_mem _ hh) _).symm
    _ ≤ ∑ j ∈ J, finiteCubicBound P (frequencyDyad j)*E := by
      apply Finset.sum_le_sum
      intro j hj
      have hsub : H.filter (fun h => Nat.log 2 (normNat h) = j) ⊆ frequencyDyad j := by
        intro h hh
        exact mem_frequencyDyad.mpr ⟨(hH h (Finset.mem_filter.mp hh).1).1,
          (Finset.mem_filter.mp hh).2⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
        (finiteCubicBound_controls_mass P (frequencyDyad j) v)
    _ ≤ ∑ j ∈ J, (256*(finiteCubicBound P (frequencyDyad j)/(1+(1/Z)*2^j)^8))*E :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hdyad j hj) hE)
    _ = (256*∑ j ∈ J, finiteCubicBound P (frequencyDyad j)/(1+(1/Z)*2^j)^8)*E := by
      simp only [Finset.mul_sum,Finset.sum_mul]
    _ ≤ (256*dualDyadicNorm P (1/Z) 8)*E := by
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hs.sum_le_tsum J (fun j _ => div_nonneg (finiteCubicBound_nonneg _ _) (by positivity))

private lemma inverse_negative_rpow {Z : ℝ} (hZ : 0 < Z) (a : ℝ) :
    (1/Z)^(-a) = Z^a := by
  rw [one_div,Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]

/-- Sharp cutoff form of the cube-extracted cubic sieve. The inner
support need not be squarefree or primary. -/
theorem unrestricted_cubic_operator_bound {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : Finset Eisenstein) (N Z : ℝ),
      1 ≤ N → 1 ≤ Z →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Z) →
      finiteCubicBound P H ≤ C*(N*Z)^ε*
        (N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z) := by
  obtain ⟨C,hC,hbound⟩ := SieveExponent.dual_bound (ξ := (4/3:ℝ))
    (by norm_num) (by norm_num) sieveExponent_four_thirds hε hε₁
  refine ⟨256*C,by positivity,?_⟩
  intro P H N Z hN hZ hP hH
  have hZ0 : 0 < Z := by linarith
  have hN0 : 0 < N := by linarith
  have h := hbound P N (1/Z) hN (by positivity) hP
  simp only [inverse_negative_rpow hZ0] at h
  apply (finiteCubicBound_le_dualDyadicNorm P H (fun p hp => (hP p hp).1) hZ0 hH).trans
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 256)).trans_eq
  rw [Real.mul_rpow hN0.le hZ0.le,Real.mul_rpow hN0.le hZ0.le]
  rw [Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_add hZ0,
    Real.rpow_one]
  ring

/-- Transposition of the actual finite cubic-character matrix. This does
not require reciprocity or primarity of the inner support. -/
lemma finiteCubicBound_controls_transpose (P H : Finset Eisenstein)
    (v : Eisenstein → ℂ) :
    (∑ p ∈ P, ‖∑ h ∈ H, v h*cubicSymbol p h‖^2) ≤
      finiteCubicBound P H * ∑ h ∈ H, ‖v h‖^2 := by
  let f (p : Eisenstein) := ∑ h ∈ H, v h*cubicSymbol p h
  let g (h : Eisenstein) := ∑ p ∈ P, f p*star (cubicSymbol p h)
  let E : ℝ := ∑ p ∈ P, ‖f p‖^2
  let V : ℝ := ∑ h ∈ H, ‖v h‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdual : (E:ℂ) = ∑ h ∈ H, v h*star (g h) := by
    change ((∑ p ∈ P, ‖f p‖^2:ℝ):ℂ) = _
    have hcast : ((∑ p ∈ P, ‖f p‖^2:ℝ):ℂ) =
        ∑ p ∈ P, ((‖f p‖^2:ℝ):ℂ) := map_sum Complex.ofRealHom _ _
    rw [hcast]
    simp_rw [Complex.ofReal_pow,← Complex.mul_conj']
    conv_lhs => arg 2; ext p; lhs; unfold f
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    simp only [g,star_sum,star_mul,star_star,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [starRingEnd_apply]
    ring
  have hg : (∑ h ∈ H, ‖g h‖^2) ≤ finiteCubicBound P H*E := by
    have h := finiteCubicBound_controls_mass P H (fun p => star (f p))
    have he (h : Eisenstein) : g h = star (∑ p ∈ P, star (f p)*cubicSymbol p h) := by
      simp only [g,star_sum,star_mul,star_star,mul_comm]
    simpa only [he,norm_star] using h
  have hCS := complex_bilinear_rows_sq H v (fun h => star (g h))
  rw [← hdual,Complex.norm_real,Real.norm_of_nonneg hE] at hCS
  simp only [norm_star] at hCS
  change E^2 ≤ V*(∑ h ∈ H, ‖g h‖^2) at hCS
  have hmul := mul_le_mul_of_nonneg_left hg hV
  change E ≤ finiteCubicBound P H*V
  by_cases hz : E = 0
  · rw [hz]
    exact mul_nonneg (finiteCubicBound_nonneg _ _) hV
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    nlinarith

theorem unrestricted_cubic_sieve {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : Finset Eisenstein) (N Z : ℝ),
      1 ≤ N → 1 ≤ Z →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Z) → ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ h ∈ H, v h*cubicSymbol p h‖^2) ≤
      C*(N*Z)^ε*(N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z)*
        ∑ h ∈ H, ‖v h‖^2 := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_cubic_operator_bound hε hε₁
  refine ⟨C,hC,?_⟩
  intro P H N Z hN hZ hP hH v
  exact (finiteCubicBound_controls_transpose P H v).trans
    (mul_le_mul_of_nonneg_right (hbound P H N Z hN hZ hP hH)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FirstShapeErrorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse error terms in the first exceptional conductor configuration. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem unrestricted_mixed_product_sieve {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q H : Finset Eisenstein) (N Z : ℝ),
      1 ≤ N → 1 ≤ Z →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ N) →
      (∀ q ∈ Q, primary q) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Z) →
      ∀ v : Eisenstein → ℂ,
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ h ∈ H, v h*mixedCubic p q h‖^2) ≤
        (Q.card:ℝ)*C*(N*Z)^ε*(N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z)*
          ∑ h ∈ H, ‖v h‖^2 := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_cubic_sieve hε hε₁
  refine ⟨C,hC,?_⟩
  intro P Q H N Z hN hZ hP hQ hH v
  have hrow (q : Eisenstein) (hq : q ∈ Q) :
      (∑ p ∈ P, ‖∑ h ∈ H, v h*mixedCubic p q h‖^2) ≤
      C*(N*Z)^ε*(N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z)*
        ∑ h ∈ H, ‖v h‖^2 := by
    have he (p : Eisenstein) : (∑ h ∈ H, v h*mixedCubic p q h) =
        ∑ h ∈ H, (v h*star (cubicSymbol q h))*cubicSymbol p h := by
      apply Finset.sum_congr rfl
      intro h hh
      unfold mixedCubic
      ring
    simp_rw [he]
    apply (hbound P H N Z hN hZ hP hH (fun h => v h*star (cubicSymbol q h))).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro h hh
    rw [norm_mul,norm_star,mul_pow]
    apply mul_le_of_le_one_right (sq_nonneg _)
    simpa only [one_pow] using pow_le_pow_left₀ (_root_.norm_nonneg _)
      (norm_cubicSymbol_le_one (hQ q hq) h) 2
  calc
    _ ≤ ∑ _q ∈ Q,
        C*(N*Z)^ε*(N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z)*
          ∑ h ∈ H, ‖v h‖^2 := Finset.sum_le_sum hrow
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; ring

private lemma first_shape_sieve_power {Y θ : ℝ} (hY : 1 ≤ Y) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) :
    Y^(θ/16) * (Y^(1+θ/16)*Y)^(θ/16) *
      (Y^(1+θ/16)*Y^(1/3:ℝ)+(Y^(1+θ/16)*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y) *
        Y^(1-θ) ≤ 4*Y^(7/3-θ/2) := by
  have hY0 : 0 < Y := by linarith
  have hNY : Y^(1+θ/16)*Y = Y^(2+θ/16) := by
    calc
      _ = Y^(1+θ/16)*Y^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hY0]; congr 1; ring
  have hfirst : Y^(1+θ/16)*Y^(1/3:ℝ) = Y^(4/3+θ/16) := by
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  have hsecond : (Y^(1+θ/16)*Y)^(2/3:ℝ) ≤ Y^(4/3+θ/16) := by
    rw [hNY,← Real.rpow_mul hY0.le]
    exact Real.rpow_le_rpow_of_exponent_le hY (by nlinarith)
  have hthird : Y^(4/3:ℝ) ≤ Y^(4/3+θ/16) :=
    Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hlast : Y ≤ Y^(4/3+θ/16) := by
    nth_rw 1 [← Real.rpow_one Y]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hpoly : Y^(1+θ/16)*Y^(1/3:ℝ)+(Y^(1+θ/16)*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y ≤
      4*Y^(4/3+θ/16) := by rw [hfirst]; linarith
  calc
    _ ≤ Y^(θ/16)*(Y^(1+θ/16)*Y)^(θ/16)*(4*Y^(4/3+θ/16))*Y^(1-θ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by positivity)) (by positivity)
    _ = 4*Y^(7/3-θ+2*(θ/16)+(2+θ/16)*(θ/16)) := by
      rw [hNY,← Real.rpow_mul hY0.le]
      calc
        _ = 4*(Y^(θ/16)*Y^((2+θ/16)*(θ/16))*Y^(4/3+θ/16)*Y^(1-θ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hY0,← Real.rpow_add hY0,← Real.rpow_add hY0]
          congr 1
          ring_nf
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hY
      nlinarith

/-- Sparse coefficient energy supplies a fixed saving for the first
exceptional conductor shape. All arithmetic support conditions are kept
on the actual coefficient and character sets. -/
theorem first_shape_sparse_mixed_moment {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y E : ℝ), 1 ≤ Y → 0 ≤ E →
      ∀ (P Q H : Finset Eisenstein),
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ Y^(1+θ/16)) →
      (∀ q ∈ Q, primary q ∧ norm q ≤ Y^(θ/16)) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Y) →
      ∀ v : Eisenstein → ℂ, (∑ h ∈ H, ‖v h‖^2) ≤ E*Y^(1-θ) →
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ h ∈ H, v h*mixedCubic p q h‖^2) ≤
        C*E*Y^(7/3-θ/2) := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_mixed_product_sieve
    (show 0 < θ/16 by positivity) (show θ/16 ≤ 1 by linarith)
  refine ⟨72*C,by positivity,?_⟩
  intro Y E hY hE P Q H hP hQ hH v hv
  have hN : 1 ≤ Y^(1+θ/16) := Real.one_le_rpow hY (by positivity)
  have hraw := hbound P Q H (Y^(1+θ/16)) Y hN hY hP (fun q hq => (hQ q hq).1) hH v
  have hQsub : Q ⊆ nonzeroNormBall (Y^(θ/16)) := fun q hq =>
    mem_nonzeroNormBall.mpr ⟨(hQ q hq).2,primary_ne_zero (hQ q hq).1⟩
  have hQcard : (Q.card:ℝ) ≤ 18*Y^(θ/16) :=
    (Nat.cast_le.mpr (Finset.card_le_card hQsub)).trans (nonzeroNormBall_card_le (by positivity))
  have hY0 : 0 < Y := by linarith
  calc
    _ ≤ (18*Y^(θ/16))*C*(Y^(1+θ/16)*Y)^(θ/16)*
        (Y^(1+θ/16)*Y^(1/3:ℝ)+(Y^(1+θ/16)*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y)*
          (E*Y^(1-θ)) := by
      apply hraw.trans
      gcongr
    _ = (18*C*E)*(Y^(θ/16)*(Y^(1+θ/16)*Y)^(θ/16)*
        (Y^(1+θ/16)*Y^(1/3:ℝ)+(Y^(1+θ/16)*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y)*Y^(1-θ)) := by ring
    _ ≤ (18*C*E)*(4*Y^(7/3-θ/2)) :=
      mul_le_mul_of_nonneg_left (first_shape_sieve_power hY hθ hθ₁) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

/-- On the powers of one prime ideal, Dirichlet convolution with the
constant-one function is the ordinary partial sum of coefficients. -/
lemma coeff_mul_zeta_single (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) =
      ∑ k ∈ Finset.range (n + 1), MvPowerSeries.coeff (Finsupp.single p k) A := by
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
    MvPowerSeries.coeff_apply, idealZeta, mul_one]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k _ => A (Finsupp.single p k)) n

lemma coeff_single_eq_zeta_difference (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) A =
      MvPowerSeries.coeff (Finsupp.single p (n + 1)) (A * idealZeta) -
        MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) := by
  rw [coeff_mul_zeta_single, coeff_mul_zeta_single, Finset.sum_range_succ]
  ring

lemma idealZeta_mul_moebiusSeries : idealZeta * idealMoebiusSeries = 1 := by
  rw [mul_comm, idealMoebiusSeries_mul_zeta]

lemma idealZeta_mul_vonMangoldt : idealZeta * idealVonMangoldt = idealLogNorm := by
  rw [idealVonMangoldt, ← mul_assoc, idealZeta_mul_moebiusSeries, one_mul]

/-- The ideal von Mangoldt weight on every positive prime power is
exactly the logarithm of the prime-ideal norm. -/
lemma idealVonMangoldt_prime_power (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) idealVonMangoldt =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  rw [coeff_single_eq_zeta_difference, mul_comm idealVonMangoldt idealZeta,
    idealZeta_mul_vonMangoldt]
  simp only [MvPowerSeries.coeff_apply, idealLogNorm, idealExponentNorm_single,
    Real.log_pow]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMoebiusBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler products identify and bound the arithmetic Möbius coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_support_card {a : Eisenstein} (ha : Squarefree a) :
    (idealExponentOf a).support.card = (UniqueFactorizationMonoid.factors a).card := by
  have hnodup : (Associates.factors' a).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    exact (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha
  change (Associates.factors' a).toFinset.card = _
  rw [Multiset.toFinset_card_of_nodup hnodup]
  have h := congrArg Multiset.card (Associates.map_subtype_coe_factors' (a := a))
  simpa only [Multiset.card_map] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealVonMangoldt
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The convolution definition of ideal von Mangoldt has exactly its usual
prime-power coefficients. This is the arithmetic bridge for prime replacement
in the short Möbius decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealLogNorm_prime_difference (ν : EisensteinIdealExponent)
    (p : EisensteinIdealPrime) (hp : 1 ≤ ν p) :
    MvPowerSeries.coeff ν idealLogNorm -
        MvPowerSeries.coeff (ν - Finsupp.single p 1) idealLogNorm =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr hp
  have he : ν = (ν - Finsupp.single p 1) + Finsupp.single p 1 :=
    (tsub_add_cancel_of_le hle).symm
  change Real.log (idealExponentNorm ν) -
    Real.log (idealExponentNorm (ν - Finsupp.single p 1)) = _
  conv_lhs => lhs; rw [he, idealExponentNorm_add]
  rw [Real.log_mul (idealExponentNorm_pos _).ne' (idealExponentNorm_pos _).ne',
    idealExponentNorm_single, pow_one]
  ring

private lemma coeff_logNorm_finite_nonempty (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hS : S.Nonempty) (hν : S ⊆ ν.support) :
    MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius S) =
      if S.card = 1 then ∑ p ∈ S, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert p S hp ih =>
    have hνp : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (hν (Finset.mem_insert_self _ _)))
    have he : idealLogNorm * finiteIdealMoebius (insert p S) =
        (idealLogNorm * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, mul_sub, mul_one, map_sub, MvPowerSeries.X_def,
      MvPowerSeries.coeff_mul_monomial]
    simp only [Finsupp.single_le_iff, ite_eq_left hνp, mul_one]
    by_cases hSE : S = ∅
    · subst S
      simpa [finiteIdealMoebius] using idealLogNorm_prime_difference ν p hνp
    · have hS' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSE
      have hνS : S ⊆ ν.support := fun q hq => hν (Finset.mem_insert_of_mem hq)
      have hνS' : S ⊆ (ν - Finsupp.single p 1 : EisensteinIdealExponent).support := by
        intro q hq
        apply Finsupp.mem_support_iff.mpr
        have hqp : q ≠ p := ne_of_mem_of_not_mem hq hp
        simpa [Finsupp.tsub_apply, hqp] using Finsupp.mem_support_iff.mp (hνS hq)
      rw [ih ν hS' hνS, ih _ hS' hνS', sub_self]
      have hc : (insert p S).card ≠ 1 := by
        rw [Finset.card_insert_of_notMem hp]
        have := Finset.card_pos.mpr hS'
        omega
      simp [hc]

lemma idealVonMangoldt_coeff_eq_finite (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius ν.support) := by
  rw [idealVonMangoldt, mul_comm idealLogNorm, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a.1 ≤ ν := by
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp ha]
    exact le_add_of_nonneg_right zero_le
  rw [coeff_idealMoebiusSeries_eq_finite ν.support a.1 (Finsupp.support_mono hle)]

/-- The von Mangoldt coefficient is supported precisely on prime-ideal
powers and has weight the logarithm of that prime-ideal norm. -/
lemma idealVonMangoldt_coeff (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      if ν.support.card = 1 then
        ∑ p ∈ ν.support, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  rw [idealVonMangoldt_coeff_eq_finite]
  by_cases hs : ν.support.Nonempty
  · exact coeff_logNorm_finite_nonempty _ _ hs (Finset.Subset.refl _)
  · have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst ν
    simp only [Finsupp.support_zero, finiteIdealMoebius, Finset.prod_empty, mul_one,
      Finset.card_empty, Nat.zero_ne_one, ite_false, if_false]
    change Real.log (idealExponentNorm 0) = 0
    simp [idealExponentNorm, idealExponentGenerator]

lemma idealVonMangoldt_not_prime_power (ν : EisensteinIdealExponent)
    (hν : ν.support.card ≠ 1) :
    MvPowerSeries.coeff ν idealVonMangoldt = 0 := by
  rw [idealVonMangoldt_coeff, ite_eq_right hν]

lemma idealVonMangoldt_coeff_nonneg (ν : EisensteinIdealExponent) :
    0 ≤ MvPowerSeries.coeff ν idealVonMangoldt := by
  rw [idealVonMangoldt_coeff]
  split_ifs
  · apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    simpa only [idealExponentNorm_single, pow_one] using
      idealExponentNorm_ge_one (Finsupp.single p 1)
  · exact le_rfl

lemma idealVonMangoldt_coeff_le_logNorm (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt ≤ Real.log (idealExponentNorm ν) := by
  by_cases hc : ν.support.card = 1
  · obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
    have hlog : 0 ≤ Real.log (normNat (idealPrimeRepresentative p)) := by
      apply Real.log_nonneg
      simpa only [idealExponentNorm_single, pow_one] using
        idealExponentNorm_ge_one (Finsupp.single p 1)
    have hn : (1 : ℝ) ≤ (ν p : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    rw [idealVonMangoldt_coeff, ite_eq_left hc, he, Finsupp.support_single _ hp,
      Finset.sum_singleton, idealExponentNorm_single, Real.log_pow]
    exact le_mul_of_one_le_left hlog hn
  · rw [idealVonMangoldt_not_prime_power ν hc]
    exact Real.log_nonneg (idealExponentNorm_ge_one ν)

lemma idealVonMangoldt_at_prime {a : Eisenstein} (ha : Prime a) :
    MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt = Real.log (norm a) := by
  have hcard : (idealExponentOf a).support.card = 1 := by
    rw [idealExponentOf_support_card ha.irreducible.squarefree,
      UniqueFactorizationMonoid.card_factors_of_irreducible ha.irreducible]
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hcard
  have hone : idealExponentOf a p = 1 := by
    have hle := (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha.irreducible.squarefree p
    omega
  calc
    _ = MvPowerSeries.coeff (Finsupp.single p 1) idealVonMangoldt := by rw [he, hone]
    _ = Real.log (normNat (idealPrimeRepresentative p)) := idealVonMangoldt_prime_power p 0
    _ = Real.log (idealExponentNorm (idealExponentOf a)) := by
      rw [he, hone, idealExponentNorm_single, pow_one]
    _ = _ := by rw [idealExponentOf_norm ha.ne_zero]

/-- A nonzero von Mangoldt coefficient at an actual primary element
comes from an actual power of a primary prime, with no residual unit. -/
lemma idealVonMangoldt_primary_support {a : Eisenstein} (ha : primary a)
    (hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 0 < j ∧ a = p ^ j := by
  have hcard : (idealExponentOf a).support.card = 1 := by
    by_contra h
    exact hΛ (idealVonMangoldt_not_prime_power _ h)
  obtain ⟨p, hp, he⟩ := Finsupp.card_support_eq_one.mp hcard
  let j := idealExponentOf a p
  let r := idealPrimeRepresentative p
  have hj : 0 < j := Nat.pos_of_ne_zero hp
  have hgen : idealExponentGenerator (idealExponentOf a) = r ^ j := by
    rw [he]
    exact Finsupp.prod_single_index (h := fun q k => idealPrimeRepresentative q ^ k)
      (pow_zero _)
  have hassoc : Associated (r ^ j) a := by
    rw [← hgen]
    exact idealExponentOf_associated (primary_ne_zero ha)
  have hrdiv : r ∣ a := (dvd_pow_self r hj.ne').trans hassoc.dvd
  have hr : Prime r := (idealPrimeRepresentative_irreducible p).prime
  let q := primaryNormalize r
  have hq : primaryPrime q := ⟨primaryNormalize_primary
    (unit_residue_of_dvd_primary ha hrdiv), prime_primaryNormalize hr⟩
  have hqp : primary (q ^ j) := by
    induction j with
    | zero => simp [primary]
    | succ n ih => simpa only [pow_succ] using primary_mul ih hq.1
  refine ⟨q, j, hq, hj, ?_⟩
  apply primary_associated_eq ha hqp
  exact hassoc.symm.trans ((primaryNormalize_associated r).pow_pow (n := j))

lemma idealVonMangoldt_primary_nonprime_support {a : Eisenstein} (ha : primary a)
    (hprime : ¬ Prime a)
    (hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 2 ≤ j ∧ a = p ^ j := by
  obtain ⟨p,j,hp,hj,he⟩ := idealVonMangoldt_primary_support ha hΛ
  refine ⟨p,j,hp,?_,he⟩
  by_contra h
  have hje : j = 1 := by omega
  have hae : a = p := by simpa [hje] using he
  apply hprime
  rw [hae]
  exact hp.2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_primaryIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ primaryIdealBall Y ↔ primary (idealPrimaryGenerator ν) ∧ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha,hN⟩ := mem_primaryElementBall.mp ha
    rw [idealPrimaryGenerator_at_element ha,idealExponentOf_norm (primary_ne_zero ha)]
    exact ⟨ha,hN⟩
  · rintro ⟨hν,hN⟩
    exact Finset.mem_image.mpr ⟨idealPrimaryGenerator ν,
      mem_primaryElementBall.mpr ⟨hν,(idealPrimaryGenerator_norm ν).trans_le hN⟩,
      idealExponentOf_primaryGenerator ν⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-length convolutions of arbitrary primary elements. The divisor
bound absorbs the tuple multiplicity in any positive norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedPrimarySupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ a ∈ S i, primary a) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) : primary b := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  exact primary_finset_prod _ _ (fun i _ => hS i (f i) (Fintype.mem_piFinset.mp hf i))

/-- The tuple multiplicity is uniformly a small power even when each
factor has arbitrarily many distinct prime divisors. -/
theorem primary_tuple_fiber_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein),
      (∀ i, ∀ a ∈ S i, primary a) → ∀ Y : ℝ, 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      (((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card : ℝ) ≤ C*Y^ε := by
  let k : ℝ := Fintype.card ι
  let δ : ℝ := ε/(k+1)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ*k ≤ ε := by
    have h := div_mul_cancel₀ ε (show k+1 ≠ 0 by positivity)
    change δ*(k+1) = ε at h
    nlinarith
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hδ
  refine ⟨D^(Fintype.card ι),pow_pos hD _,?_⟩
  intro S hS Y hY b hb hbY
  have hb0 := primary_ne_zero (orderedPrimarySupport_primary S hS hb)
  have hsub : (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b) ⊆
      Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b)) := by
    intro f hf
    obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hfs i,?_⟩
    rw [← hfb]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have hcard (i : ι) : (((S i).filter (fun a => a ∣ b)).card : ℝ) ≤ D*Y^δ :=
    (hdiv (S i) (hS i) b hb0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg b) hbY hδ.le) hD.le)
  calc
    _ ≤ ((Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ∏ i, (((S i).filter (fun a => a ∣ b)).card : ℝ) := by
      rw [Fintype.card_piFinset,Nat.cast_prod]
    _ ≤ ∏ _i : ι, D*Y^δ := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
      (fun i _ => hcard i)
    _ = D^(Fintype.card ι)*Y^(δ*k) := by
      rw [Finset.prod_const,Finset.card_univ,mul_pow,← Real.rpow_mul_natCast (by linarith)]
    _ ≤ D^(Fintype.card ι)*Y^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY hδε) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogReplacement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact replacement of a prime indicator by von Mangoldt divided by log norm.
The discrepancy is bounded and is supported on actual higher primary prime powers. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_norm_gt_one {p : Eisenstein} (hp : Prime p) : 1 < norm p := by
  have hn := one_le_norm hp.ne_zero
  apply lt_of_le_of_ne hn
  intro he
  exact hp.not_isUnit (isUnit_of_norm_eq_one he.symm)

lemma normalizedVonMangoldt_at_prime {p : Eisenstein} (hp : Prime p) :
    normalizedVonMangoldt p = 1 := by
  rw [normalizedVonMangoldt,idealVonMangoldt_at_prime hp]
  exact div_self (Real.log_pos (prime_norm_gt_one hp)).ne'

lemma normalizedVonMangoldt_nonneg {a : Eisenstein} (ha : primary a) :
    0 ≤ normalizedVonMangoldt a :=
  div_nonneg (idealVonMangoldt_coeff_nonneg _)
    (Real.log_nonneg (one_le_norm (primary_ne_zero ha)))

lemma normalizedVonMangoldt_le_one {a : Eisenstein} (ha : primary a) :
    normalizedVonMangoldt a ≤ 1 := by
  have hlog : 0 ≤ Real.log (norm a) := Real.log_nonneg (one_le_norm (primary_ne_zero ha))
  have hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≤ Real.log (norm a) := by
    simpa only [idealExponentOf_norm (primary_ne_zero ha)] using
      idealVonMangoldt_coeff_le_logNorm (idealExponentOf a)
  by_cases hz : Real.log (norm a) = 0
  · simp only [normalizedVonMangoldt,hz,div_zero]
    norm_num
  · exact (div_le_one (lt_of_le_of_ne hlog (Ne.symm hz))).mpr hΛ

lemma primeLogCorrection_at_prime {p : Eisenstein} (hp : Prime p) :
    primeLogCorrection p = 0 := by
  simp only [primeLogCorrection,normalizedVonMangoldt_at_prime hp,primeIndicator,
    ite_eq_left hp,sub_self]

lemma primeLogCorrection_support {a : Eisenstein} (ha : primary a)
    (he : primeLogCorrection a ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 2 ≤ j ∧ a = p^j := by
  have hp : ¬ Prime a := fun hp => he (primeLogCorrection_at_prime hp)
  have hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0 := by
    intro hz
    apply he
    simp only [primeLogCorrection,primeIndicator,ite_eq_right hp,normalizedVonMangoldt,hz,
      zero_div,sub_self]
  exact idealVonMangoldt_primary_nonprime_support ha hp hΛ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogConvolution
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual error in replacing a convolution of prime indicators by
normalized von Mangoldt coefficients has sparse prime-power support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeLogConvolutionError_sum (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (b : Eisenstein) :
    primeLogConvolutionError S w b =
      ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b),
        ((∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
          ∏ i, (primeIndicator (f i):ℂ)*w i (f i)) := by
  unfold primeLogConvolutionError orderedConvolution
  rw [Finset.sum_sub_distrib]

lemma primeLogConvolutionError_support_of_norm_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {Y c : ℝ}
    (hS : ∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a)
    {b : Eisenstein} (hbY : norm b ≤ Y) (hb : primeLogConvolutionError S w b ≠ 0) :
    b ∈ largePrimePowerSupport Y c := by
  rw [primeLogConvolutionError_sum] at hb
  obtain ⟨f,hf,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hex : ∃ i, primeLogCorrection (f i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    have he : (∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i)) =
        ∏ i, (primeIndicator (f i):ℂ)*w i (f i) := by
      apply Finset.prod_congr rfl
      intro i _
      have hi : normalizedVonMangoldt (f i) = primeIndicator (f i) :=
        sub_eq_zero.mp (h i)
      rw [hi]
    exact sub_eq_zero.mpr he
  obtain ⟨i,hi⟩ := hex
  have hfi := hS i (f i) (Fintype.mem_piFinset.mp hfs i)
  obtain ⟨p,j,hp,hj,he⟩ := primeLogCorrection_support hfi.1 hi
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => primary_ne_zero (hS i (f i) (Fintype.mem_piFinset.mp hfs i)).1)
  refine Finset.mem_filter.mpr ⟨mem_nonzeroNormBall.mpr
    ⟨hbY,hfb ▸ hprod0⟩,p,j,hp,hj,?_,?_⟩
  · rw [← he]
    exact hfi.2
  · rw [← he,← hfb]
    exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)


lemma primeLog_factor_norm_le (w : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    {a : Eisenstein} (ha : primary a) (hw : ‖w a‖ ≤ M) :
    ‖(normalizedVonMangoldt a:ℂ)*w a‖ ≤ M ∧
    ‖(primeIndicator a:ℂ)*w a‖ ≤ M := by
  constructor
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (normalizedVonMangoldt_nonneg ha)]
    exact (mul_le_mul (normalizedVonMangoldt_le_one ha) hw (_root_.norm_nonneg _) zero_le_one).trans_eq
      (one_mul M)
  · by_cases hp : Prime a
    · simpa only [primeIndicator,ite_eq_left hp,Complex.ofReal_one,one_mul] using hw
    · simp only [primeIndicator,ite_eq_right hp,Complex.ofReal_zero,zero_mul,norm_zero]
      exact hM

/-- A divisor bound gives the genuine error coefficient a subpower amplitude. -/
theorem primeLogConvolutionError_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) → 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      ‖primeLogConvolutionError S w b‖ ≤ C*Y^ε*(∏ i, M i) := by
  obtain ⟨C,hC,hfiber⟩ := primary_tuple_fiber_small_power (ι := ι) hε
  refine ⟨2*C,by positivity,?_⟩
  intro S w M Y hS hM hw hY b hb hbY
  have hMp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have ht (f : ι → Eisenstein) (hf : f ∈ Fintype.piFinset S) :
      ‖(∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
        ∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ ≤ 2*∏ i, M i := by
    have hl (i : ι) := primeLog_factor_norm_le (w i) (hM i)
      (hS i (f i) (Fintype.mem_piFinset.mp hf i))
      (hw i (f i) (Fintype.mem_piFinset.mp hf i))
    have h1 : ‖∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i)‖ ≤ ∏ i, M i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _) (fun i _ => (hl i).1)
    have h2 : ‖∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ ≤ ∏ i, M i := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => _root_.norm_nonneg _) (fun i _ => (hl i).2)
    exact (norm_sub_le _ _).trans (by linarith)
  rw [primeLogConvolutionError_sum]
  calc
    _ ≤ ∑ f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b),
        ‖(∏ i, (normalizedVonMangoldt (f i):ℂ)*w i (f i))-
          ∏ i, (primeIndicator (f i):ℂ)*w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b), 2*∏ i, M i :=
      Finset.sum_le_sum (fun f hf => ht f (Finset.mem_filter.mp hf).1)
    _ = (((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card:ℝ)*(2*∏ i, M i) := by simp
    _ ≤ (C*Y^ε)*(2*∏ i, M i) :=
      mul_le_mul_of_nonneg_right (hfiber S hS Y hY b hb hbY) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact collection of the original independently weighted prime tuples,
with the individual support and the global norm cutoff both retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateSupport_lower (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y R : ℝ)
    (hW : ∀ i x, x < 1 → W i x = 0) (hX : ∀ i, 0 < X i)
    (hRX : ∀ i, R < X i) :
    ∀ i, ∀ n ∈ coordinateSupport W X Y i, primary n ∧ R < norm n := by
  intro i n hn
  obtain ⟨hn,hne⟩ := Finset.mem_filter.mp hn
  refine ⟨(mem_primaryElementBall.mp hn).1,(hRX i).trans_le ?_⟩
  have hlo : 1 ≤ norm n/X i := by
    by_contra h
    exact hne (hW i _ (lt_of_not_ge h))
  simpa only [one_mul] using (le_div_iff₀ (hX i)).mp hlo

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateFactor_bound (q : ι → Eisenstein) (hq : ∀ i, q i ≠ 0)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (M : ι → ℝ)
    (hM : ∀ i x, ‖W i x‖ ≤ M i) (i : ι) (n : Eisenstein) :
    ‖coordinateFactor q η t W X i n‖ ≤ M i := by
  unfold coordinateFactor
  rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
  exact (mul_le_of_le_one_right (_root_.norm_nonneg _)
    (residueChar_norm_le_one (hq i) (η i) _)).trans (hM i _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateDifference
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact difference between normalized von Mangoldt tuples and
original prime-indicator tuples on the global smooth cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coordinateProductCutoff_spec (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    coordinateProductCutoff W X Y ⊆ orderedConvolutionSupport (coordinateSupport W X Y) ∧
      ∀ b ∈ coordinateProductCutoff W X Y, norm b ≤ 2*Y :=
  ⟨Finset.filter_subset _ _,fun _ hb => (Finset.mem_filter.mp hb).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A power saving for the exact higher-prime-power replacement error.
Both the sparse support and the coefficient amplitude are proved. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeLogConvolutionError_cutoff_energy {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      (∑ b ∈ B, ‖primeLogConvolutionError S w b‖^2) ≤
        K*Y^(1-c/16)*(∏ i, M i)^2 := by
  obtain ⟨C,hC,hamp⟩ := primeLogConvolutionError_bound (ι := ι)
    (show 0 < c/32 by positivity)
  obtain ⟨D,hD,hcount⟩ := largePrimePowerSupport_card_bound
  refine ⟨D*C^2,by positivity,?_⟩
  intro S w M Y hY hM hS B hB hBY hw
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  let T := B.filter (fun b => primeLogConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largePrimePowerSupport Y c := fun b hb =>
    primeLogConvolutionError_support_of_norm_le S w hS
      (hBY b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ D*Y^(1-c/8) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y c hYp)
  have hsum : (∑ b ∈ T, ‖primeLogConvolutionError S w b‖^2) =
      ∑ b ∈ B, ‖primeLogConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hn
    have hz : primeLogConvolutionError S w b = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  rw [← hsum]
  have hMp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have he : Y^(1-c/8)*(Y^(c/32))^2 = Y^(1-c/16) := by
    rw [← Real.rpow_mul_natCast hYp.le,← Real.rpow_add hYp]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ∑ _b ∈ T, (C*Y^(c/32)*(∏ i, M i))^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have hbB := (Finset.mem_filter.mp hb).1
      have hbS := hB hbB
      have hbY : norm b ≤ Y := hBY b hbB
      exact pow_le_pow_left₀ (_root_.norm_nonneg _)
        (hamp S w M Y (fun i a ha => (hS i a ha).1) hM hw hY b hbS hbY) 2
    _ = (T.card:ℝ)*(C*Y^(c/32)*(∏ i, M i))^2 := by simp
    _ ≤ (D*Y^(1-c/8))*(C*Y^(c/32)*(∏ i, M i))^2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = (D*C^2)*(Y^(1-c/8)*(Y^(c/32))^2)*(∏ i, M i)^2 := by ring
    _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeLogCutoffMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime-log replacement moments on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem primeLogConvolution_first_shape_cutoff_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primary a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ (P Q : Finset Eisenstein),
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ Y^(1+c/256)) →
      (∀ q ∈ Q, primary q ∧ norm q ≤ Y^(c/256)) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ B, ‖χ b‖ ≤ 1) →
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ b ∈ B,
        (primeLogConvolutionError S w b*χ b)*mixedCubic p q b‖^2) ≤
        C*(∏ i, M i)^2*Y^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := first_shape_sparse_mixed_moment
    (show 0 < c/16 by positivity) (show c/16 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeLogConvolutionError_cutoff_energy (ι := ι) hc
  have h₁ : c/16/16 = c/256 := by ring
  have h₂ : c/16/2 = c/32 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS B hB hBY hw P Q hP hQ χ hχ
  have hH : ∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨primary_ne_zero (orderedPrimarySupport_primary S
      (fun i a ha => (hS i a ha).1) (hB hb)),?_⟩
    exact hBY b hb
  have hE : (∑ b ∈ B,
      ‖primeLogConvolutionError S w b*χ b‖^2) ≤
      (K*(∏ i, M i)^2)*Y^(1-c/16) :=
    ((coefficient_twist_energy_le B
      (primeLogConvolutionError S w) χ hχ).trans
      (henergy S w M Y hY hM hS B hB hBY hw)).trans_eq (by ring)
  exact (hbound Y (K*(∏ i, M i)^2) hY (by positivity) P Q
    B hP hQ hH (fun b => primeLogConvolutionError S w b*χ b)
    hE).trans_eq (by ring)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateErrors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prime-indicator replacement errors in the two exceptional regions. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_primeCoordinateError_moment_oai {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset Eisenstein,
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/256)) →
      (∑ a ∈ P, ‖primeCoordinateError a 1 q η t W X V Y‖^2) ≤
        C*(∏ i, M i)^2*(2*Y)^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primeLogConvolution_first_shape_cutoff_moment (ι := ι) hc hc₁
  refine ⟨C,hC,?_⟩
  intro q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS := coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX
  have hB := coordinateProductCutoff_spec W X Y
  have hQ : ∀ b ∈ ({1}:Finset Eisenstein), primary b ∧ norm b ≤ (2*Y)^(c/256) := by
    intro b hb
    have he : b = 1 := Finset.mem_singleton.mp hb
    subst b
    constructor
    · norm_num [primary]
    · simpa using Real.one_le_rpow (show 1 ≤ 2*Y by linarith) (show 0 ≤ c/256 by positivity)
  have hh := hbound (coordinateSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinateProductCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P {1} hP hQ
    (fun z => V (norm z/Y)) (fun z _ => hV _)
  simp only [Finset.sum_singleton] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  ring

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.first_primeCoordinateError_moment_oai.{u_1} := @OAI.CubicFirstMoment.first_primeCoordinateError_moment_oai.{u_1}
