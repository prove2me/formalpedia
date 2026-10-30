-- Prove2me | solution 1 for OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:29:37.890038+00:00
-- url     : https://prove2.me/submissions/dd83deb2-b15e-4ffa-b75b-00d58dfb773c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A010
import Definitions.Def_OAIQ096A011
import Theorems.Thm_OAI_CubicFirstMoment_sieveExponent_four_thirds

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LargeSquareSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient bounds for a bounded number of ordered prime factors. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every prime in another tuple with the same product occurs in the
reference tuple. This includes repeated primes. -/
lemma prime_tuple_range_subset (f g : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hg : ∀ i, primaryPrime (g i))
    (hprod : (∏ i, g i) = ∏ i, f i) (i : ι) :
    g i ∈ Finset.univ.image f := by
  have hd : g i ∣ ∏ j, f j := hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  obtain ⟨j,_,hj⟩ := ((hg i).2.dvd_finsetProd_iff f).mp hd
  have he : g i = f j := primary_associated_eq (hg i).1 (hf j).1
    (((hg i).2.dvd_prime_iff_associated (hf j).2).mp hj)
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩

/-- The deliberately generous `k^k` bound avoids ordering conventions and
is uniform in the norm and in all independent supports. -/
theorem prime_tuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (b : Eisenstein) :
    ((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card ≤
      (Fintype.card ι)^(Fintype.card ι) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  by_cases ht : T.Nonempty
  · obtain ⟨f,hf⟩ := ht
    have hfs := (Finset.mem_filter.mp hf).1
    have hfb := (Finset.mem_filter.mp hf).2
    have hprime : ∀ i, primaryPrime (f i) :=
      fun i => hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)
    have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.univ.image f) := by
      intro g hg
      obtain ⟨hgs,hgb⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      exact prime_tuple_range_subset f g hprime
        (fun i => hS i (g i) ((Fintype.mem_piFinset.mp hgs) i)) (hgb.trans hfb.symm)
    calc
      T.card ≤ (Fintype.piFinset (fun _ : ι => Finset.univ.image f)).card :=
        Finset.card_le_card hsub
      _ = ((Finset.univ.image f).card)^(Fintype.card ι) := by
        simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by
        simpa using (Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))) _
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ _
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- The coefficient bound depends only on the number of prime factors
and on their separate weight bounds, including for nonsquarefree products. -/
theorem orderedConvolution_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  have hprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  unfold orderedConvolution
  calc
    _ ≤ ∑ f ∈ T, ‖∏ i, w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ T, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _)
        (fun i _ => hw i (f i) ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1) i))
    _ = (T.card:ℝ)*(∏ i, M i) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (prime_tuple_fiber_card S hS b)) hprod

/-- Removing nonsquarefree products never enlarges a coefficient; its
error also obeys the same uniform coefficient bound. -/
theorem convolutionError_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b-squarefreeConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hs : Squarefree b
  · simp only [squarefreeConvolution,ite_eq_left hs,sub_self,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  · simpa only [squarefreeConvolution,ite_eq_right hs,sub_zero] using
      orderedConvolution_norm_bound S w M hS hM hw b

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FirstShapeErrorMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeCoordinateCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
lemma coordinateSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ n ∈ coordinateSupport W X Y i, primary n := by
  intro i n hn
  exact (mem_primaryElementBall.mp (Finset.mem_filter.mp hn).1).1

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeIndicatorCollection
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting the indicator convolution to genuine primary primes,
followed by the exact squarefree discrepancy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_primary (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i, primaryPrime p := by
  intro i p hp
  exact ⟨coordinateSupport_primary W X Y i p (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

lemma coordinatePrimeCutoff_spec (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    coordinatePrimeCutoff W X Y ⊆ orderedConvolutionSupport (coordinatePrimeSupport W X Y) ∧
      ∀ b ∈ coordinatePrimeCutoff W X Y, norm b ≤ 2*Y :=
  ⟨Finset.filter_subset _ _,fun _ hb => (Finset.mem_filter.mp hb).2⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RepeatedPrimeCutoffEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated-prime energy on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma convolutionError_mem_largeSquareSupport_of_norm
    (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ) (Y D : ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p)
    {b : Eisenstein} (hbY : norm b ≤ Y) (hb : squarefreeConvolutionError S w b ≠ 0) :
    b ∈ largeSquareSupport Y D := by
  have hns : ¬Squarefree b := by
    intro hs
    simp [squarefreeConvolutionError,squarefreeConvolution,hs] at hb
  have ho : orderedConvolution S w b ≠ 0 := by
    simpa only [squarefreeConvolutionError,squarefreeConvolution,ite_eq_right hns,sub_zero] using hb
  obtain ⟨f,hf,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  have hprime : ∀ i, primaryPrime (f i) :=
    fun i => (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).1
  have hnot : ¬Function.Injective f := by
    intro hi
    exact hns (hfb ▸ (squarefree_prime_tuple_iff f hprime).mpr hi)
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hnot
  have hdvd : (f i)^2 ∣ ∏ k, f k := by
    have h := Finset.prod_dvd_prod_of_subset ({i,j}:Finset ι) Finset.univ f
      (Finset.subset_univ _)
    simpa [hne,hij,pow_two] using h
  have hprod0 : (∏ i, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hprime i).2.ne_zero)
  apply Finset.mem_filter.mpr
  refine ⟨mem_nonzeroNormBall.mpr ⟨?_,?_⟩,f i,?_,?_⟩
  · exact hbY
  · exact hfb ▸ hprod0
  · exact (hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)).2
  · exact hfb ▸ hdvd

private theorem convolutionError_cutoff_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (Y D E : ℝ),
      0 ≤ Y → 0 < D → 0 ≤ E →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ D < norm p) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ b ∈ B, ‖squarefreeConvolutionError S w b‖ ≤ E) →
      (∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y*D^(-(1/2:ℝ))*E^2 := by
  obtain ⟨C,hC,hcount⟩ := largeSquareSupport_card_bound
  refine ⟨C,hC,?_⟩
  intro S w Y D E hY hD hE hS B hB hBY hbound
  let T := B.filter (fun b => squarefreeConvolutionError S w b ≠ 0)
  have hsub : T ⊆ largeSquareSupport Y D := by
    intro b hb
    exact convolutionError_mem_largeSquareSupport_of_norm S w Y D hS
      (hBY b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have hcard : (T.card:ℝ) ≤ C*Y*D^(-(1/2:ℝ)) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount Y D hY hD)
  have heq : (∑ b ∈ T, ‖squarefreeConvolutionError S w b‖^2) =
      ∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnot
    have hz : squarefreeConvolutionError S w b = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hb,hn⟩)
    simp [hz]
  rw [← heq]
  calc
    _ ≤ ∑ _b ∈ T, E^2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hbound b (Finset.mem_filter.mp hb).1) 2
    _ = (T.card:ℝ)*E^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg E)

theorem primeConvolutionError_cutoff_power_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y c : ℝ),
      0 < Y → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ p ∈ S i, primaryPrime p ∧ Y^c < norm p) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i) →
      (∑ b ∈ B, ‖squarefreeConvolutionError S w b‖^2) ≤
        C*Y^(1-c/2)*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  obtain ⟨C,hC,hbound⟩ := convolutionError_cutoff_energy_bound (ι := ι)
  refine ⟨C,hC,?_⟩
  intro S w M Y c hY hM hS B hB hBY hw
  have hA : 0 ≤ ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))
  have hh := hbound S w Y (Y^c) _ hY.le (Real.rpow_pos_of_pos hY _) hA
    hS B hB hBY (fun b _ => convolutionError_norm_bound S w M
      (fun i p hp => (hS i p hp).1) hM hw b)
  have he : C*Y*(Y^c)^(-(1/2:ℝ)) = C*Y^(1-c/2) := by
    rw [← Real.rpow_mul hY.le]
    nth_rw 1 [← Real.rpow_one Y]
    rw [mul_assoc,← Real.rpow_add hY]
    congr 2
    ring
  simpa only [he] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RepeatedPrimeCutoffMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The repeated-prime replacement moments on the actual global norm cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem repeatedPrime_first_shape_cutoff_moment {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ) (Y : ℝ), 1 ≤ Y →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, primaryPrime a ∧ Y^c < norm a) →
      ∀ B : Finset Eisenstein, B ⊆ orderedConvolutionSupport S →
      (∀ b ∈ B, norm b ≤ Y) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ (P Q : Finset Eisenstein),
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ Y^(1+c/32)) →
      (∀ q ∈ Q, primary q ∧ norm q ≤ Y^(c/32)) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ B, ‖χ b‖ ≤ 1) →
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ b ∈ B,
        (squarefreeConvolutionError S w b*χ b)*mixedCubic p q b‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*Y^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := first_shape_sparse_mixed_moment
    (show 0 < c/2 by positivity) (show c/2 ≤ 1 by linarith)
  obtain ⟨K,hK,henergy⟩ := primeConvolutionError_cutoff_power_energy (ι := ι)
  have h₁ : c/2/16 = c/32 := by ring
  have h₂ : c/2/2 = c/4 := by ring
  simp only [h₁,h₂] at hbound
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro S w M Y hY hM hS B hB hBY hw P Q hP hQ χ hχ
  have hH : ∀ b ∈ B, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨primary_ne_zero (orderedPrimarySupport_primary S
      (fun i a ha => (hS i a ha).1.1) (hB hb)),?_⟩
    exact hBY b hb
  have hE : (∑ b ∈ B,
      ‖squarefreeConvolutionError S w b*χ b‖^2) ≤
      (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2)*Y^(1-c/2) :=
    ((coefficient_twist_energy_le B
      (squarefreeConvolutionError S w) χ hχ).trans
      (henergy S w M Y c (by linarith) hM hS B hB hBY hw)).trans_eq (by ring)
  exact (hbound Y (K*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2) hY (by positivity) P Q
    B hP hQ hH (fun b => squarefreeConvolutionError S w b*χ b)
    hE).trans_eq (by ring)


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSquarefreeCoordinateErrors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual angular replacement errors obey the unchanged sparse
moment estimates; theta is included in the bounded outer coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_angular_squarefreeCoordinateError_moment_oai {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℤ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (W : ι → ℝ → ℂ) (M X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ), 1 ≤ Y →
      (∀ i, q i ≠ 0) → (∀ i, 0 ≤ M i) → (∀ i x, ‖W i x‖ ≤ M i) →
      (∀ i x, x < 1 → W i x = 0) → (∀ i, (2*Y)^c < X i) →
      (∀ x, ‖V x‖ ≤ 1) → ∀ P : Finset Eisenstein,
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/32)) →
      (∑ a ∈ P, ‖angularSquarefreeCoordinateError ℓ a 1 q η t W X V Y‖^2) ≤
        C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2*(2*Y)^(7/3-c/4) := by
  obtain ⟨C,hC,hbound⟩ := repeatedPrime_first_shape_cutoff_moment (ι := ι) hc hc₁
  refine ⟨C,hC,?_⟩
  intro ℓ q η t W M X V Y hY hq hM hW hWlo hX hV P hP
  have hYp : 0 < 2*Y := by linarith
  have hXpos : ∀ i, 0 < X i := fun i => (Real.rpow_pos_of_pos hYp c).trans (hX i)
  have hS : ∀ i, ∀ p ∈ coordinatePrimeSupport W X Y i,
      primaryPrime p ∧ (2*Y)^c < norm p := by
    intro i p hp
    exact ⟨coordinatePrimeSupport_primary W X Y i p hp,
      (coordinateSupport_lower W X Y ((2*Y)^c) hWlo hXpos hX i p
        (Finset.mem_filter.mp hp).1).2⟩
  have hB := coordinatePrimeCutoff_spec W X Y
  have hQ : ∀ b ∈ ({1}:Finset Eisenstein), primary b ∧ norm b ≤ (2*Y)^(c/32) := by
    intro b hb
    have he : b = 1 := Finset.mem_singleton.mp hb
    subst b
    constructor
    · norm_num [primary]
    · simpa using Real.one_le_rpow (show 1 ≤ 2*Y by linarith) (show 0 ≤ c/32 by positivity)
  have hχ (z : Eisenstein) (hz : z ∈ coordinatePrimeCutoff W X Y) :
      ‖theta ℓ z*V (norm z/Y)‖ ≤ 1 := by
    have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Y)
        (fun i p hp => (coordinatePrimeSupport_primary W X Y i p hp).1) (hB.1 hz)
    rw [norm_mul,norm_theta (primary_ne_zero hp) ℓ,one_mul]
    exact hV _
  have hh := hbound (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) M (2*Y)
    (by linarith) hM hS (coordinatePrimeCutoff W X Y) hB.1 hB.2
    (fun i n _ => coordinateFactor_bound q hq η t W X M hW i n) P {1} hP hQ
    (fun z => theta ℓ z*V (norm z/Y)) hχ
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

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment_oai.{u_1} := @OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment_oai.{u_1}
