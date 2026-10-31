-- Prove2me | solution 1 for OAI.CubicFirstMoment.outer_core_block_sieve
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:57:07.526535+00:00
-- url     : https://prove2.me/submissions/5d8b0acb-6778-4767-a63d-bb099d7f86be

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008
import Theorems.Thm_OAI_CubicFirstMoment_sieveExponent_four_thirds

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_SieveImprovement
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeFrequencyBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeSieveAssembly
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterSieveNumerical
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical minimization of the two cubic-sieve orientations for an
outer frequency block. Variables p and q are the cube roots of its
squarefree side lengths. -/
namespace CubicFirstMoment

lemma outer_sieve_polynomial_min {p q j N T : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hj : p*q^2 ≤ j) (hN : 0 ≤ N) (hT : 0 ≤ T) :
    min (q^3*(p^3+N+p^2*T)) (p^3*(q^3+N+q^2*T)) ≤
      (p*q^2)*(j^2+N+j*T) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hpq : 0 ≤ p*q^2 := mul_nonneg hp0 (sq_nonneg q)
  have hj0 : 0 ≤ j := hpq.trans hj
  have hq2 : q ≤ q^2 := by nlinarith
  have hq4 : q ≤ q^4 := hq2.trans (by nlinarith [sq_nonneg (q^2-1)])
  have hbase : p^2*q ≤ j^2 := by
    calc
      _ ≤ p^2*q^4 := mul_le_mul_of_nonneg_left hq4 (sq_nonneg p)
      _ = (p*q^2)^2 := by ring
      _ ≤ j^2 := pow_le_pow_left₀ hpq hj 2
  rcases le_total q p with hqp | hpq'
  · have hprod : p*q ≤ j := (mul_le_mul_of_nonneg_left hq2 hp0).trans hj
    have hmain := mul_le_mul_of_nonneg_left hbase hpq
    have hlinear : q^3*N ≤ (p*q^2)*N := by
      apply mul_le_mul_of_nonneg_right _ hN
      nlinarith [mul_le_mul_of_nonneg_right hqp (sq_nonneg q)]
    have hcross := mul_le_mul_of_nonneg_left hprod (mul_nonneg hpq hT)
    apply (min_le_left _ _).trans
    nlinarith
  · have hpq2 : p ≤ q^2 := hpq'.trans hq2
    have hprod : p^2 ≤ j := (by nlinarith [mul_le_mul_of_nonneg_left hpq2 hp0] : p^2 ≤ p*q^2).trans hj
    have hmain := mul_le_mul_of_nonneg_left hbase hpq
    have hlinear : p^3*N ≤ (p*q^2)*N := by
      apply mul_le_mul_of_nonneg_right _ hN
      nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hpq' 2) hp0]
    have hcross := mul_le_mul_of_nonneg_left hprod (mul_nonneg hpq hT)
    apply (min_le_right _ _).trans
    nlinarith

end CubicFirstMoment

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterSievePowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring norm scales in the outer sieve minimization. -/
noncomputable section
namespace CubicFirstMoment

lemma cube_root_cubed {x : ℝ} (hx : 0 ≤ x) : (x^(1/3:ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

lemma cube_root_squared {x : ℝ} (hx : 0 ≤ x) : (x^(1/3:ℝ))^2 = x^(2/3:ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

lemma outer_sieve_power_min {P Q J N : ℝ} (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hJ : P*Q^2 ≤ J) (hN : 0 ≤ N) :
    (J/(P*Q^2))^(1/3:ℝ)*
      min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))) ≤
        J+(J*N)^(2/3:ℝ)+J^(1/3:ℝ)*N := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hD : 0 < P*Q^2 := mul_pos (zero_lt_one.trans_le hP) (sq_pos_of_pos (zero_lt_one.trans_le hQ))
  have hJ0 : 0 < J := hD.trans_le hJ
  let p := P^(1/3:ℝ)
  let q := Q^(1/3:ℝ)
  let j := J^(1/3:ℝ)
  have hp : 1 ≤ p := Real.one_le_rpow hP (by norm_num)
  have hq : 1 ≤ q := Real.one_le_rpow hQ (by norm_num)
  have hp3 : p^3 = P := cube_root_cubed hP0
  have hq3 : q^3 = Q := cube_root_cubed hQ0
  have hj3 : j^3 = J := cube_root_cubed hJ0.le
  have hp2 : p^2 = P^(2/3:ℝ) := cube_root_squared hP0
  have hq2 : q^2 = Q^(2/3:ℝ) := cube_root_squared hQ0
  have hj2 : j^2 = J^(2/3:ℝ) := cube_root_squared hJ0.le
  have hroot : (P*Q^2)^(1/3:ℝ) = p*q^2 := by
    rw [Real.mul_rpow hP0 (sq_nonneg Q),← Real.rpow_pow_comm hQ0]
  have hj : p*q^2 ≤ j := by
    rw [← hroot]
    exact Real.rpow_le_rpow hD.le hJ (by norm_num)
  have hpoly := outer_sieve_polynomial_min hp hq hj hN
    (Real.rpow_nonneg hN (2/3:ℝ))
  have hmin : min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))) =
      min (q^3*(p^3+N+p^2*N^(2/3:ℝ)))
        (p^3*(q^3+N+q^2*N^(2/3:ℝ))) := by
    rw [hp3,hq3,hp2,hq2,Real.mul_rpow hP0 hN,Real.mul_rpow hQ0 hN]
  rw [hmin,Real.div_rpow hJ0.le hD.le,hroot]
  have hpq : p*q^2 ≠ 0 := ne_of_gt (mul_pos (zero_lt_one.trans_le hp)
    (sq_pos_of_pos (zero_lt_one.trans_le hq)))
  have hjn : (J*N)^(2/3:ℝ) = j^2*N^(2/3:ℝ) := by
    rw [Real.mul_rpow hJ0.le hN,hj2]
  calc
    _ ≤ j/(p*q^2)*((p*q^2)*(j^2+N+j*N^(2/3:ℝ))) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = J+(J*N)^(2/3:ℝ)+j*N := by
      rw [hjn]
      field_simp
      nlinarith [hj3]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterSieveDilation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorb fixed dyadic dilation and lattice counting into one constant
before minimizing the two outer-sieve orientations. -/
noncomputable section
namespace CubicFirstMoment

lemma sieve_doubled_bracket {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    2*M+N+(2*M*N)^(2/3:ℝ) ≤ 2*(M+N+(M*N)^(2/3:ℝ)) := by
  have htwo : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (2/3:ℝ) ≤ 1)
  have hp : (2*M*N)^(2/3:ℝ) ≤ 2*(M*N)^(2/3:ℝ) := by
    rw [mul_assoc,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hM hN)]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (mul_nonneg hM hN) _)
  linarith

lemma sieve_doubled_term {M N B A K ε : ℝ} (hM : 0 ≤ M) (hMB : M ≤ B)
    (hN : 0 ≤ N) (hA : 0 ≤ A) (_hK : 0 ≤ K) (hKA : K ≤ 36*A) (hε : 0 ≤ ε) :
    K*(2*M*N)^ε*(2*M+N+(2*M*N)^(2/3:ℝ)) ≤
      (72*(2*B*N)^ε)*(A*(M+N+(M*N)^(2/3:ℝ))) := by
  have hB0 : 0 ≤ B := hM.trans hMB
  have hbase : 0 ≤ 2*M*N := mul_nonneg (mul_nonneg (by norm_num) hM) hN
  have hp : (2*M*N)^ε ≤ (2*B*N)^ε := Real.rpow_le_rpow hbase
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB (by norm_num)) hN) hε
  have hKp := mul_le_mul hKA hp (Real.rpow_nonneg hbase ε) (by positivity : 0 ≤ 36*A)
  have hbr := sieve_doubled_bracket hM hN
  calc
    _ ≤ (36*A)*(2*B*N)^ε*(2*(M+N+(M*N)^(2/3:ℝ))) :=
      mul_le_mul hKp hbr (by positivity) (by positivity)
    _ = _ := by ring

lemma outer_dyadic_sieve_min {P Q B N S T ε : ℝ}
    (hP : 0 ≤ P) (hPB : P ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hN : 0 ≤ N) (hS : 0 ≤ S) (hSP : S ≤ 36*P)
    (hT : 0 ≤ T) (hTQ : T ≤ 36*Q) (hε : 0 ≤ ε) :
    min (T*(2*P*N)^ε*(2*P+N+(2*P*N)^(2/3:ℝ)))
      (S*(2*Q*N)^ε*(2*Q+N+(2*Q*N)^(2/3:ℝ))) ≤
      (72*(2*B*N)^ε)*
        min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))) := by
  have hB0 : 0 ≤ B := hP.trans hPB
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 72*(2*B*N)^ε)]
  exact min_le_min (sieve_doubled_term hP hPB hN hQ hT hTQ hε)
    (sieve_doubled_term hQ hQB hN hP hS hSP hε)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_OuterCoreBlock
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The outer cubic sieve on one actual frequency core block. This is
valid for arbitrary squarefree coefficients, hence for the shortened
common-divisor rows. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem outer_core_block_sieve_oai {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ) (i j : ℕ),
      0 ≤ B → 1 ≤ N → coreDyadicConductor i j ≤ B →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      H ⊆ coreDyadicBlock B i j → ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  obtain ⟨C₀,hC₀,hbound⟩ := residualFrequency_sieve_bound ε hε
  let R := nonzeroNormBall 729
  let C := (R.card:ℝ)*18*C₀*72
  refine ⟨C+1,by dsimp [C]; positivity,?_⟩
  intro S H B N i j hB hN hDB hS hH β
  let P : ℝ := 2^i
  let Q : ℝ := 2^j
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hQ : 1 ≤ Q := one_le_pow₀ (by norm_num)
  have hP0 := zero_le_one.trans hP
  have hQ0 := zero_le_one.trans hQ
  have hPQ : P*Q^2 ≤ B := hDB
  have hPB : P ≤ B := (le_mul_of_one_le_right hP0 (one_le_pow₀ hQ)).trans hPQ
  have hQB : Q ≤ B := (by nlinarith [sq_nonneg (Q-1),mul_le_mul_of_nonneg_right hP (sq_nonneg Q)] : Q ≤ P*Q^2).trans hPQ
  have hp (n : Eisenstein) (hn : n ∈ squarefreePrimaryDyad i) :
      primary n ∧ Squarefree n ∧ norm n ≤ 2*P := by
    have hh := squarefreePrimaryDyad_gramDyad hn
    exact ⟨hh.1,hh.2.1,hh.2.2.2.le⟩
  have hq (n : Eisenstein) (hn : n ∈ squarefreePrimaryDyad j) :
      primary n ∧ Squarefree n ∧ norm n ≤ 2*Q := by
    have hh := squarefreePrimaryDyad_gramDyad hn
    exact ⟨hh.1,hh.2.1,hh.2.2.2.le⟩
  have hpCard : ((squarefreePrimaryDyad i).card:ℝ) ≤ 36*P := by
    have hh := primary_support_card_le (squarefreePrimaryDyad i) (by positivity : 0 ≤ 2*P)
      (fun n hn => ⟨(hp n hn).1,(hp n hn).2.2⟩)
    linarith
  have hqCard : ((squarefreePrimaryDyad j).card:ℝ) ≤ 36*Q := by
    have hh := primary_support_card_le (squarefreePrimaryDyad j) (by positivity : 0 ≤ 2*Q)
      (fun n hn => ⟨(hq n hn).1,(hq n hn).2.2⟩)
    linarith
  have hcCard : ((coreDyadicCubeFactors B i j).card:ℝ) ≤
      18*(B/(P*Q^2))^(1/3:ℝ) :=
    nonzeroNormBall_card_le (Real.rpow_nonneg (div_nonneg hB (coreDyadicConductor_pos i j).le) _)
  have hh := (frequency_subset_mass_le H _ S
    (hH.trans (coprimeResidualSupport_subset R (coreDyadicCubeFactors B i j)
      (squarefreePrimaryDyad i) (squarefreePrimaryDyad j))) β).trans
    (hbound S R (squarefreePrimaryDyad i) (squarefreePrimaryDyad j)
      (coreDyadicCubeFactors B i j) N (2*P) (2*Q) hN (by linarith) (by linarith) hS hp hq β)
  have hmin := outer_dyadic_sieve_min hP0 hPB hQ0 hQB (zero_le_one.trans hN)
    (Nat.cast_nonneg (squarefreePrimaryDyad i).card) hpCard
    (Nat.cast_nonneg (squarefreePrimaryDyad j).card) hqCard hε.le
  have houter := outer_sieve_power_min hP hQ hPQ (zero_le_one.trans hN)
  have hE : 0 ≤ ∑ n ∈ S, ‖β n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ (R.card:ℝ)*(18*(B/(P*Q^2))^(1/3:ℝ))*C₀*
        ((72*(2*B*N)^ε)*
          min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))))*
        ∑ n ∈ S, ‖β n‖^2 := by
      apply hh.trans
      gcongr
    _ = C*(2*B*N)^ε*((B/(P*Q^2))^(1/3:ℝ)*
        min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))))*
        ∑ n ∈ S, ‖β n‖^2 := by dsimp only [C]; ring
    _ ≤ C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
        ∑ n ∈ S, ‖β n‖^2 := by gcongr
    _ ≤ _ := by gcongr; linarith

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.outer_core_block_sieve_oai := @OAI.CubicFirstMoment.outer_core_block_sieve_oai
