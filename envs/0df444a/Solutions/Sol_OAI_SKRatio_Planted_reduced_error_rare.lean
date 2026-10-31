-- Prove2me | solution 1 for OAI.SKRatio.Planted.reduced_error_rare
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:34:20.553748+00:00
-- url     : https://prove2.me/submissions/2a45168e-3004-49d4-bd6d-b950d30fbe98

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S016
import Theorems.Thm_OAI_SKRatio_Planted_augmented_norm_rare

section
-- module Solutions.OAIQ024_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PlusSpin
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus

open Real Set

lemma hasDerivAt_tanh (y : ℝ) : HasDerivAt tanh (1 - tanh y ^ 2) y := by
  convert! (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (cosh_pos y).ne' using 1
  · ext x
    exact tanh_eq_sinh_div_cosh x
  · rw [tanh_eq_sinh_div_cosh]
    field_simp

lemma tanh_lipschitz_abs (x y : ℝ) : |tanh x-tanh y| ≤ |x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_tanh z).hasDerivWithinAt)
    (C := 1) (fun z _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one z).le)]
      linarith [sq_nonneg (tanh z)]) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma sum_transpose_triangle {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => j < i), F i j) =
      pairSum (fun i j => F j i) := by
  simp only [pairSum, Finset.sum_filter]
  rw [Finset.sum_comm]

lemma sum_offdiag_pairs {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, F i j) = pairSum (fun i j => F i j + F j i) := by
  have hsplit (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, F i j) =
        (∑ j ∈ Finset.univ.filter (fun j => i < j), F i j) +
        ∑ j ∈ Finset.univ.filter (fun j => j < i), F i j := by
    have heq : Finset.univ.erase i = (Finset.univ.filter (fun j => i < j)) ∪
        (Finset.univ.filter (fun j => j < i)) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
        Finset.mem_filter, true_and]
      omega
    have hdis : Disjoint (Finset.univ.filter (fun j => i < j))
        (Finset.univ.filter (fun j => j < i)) := by
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj hj'; exact (lt_asymm hj hj')
    rw [heq, Finset.sum_union hdis]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, sum_transpose_triangle]
  simp only [pairSum, Finset.sum_add_distrib]

lemma pairSum_add {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    pairSum (fun i j => F i j + G i j) = pairSum F + pairSum G := by
  simp only [pairSum, Finset.sum_add_distrib]

end SKRatio.Calculus
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_GradientMoments
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma row_squares_le_opNorm {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j = J j i) {K : ℝ}
    (hK : 0 ≤ K)
    (hop : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) (i : Fin n) :
    ∑ j, J i j ^ 2 ≤ K^2 := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J).le_opNorm e
  rw [he,mul_one] at h
  have hsq := sq_le_sq₀ (norm_nonneg _) hK |>.mpr (h.trans hop)
  rw [EuclideanSpace.real_norm_sq_eq] at hsq
  have happly (j : Fin n) :
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J e).ofLp j = J i j := by
    change (∑ coordinate, J j coordinate * e.ofLp coordinate) = J i j
    simp only [e, EuclideanSpace.single, PiLp.single_apply,
      mul_ite, mul_one, mul_zero]
    simp [hsymm j i]
  simpa only [happly] using hsq

end SKRatio.Calculus

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RandomMatrixNet
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
namespace SKRatio.MatrixNet

lemma separated_card_le {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1/4:ℝ) < dist x y) :
    (s.card : ℝ) ≤ (9:ℝ)^n := by
  have hd : Set.PairwiseDisjoint (↑s) (fun x : EuclideanSpace ℝ (Fin n) => ball x (1/8)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (by linarith [hs x hx y hy hxy])
  have hsub : (⋃ x ∈ s, ball x (1/8)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (9/8) := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp hy
    have h := dist_triangle y x (0 : EuclideanSpace ℝ (Fin n))
    simp only [mem_ball, dist_zero_right] at hy h ⊢
    linarith [hb x hx]
  have hm := measureReal_mono (μ := volume) hsub measure_ball_ne_top
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)] at hm
  have hvol (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
      volume.real (ball x r) = r ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    simp only [measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _), finrank_euclideanSpace,
      Fintype.card_fin]
  simp only [hvol _ _ (by norm_num : (0:ℝ) < 1/8),
    hvol _ _ (by norm_num : (0:ℝ) < 9/8), Finset.sum_const, nsmul_eq_mul] at hm
  have hp : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    exact ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  have hh : (s.card : ℝ) * (1/8:ℝ)^n ≤ (9/8:ℝ)^n :=
    (mul_le_mul_iff_left₀ hp).mp (by simpa only [mul_assoc] using hm)
  have he : (9/8:ℝ)^n = (9:ℝ)^n * (1/8:ℝ)^n := by rw [← mul_pow]; congr 1; norm_num
  rw [he] at hh
  exact (mul_le_mul_iff_left₀ (show 0 < (1/8:ℝ)^n by positivity)).mp
    (by simpa only [mul_comm] using hh)

lemma unit_ball_net (n : ℕ) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/4) ∧
      (s.card : ℝ) ≤ (9:ℝ)^n := by
  classical
  let A := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  obtain ⟨C, _, hCf, hC⟩ := exists_finite_isCover_of_isCompact
    (by norm_num : (1/8 : ℝ≥0) ≠ 0) (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hpack : packingNumber (1/4 : ℝ≥0) A ≠ ⊤ := by
    have hle := (packingNumber_two_mul_le_externalCoveringNumber (1/8 : ℝ≥0) A).trans
      hC.externalCoveringNumber_le_encard
    norm_num only [show (2:ℝ≥0)*(1/8) = 1/4 by norm_num] at hle
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCf) hle

  let D := maximalSeparatedSet (1/4 : ℝ≥0) A
  have hDf : D.Finite := Set.encard_ne_top_iff.mp (by
    rw [show D = maximalSeparatedSet (1/4 : ℝ≥0) A from rfl, encard_maximalSeparatedSet hpack]
    exact hpack)
  refine ⟨hDf.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have h := maximalSeparatedSet_subset (ε := (1/4 : ℝ≥0)) (A := A) (hDf.mem_toFinset.mp hx)
    simpa only [A, mem_closedBall, dist_zero_right] using h
  · intro x hx
    have hxA : x ∈ A := by simpa only [A, mem_closedBall, dist_zero_right] using hx
    obtain ⟨y, hy, hdist⟩ := isCover_maximalSeparatedSet hpack hxA
    refine ⟨y, hDf.mem_toFinset.mpr hy, ?_⟩
    change edist x y ≤ ((1/4 : ℝ≥0) : ℝ≥0∞) at hdist
    have h := ENNReal.toReal_mono (by norm_num : ((1/4 : ℝ≥0) : ℝ≥0∞) ≠ ⊤) hdist
    simpa only [edist_dist, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist x y),
      ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h
  · apply separated_card_le
    · intro x hx
      have h := maximalSeparatedSet_subset (ε := (1/4 : ℝ≥0)) (A := A) (hDf.mem_toFinset.mp hx)
      simpa only [A, mem_closedBall, dist_zero_right] using h
    · intro x hx y hy hxy
      have h := isSeparated_maximalSeparatedSet (ε := (1/4 : ℝ≥0)) (A := A)
        (hDf.mem_toFinset.mp hx) (hDf.mem_toFinset.mp hy) hxy
      simpa only [edist_dist, ENNReal.coe_lt_ofReal, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_ofNat] using h

lemma opNorm_le_of_net {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/4)
    (M : ℝ) (hM : 0 ≤ M)
    (hnet : ∀ x ∈ s, ∀ y ∈ s, |inner (𝕜 := ℝ) (A x) y| ≤ M) : ‖A‖ ≤ 2*M := by
  have hh : ‖A‖ ≤ M + ‖A‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨a, ha, hxa⟩ := hcover x hx.le
    obtain ⟨b, hb', hyb⟩ := hcover y hy.le
    have hxan : ‖x-a‖ ≤ 1/4 := by simpa only [dist_eq_norm] using hxa
    have hybn : ‖y-b‖ ≤ 1/4 := by simpa only [dist_eq_norm] using hyb
    have h₁ : |inner (𝕜 := ℝ) (A (x-a)) y| ≤ ‖A‖/4 := by
      calc
        _ ≤ ‖A (x-a)‖ * ‖y‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖x-a‖) * ‖y‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖A‖/4 := by rw [hy, mul_one]; nlinarith [norm_nonneg A]
    have h₂ : |inner (𝕜 := ℝ) (A a) (y-b)| ≤ ‖A‖/4 := by
      calc
        _ ≤ ‖A a‖ * ‖y-b‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖a‖) * ‖y-b‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖A‖ * (1:ℝ) * (1/4) := mul_le_mul
          (mul_le_mul_of_nonneg_left (hb a ha) (norm_nonneg A)) hybn (norm_nonneg _) (by positivity)
        _ = ‖A‖/4 := by ring
    have he : inner (𝕜 := ℝ) (A x) y = inner (𝕜 := ℝ) (A (x-a)) y +
        inner (𝕜 := ℝ) (A a) (y-b) + inner (𝕜 := ℝ) (A a) b := by
      simp only [map_sub, inner_sub_left, inner_sub_right]; ring
    change inner (𝕜 := ℝ) (A x) y ≤ M + ‖A‖/2
    rw [he]
    have hh := hnet a ha b hb'
    linarith [le_abs_self (inner (𝕜 := ℝ) (A (x-a)) y),
      le_abs_self (inner (𝕜 := ℝ) (A a) (y-b)), le_abs_self (inner (𝕜 := ℝ) (A a) b)]
  linarith

lemma opNorm_tail_of_bilinear {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (A : Ω → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {u : ℝ} (hu : 0 ≤ u) (P : ℝ≥0∞)
    (h : ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      μ {ω | u ≤ |inner (𝕜 := ℝ) (A ω x) y|} ≤ P) :
    μ {ω | 2*u < ‖A ω‖} ≤ (81:ℝ≥0∞)^n*P := by
  classical
  obtain ⟨s,hb,hc,hs⟩ := unit_ball_net n
  let E (x y : EuclideanSpace ℝ (Fin n)) : Set Ω :=
    {ω | u ≤ |inner (𝕜 := ℝ) (A ω x) y|}
  have hsub : {ω | 2*u < ‖A ω‖} ⊆ ⋃ x ∈ s, ⋃ y ∈ s, E x y := by
    intro ω hω
    by_contra hn
    have hnet : ∀ x ∈ s, ∀ y ∈ s, |inner (𝕜 := ℝ) (A ω x) y| ≤ u := by
      intro x hx y hy
      have he : ω ∉ E x y := fun hh => hn
        (mem_iUnion₂.mpr ⟨x,hx,mem_iUnion₂.mpr ⟨y,hy,hh⟩⟩)
      exact (not_le.mp he).le
    exact not_lt_of_ge (opNorm_le_of_net (A ω) s hb hc u hu hnet) hω
  have hs2 : (s.card:ℝ)^2 ≤ (81:ℝ)^n := by
    calc
      _ ≤ ((9:ℝ)^n)^2 := pow_le_pow_left₀ (by positivity) hs 2
      _ = _ := by rw [←pow_mul,mul_comm n 2,pow_mul]; norm_num
  have hsE : (s.card : ℝ≥0∞)^2 ≤ (81:ℝ≥0∞)^n := by
    simpa only [ENNReal.ofReal_pow (Nat.cast_nonneg s.card),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 81),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hs2
  calc
    _ ≤ μ (⋃ x ∈ s, ⋃ y ∈ s, E x y) := measure_mono hsub
    _ ≤ ∑ x ∈ s, ∑ y ∈ s, μ (E x y) :=
      (measure_biUnion_finset_le s _).trans
        (Finset.sum_le_sum (fun x _ => measure_biUnion_finset_le s (E x)))
    _ ≤ ∑ _x ∈ s, ∑ _y ∈ s, P := Finset.sum_le_sum
      (fun x hx => Finset.sum_le_sum (fun y hy => h x y (hb x hx) (hb y hy)))
    _ = (s.card:ℝ≥0∞)^2*P := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul' hsE le_rfl

lemma matrix_opNorm_le_schur {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i, ∑ j, |A i j| ≤ R) (hc : ∀ j, ∑ i, |A i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hR
  intro x y hx hy
  change inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x) y ≤ R
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * ∑ j, A i j*x j) ≤ R
  simp only [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, |A i j| * ((y i)^2 + (x j)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hab : 2*|y i| *|x j| ≤ (y i)^2+(x j)^2 := by
        nlinarith [sq_nonneg (|y i|-|x j|), sq_abs (y i), sq_abs (x j)]
      have hp := mul_le_mul_of_nonneg_left hab (abs_nonneg (A i j))
      have hh : y i*(A i j*x j) ≤ |y i| *|A i j| *|x j| := by
        simpa only [abs_mul, mul_assoc] using le_abs_self (y i*(A i j*x j))
      nlinarith
    _ = ((∑ i, (y i)^2 * ∑ j, |A i j|) + ∑ j, (x j)^2 * ∑ i, |A i j|)/2 := by
      simp only [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [Finset.sum_comm (f := fun i j => |A i j| * (x j)^2)]
      simp only [← Finset.sum_mul]
      congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ ≤ ((∑ i, (y i)^2 * R) + ∑ j, (x j)^2*R)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)))
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i) (sq_nonneg _)))
    _ = R := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq,
        ← EuclideanSpace.real_norm_sq_eq, hx, hy]
      ring

lemma matrix_diagonal_opNorm_le {n : ℕ} (d : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hd : ∀ i, |d i| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal d)‖ ≤ R := by
  apply matrix_opNorm_le_schur _ R hR
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_CompactMatrixMasks
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Set Metric
namespace SKRatio.MatrixNet
attribute [local instance] Classical.propDecidable

lemma masked_matrix_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s t : Fin n → Prop) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (fun i j => if s i ∧ t j then A i j else 0)‖ ≤
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := by
  let D (s : Fin n → Prop) : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => if s i then 1 else 0)
  have hde (s : Fin n → Prop) :
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (D s)‖ ≤ 1 := by
    apply matrix_diagonal_opNorm_le _ 1 zero_le_one
    intro i
    split_ifs <;> norm_num
  have he : (fun i j => if s i ∧ t j then A i j else 0) = D s*A*D t := by
    ext i j
    simp only [D,Matrix.diagonal_mul,Matrix.mul_diagonal]
    split_ifs <;> simp_all
  rw [he,map_mul,map_mul]
  calc
    _ ≤ (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (D s)‖*
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖)*
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (D t)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hde s) (norm_nonneg _)) (hde t)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma bin_kernel_decomposition {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → κ) (G : κ → κ → ℝ) :
    Matrix.of (fun i j => A i j*G (b i) (b j)) =
      ∑ a : κ, ∑ c : κ, G a c • Matrix.of (fun i j => if b i=a ∧ b j=c then A i j else 0) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul]
  simp only [mul_ite,mul_zero, ite_and,
    Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true, if_true]
  ring

lemma euclideanCLM_smul {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (a • A) =
      a • Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A := by
  exact map_smul (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) a A

lemma masked_smul_norm_le {n : ℕ} (a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s t : Fin n → Prop) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (a • Matrix.of (fun i j => if s i ∧ t j then A i j else 0))‖ ≤
      |a| * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := by
  rw [euclideanCLM_smul,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (masked_matrix_norm_le A s t) (abs_nonneg a)

lemma bin_kernel_norm_le {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → κ) (G : κ → κ → ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.of (fun i j => A i j*G (b i) (b j)))‖ ≤
      (∑ a : κ, ∑ c : κ, |G a c|) * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
  let P (a c : κ) : Matrix (Fin n) (Fin n) ℝ :=
    G a c • Matrix.of (fun i j => if b i=a ∧ b j=c then A i j else 0)
  have hmap : T (∑ a, ∑ c, P a c) = ∑ a, ∑ c, T (P a c) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => map_sum T _ _)
  have hnormsum : ‖∑ a, ∑ c, T (P a c)‖ ≤ ∑ a, ∑ c, ‖T (P a c)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
  have hbnd : ∑ a, ∑ c, ‖T (P a c)‖ ≤ ∑ a, ∑ c, |G a c| *‖T A‖ := by
    dsimp only [T,P]
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro c _
    convert masked_smul_norm_le (G a c) A (fun i => b i=a) (fun j => b j=c) using 1
    all_goals try with_reducible_and_instances rfl
    try rfl
    apply congrArg (fun M : Matrix (Fin n) (Fin n) ℝ =>
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖)
    apply Matrix.ext
    intro i j
    simp only [Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
    split_ifs <;> rfl
  rw [bin_kernel_decomposition A b G]
  change ‖T (∑ a, ∑ c, P a c)‖ ≤ _
  rw [hmap]
  apply (hnormsum.trans hbnd).trans_eq
  simp only [T, Finset.sum_mul]

lemma kernel_error_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (G G' : Fin n → Fin n → ℝ) {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hr : ∀ i, ∑ j, |A i j| ≤ C) (hc : ∀ j, ∑ i, |A i j| ≤ C)
    (he : ∀ i j, |G i j-G' i j| ≤ a) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (fun i j => A i j*(G i j-G' i j))‖ ≤ a*C := by
  apply matrix_opNorm_le_schur _ (a*C) (mul_nonneg ha hC)
  · intro i
    calc
      _ ≤ ∑ j, a*|A i j| := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ j, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr i) ha
  · intro j
    calc
      _ ≤ ∑ i, a*|A i j| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ i, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc j) ha

lemma compact_kernel_approximation {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) {a : ℝ} (ha : 0<a) :
    ∃ (s : Finset X) (b : X → s), ∀ x y, |G (x,y)-G (b x,b y)| ≤ a := by
  classical
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hG) a ha
  obtain ⟨s,_,hs,hcov⟩ := finite_cover_balls_of_compact (X := X) isCompact_univ hδ
  have hnear (x : X) : ∃ y : {z // z ∈ hs.toFinset}, dist x y < δ := by
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_univ x))
    exact ⟨⟨y,hs.mem_toFinset.mpr hy⟩,hxy⟩
  choose b hb using hnear
  refine ⟨hs.toFinset,b,?_⟩
  intro x y
  have hh := hcont (show dist (x,y) ((b x: X),(b y: X)) < δ by
    simpa only [Prod.dist_eq,max_lt_iff] using And.intro (hb x) (hb y))
  exact (Real.dist_eq _ _ ▸ hh).le

theorem continuous_kernel_insertion {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) {C u : ℝ} (hC : 0≤C) (hu : 0<u) :
    ∃ δ : ℝ, 0<δ ∧ ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ),
      (∀ i, ∑ j, |A i j| ≤ C) → (∀ j, ∑ i, |A i j| ≤ C) →
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ δ →
      ∀ x : Fin n → X,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (fun i j => A i j*G (x i,x j))‖ ≤ u := by
  classical
  let a := u/(2*(C+1))
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨s,b,hb⟩ := compact_kernel_approximation G hG ha
  let B : ℝ := ∑ k : s, ∑ l : s, |G (k,l)|
  have hB : 0≤B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  let δ := u/(2*(B+1))
  have hd : 0<δ := by dsimp [δ]; positivity
  refine ⟨δ,hd,?_⟩
  intro n A hr hc hsmall x
  have hbin := bin_kernel_norm_le A (fun i => b (x i)) (fun k l => G (k,l))
  have herr := kernel_error_norm_le A (fun i j => G (x i,x j))
    (fun i j => G (b (x i),b (x j))) ha.le hC hr hc (fun i j => hb (x i) (x j))
  have hdecomp : Matrix.of (fun i j => A i j*G (x i,x j)) =
      Matrix.of (fun i j => A i j*G (b (x i),b (x j))) +
      Matrix.of (fun i j => A i j*(G (x i,x j)-G (b (x i),b (x j)))) := by
    apply Matrix.ext
    intro i j
    change A i j*G (x i,x j) = A i j*G (b (x i),b (x j)) + A i j*(G (x i,x j)-G (b (x i),b (x j)))
    ring
  have hBδ : B*δ ≤ u/2 := by
    dsimp [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(B+1))).mpr
    nlinarith
  have haC : a*C ≤ u/2 := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(C+1))).mpr
    nlinarith
  calc
    _ ≤ B*‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖+a*C := by
      change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.of (fun i j => A i j*G (x i,x j)))‖ ≤ _
      rw [hdecomp,map_add]
      exact (norm_add_le _ _).trans (add_le_add hbin herr)
    _ ≤ B*δ+a*C := add_le_add_left (mul_le_mul_of_nonneg_left hsmall hB) _
    _ ≤ u := by linarith only [hBδ,haC]

end SKRatio.MatrixNet

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_GaussianEvents
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Gaussian
open Calculus
variable {n : ℕ}

lemma continuous_operator_norm : Continuous (fun g : Disorder n => euclideanOpNorm (coupling g)) := by
  exact continuous_norm.comp
    (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
      (continuous_pi (fun i => continuous_pi (fun k => continuous_coupling i k))))

end SKRatio.Gaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_ExponentialEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

lemma ExponentiallyRare.mono {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A B : ∀ n, Set (H n)}
    (hB : ExponentiallyRare ρ B) (hAB : ∀ᶠ n in atTop, A n ⊆ B n) :
    ExponentiallyRare ρ A := by
  obtain ⟨C,c,hC,hc,he⟩ := hB
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he,hAB] with n hn hABn
  exact (measure_mono hABn).trans hn

lemma ExponentiallyRare.union {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A B : ∀ n, Set (H n)}
    (hA : ExponentiallyRare ρ A) (hB : ExponentiallyRare ρ B) :
    ExponentiallyRare ρ (fun n => A n ∪ B n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  obtain ⟨D,d,hD,hd,hf⟩ := hB
  refine ⟨C+D,min c d,add_pos hC hD,lt_min hc hd,?_⟩
  filter_upwards [he,hf] with n hn hm
  refine (measure_union_le _ _).trans ((add_le_add hn hm).trans ?_)
  have hc' : Real.exp (-c*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := min_le_left c d
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hd' : Real.exp (-d*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := min_le_right c d
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc' hC.le))
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hd' hD.le))

lemma exponentiallyRare_empty {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) : ExponentiallyRare ρ (fun _ => ∅) := by
  refine ⟨1,1,by norm_num,by norm_num,Filter.Eventually.of_forall ?_⟩
  intro n
  simp only [measure_empty, zero_le]

lemma ExponentiallyRare.iUnion_finite {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {ι : Type*} [Finite ι]
    {A : ι → ∀ n, Set (H n)} (hA : ∀ i, ExponentiallyRare ρ (A i)) :
    ExponentiallyRare ρ (fun n => ⋃ i, A i n) := by
  classical
  cases nonempty_fintype ι
  have hs (s : Finset ι) : ExponentiallyRare ρ (fun n => ⋃ i ∈ s, A i n) := by
    induction s using Finset.induction_on with
    | empty => simpa using exponentiallyRare_empty ρ
    | @insert i s hi ih =>
      have heq : (fun n => ⋃ j ∈ insert i s, A j n) =
          (fun n => A i n ∪ ⋃ j ∈ s, A j n) := by
        funext n
        ext h
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        aesop
      rw [heq]
      exact (hA i).union ih
  simpa using hs Finset.univ

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_ExponentialBounds
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatioClock.Regression

lemma eventually_polynomial_exp_le {a : ℝ} (ha : 0<a) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^k*exp (-a*n) ≤ exp (-(a/2)*n) := by
  have ht : Tendsto (fun n : ℕ => (a/2)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).div_const ((a/2)^k)
  simp only [zero_div] at h
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)^k*exp (-(a/2)*n)) atTop (𝓝 0) := by
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    simp only [Function.comp_apply,mul_pow,neg_mul]
    field_simp
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  calc
    _ = ((n:ℝ)^k*exp (-(a/2)*n))*exp (-(a/2)*n) := by
      rw [mul_assoc,←exp_add]
      congr 2
      ring
    _ ≤ 1*exp (-(a/2)*n) := mul_le_mul_of_nonneg_right hn.le (by positivity)
    _ = _ := one_mul _

lemma eventually_geom_exp_quadratic_le {a b c : ℝ} (ha : 0<a) (hb : 0<b) :
    ∀ᶠ n : ℕ in atTop, b^n*exp (-a*(n:ℝ)^2) ≤ exp (-c*n) := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [hn.eventually (eventually_ge_atTop ((log b+c)/a))] with n hn
  rw [show b^n = exp ((n:ℝ)*log b) by rw [exp_nat_mul,exp_log hb],←exp_add]
  apply exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).mp hn) (Nat.cast_nonneg (α := ℝ) n)
  nlinarith only [hh]

lemma exponentiallyRare_of_polynomial {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, Set (H n))
    {C c : ℝ} (hC : 0<C) (hc : 0 < c) (k : ℕ)
    (hbound : ∀ᶠ n in atTop, ρ n (A n) ≤ ENNReal.ofReal (C*(n:ℝ)^k*exp (-c*n))) :
    ExponentiallyRare ρ A := by
  refine ⟨C,c/2,hC,by positivity,?_⟩
  filter_upwards [hbound,eventually_polynomial_exp_le hc k] with n hn hp
  refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le

lemma exponentiallyRare_of_geom_quadratic {H : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, Set (H n))
    {C a b : ℝ} (hC : 0<C) (ha : 0<a) (hb : 0<b)
    (hbound : ∀ᶠ n in atTop,
      ρ n (A n) ≤ ENNReal.ofReal (C*b^n*exp (-a*(n:ℝ)^2))) :
    ExponentiallyRare ρ A := by
  refine ⟨C,1,hC,by norm_num,?_⟩
  filter_upwards [hbound,eventually_geom_exp_quadratic_le (c := 1) ha hb] with n hn hp
  refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le

lemma exponentiallyRare_iUnion_polynomial {H I : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)] [∀ n, Fintype (I n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, I n → Set (H n))
    {c C D : ℝ} (hc : 0 < c) (hC : 0<C) (hD : 0<D) (k : ℕ)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (I n) : ℝ) ≤ D*(n:ℝ)^k)
    (hbound : ∀ᶠ n in atTop, ∀ i, ρ n (A n i) ≤ ENNReal.ofReal (C*exp (-c*n))) :
    ExponentiallyRare ρ (fun n => ⋃ i, A n i) := by
  apply exponentiallyRare_of_polynomial ρ _ (mul_pos hD hC) hc k
  filter_upwards [hcard,hbound] with n hcard hb
  calc
    _ ≤ ∑ i, ρ n (A n i) := measure_iUnion_fintype_le (ρ n) _
    _ ≤ ∑ _i : I n, ENNReal.ofReal (C*exp (-c*n)) := Finset.sum_le_sum (fun i _ => hb i)
    _ = ENNReal.ofReal ((Fintype.card (I n):ℝ)*(C*exp (-c*n))) := by
      simp [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((D*C)*(n:ℝ)^k*exp (-c*n)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (D*(n:ℝ)^k)*(C*exp (-c*n)) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GOERegression
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise

namespace SKRatioClock.Regression

lemma coordinate_hasLaw {ι : Type*} [Fintype ι] (i : ι) :
    HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1) (standardArrayLaw ι) :=
  (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw

lemma coordinates_independent {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (g : ι → ℝ) => g i) (standardArrayLaw ι) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma coordinates_gaussian {ι : Type*} [Fintype ι] :
    HasGaussianLaw (fun g : ι → ℝ => g) (standardArrayLaw ι) :=
  coordinates_independent.hasGaussianLaw (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    cov[fun g : ι → ℝ => g i, fun g => g j; standardArrayLaw ι] = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    rw [covariance_self (coordinate_hasLaw i).aemeasurable,
      (coordinate_hasLaw i).variance_eq, variance_id_gaussianReal]
    simp
  · rw [ite_eq_right h]
    exact (coordinates_independent.indepFun h).covariance_eq_zero
      ((coordinate_hasLaw i).hasGaussianLaw.memLp_two)
      ((coordinate_hasLaw j).hasGaussianLaw.memLp_two)

attribute [local instance] OAI.SKRatioClock.Regression.matrixMeasurable
local instance matrixBorel_r908cf4_1 {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))
lemma goe_gaussian (n : ℕ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ => goe g)
      (standardArrayLaw (Fin n × Fin n)) := by
  have h := coordinates_gaussian.map_fun
    (show ((Fin n × Fin n) → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) from goeCLM n)
  exact h.congr (Filter.Eventually.of_forall (goeCLM_apply n))

lemma goe_entry_covariance {n : ℕ} (hn : 0 < n) (i j k l : Fin n) :
    cov[fun g : (Fin n × Fin n) → ℝ => goe g i j, fun g => goe g k l;
        standardArrayLaw (Fin n × Fin n)] =
      ((if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) / n := by
  have hLp (a : Fin n × Fin n) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  simp only [goe, covariance_fun_div_left, covariance_fun_div_right]
  change cov[(fun g => g (i,j)) + (fun g => g (j,i)),
    (fun g => g (k,l)) + (fun g => g (l,k)); standardArrayLaw (Fin n × Fin n)] /
      Real.sqrt (2*n) / Real.sqrt (2*n) = _
  rw [covariance_add_left (hLp _) (hLp _) ((hLp _).add (hLp _)),
    covariance_add_right (hLp _) (hLp _) (hLp _),
    covariance_add_right (hLp _) (hLp _) (hLp _)]
  simp only [coordinate_covariance, Prod.mk.injEq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (2*n) ^ 2 = 2*n := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2*(n : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [div_div, ← pow_two]
  rw [hs]
  have ha : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have hb : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  simp only [ha, hb]
  ring

lemma coordinate_mean {ι : Type*} [Fintype ι] (i : ι) :
    (∫ g : ι → ℝ, g i ∂standardArrayLaw ι) = 0 := by
  rw [(coordinate_hasLaw i).integral_eq, integral_id_gaussianReal]

lemma goe_entry_mean {n : ℕ} (i j : Fin n) :
    (∫ g : (Fin n × Fin n) → ℝ, goe g i j ∂standardArrayLaw (Fin n × Fin n)) = 0 := by
  simp only [goe, integral_div]
  rw [integral_add (coordinate_hasLaw (i,j)).hasGaussianLaw.integrable
    (coordinate_hasLaw (j,i)).hasGaussianLaw.integrable]
  simp only [coordinate_mean, add_zero, zero_div]

lemma gaussian_add_constant {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) (c : ι → ℝ) :
    HasGaussianLaw (fun ω => X ω + c) μ := by
  have := hX.isGaussian_map
  refine ⟨?_⟩
  change IsGaussian (μ.map ((fun x : ι → ℝ => x+c) ∘ X))
  rw [← AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : AEMeasurable (fun x : ι → ℝ => x+c) (μ.map X)) hX.aemeasurable]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianSquareTails
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

lemma gaussian_integrable_exp_quarter_sq :
    Integrable (fun x : ℝ => Real.exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1:ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  have h := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  apply h.congr
  filter_upwards [] with x
  symm
  simp only [toReal_gaussianPDF,
    smul_eq_mul, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, one_div]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma squareTail_nonneg (R x : ℝ) : 0 ≤ squareTail R x := by
  unfold squareTail
  split_ifs <;> positivity

lemma squareTail_le (R x : ℝ) : squareTail R x ≤ x^2 := by
  unfold squareTail
  split_ifs <;> simp [sq_nonneg]

lemma measurable_squareTail (R : ℝ) : Measurable (squareTail R) := by
  unfold squareTail
  exact Measurable.ite (measurableSet_lt measurable_const measurable_abs)
    (by fun_prop) measurable_const

lemma integrable_exp_squareTail {ν : Measure ℝ}
    (hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) ν) (R : ℝ) :
    Integrable (fun x => Real.exp (squareTail R x/4)) ν := by
  apply hi.mono' (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (squareTail_le R x) (by norm_num))

lemma tendsto_squareTail_mgf {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) ν) :
    Tendsto (fun R : ℕ => ∫ x, Real.exp (squareTail R x/4) ∂ν) atTop (𝓝 1) := by
  have ht : Tendsto (fun R : ℕ => ∫ x, Real.exp (squareTail R x/4) ∂ν)
      atTop (𝓝 (∫ _x : ℝ, (1:ℝ) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : ℝ => Real.exp (x^2/4))
    · intro R
      exact (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable)
    · exact hi
    · intro R
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (squareTail_le R x) (by norm_num))
    · filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with R hR
      have hx : |x| ≤ (R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
      simp [squareTail, not_lt.mpr hx]
  simpa using ht

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_GaussianEmpirical
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
namespace SKRatioClock.Regression

lemma subgaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | ε ≤ |X ω|} ≤ 2 * ENNReal.ofReal (Real.exp (-ε^2/(2*(c:ℝ)))) := by
  have hu := ENNReal.ofReal_le_ofReal (hX.measure_ge_le hε)
  have hl := ENNReal.ofReal_le_ofReal (hX.neg.measure_ge_le hε)
  simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hu hl
  have hs : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    intro ω h
    simpa only [Set.mem_union, Set.mem_ofPred_eq, le_abs] using h
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add hu hl
    _ = _ := (two_mul _).symm

lemma gaussian_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ where
  integrable_exp_mul t := by
    rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq]
    exact Real.exp_pos _
  mgf_le t := by
    rw [mgf_gaussianReal hX.map_eq]
    simp

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RandomMatrixBounded
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma bilinearCoefficient_sq_le {n : ℕ} (x y : Fin n → ℝ) :
    ∑ p, bilinearCoefficient x y p ^ 2 ≤
      2 * (∑ i, x i^2) * (∑ i, y i^2) := by
  have hp (i j : Fin n) : bilinearCoefficient x y (i,j)^2 +
      bilinearCoefficient x y (j,i)^2 ≤ 2 * (x i^2*y j^2 + x j^2*y i^2) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [bilinearCoefficient, h, not_lt_of_ge h.le, ite_true, if_true, ite_false, if_false, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      nlinarith [sq_nonneg (x i*y j-x j*y i)]
    · subst j; simp only [bilinearCoefficient, lt_self_iff_false, ite_false, if_false, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      positivity
    · simp only [bilinearCoefficient, h, not_lt_of_ge h.le, ite_true, if_true, ite_false, if_false, zero_pow (by decide : (2:ℕ) ≠ 0), zero_add]
      nlinarith [sq_nonneg (x i*y j-x j*y i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [mul_add, Finset.sum_add_distrib] at hs
  rw [Finset.sum_comm (f := fun i j => bilinearCoefficient x y (j,i)^2)] at hs
  rw [Fintype.sum_prod_type]
  have he : ∑ i, ∑ j, 2*(x i^2*y j^2) = 2 * (∑ i, x i^2) * (∑ j, y j^2) := by
    calc
      _ = 2 * (∑ i, ∑ j, x i^2*y j^2) := by simp only [Finset.mul_sum]
      _ = 2 * ((∑ i, x i^2) * (∑ j, y j^2)) := by rw [Finset.sum_mul_sum]
      _ = _ := by ring
  have he' : ∑ i, ∑ j, 2*(x j^2*y i^2) = 2 * (∑ i, x i^2) * (∑ j, y j^2) := by
    rw [Finset.sum_comm]; exact he
  rw [he, he'] at hs
  linarith

lemma coupling_bilinear {n : ℕ} (x y : Fin n → ℝ) (g : Disorder n) :
    ∑ i, ∑ j, x i*coupling g i j*y j =
      ∑ e : Edge n, (x e.1.1*y e.1.2+x e.1.2*y e.1.1)*g e := by
  let F : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 < p.2 then x p.1*y p.2*g ⟨p,h⟩ else 0
  let G : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 < p.2 then x p.2*y p.1*g ⟨p,h⟩ else 0
  have hid (i j : Fin n) : x i*coupling g i j*y j = F (i,j)+G (j,i) := by
    dsimp [F,G,coupling]
    split_ifs with h₁ h₂ h₂ <;> try omega
    all_goals ring
  simp_rw [hid]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => G (j,i)), ← Finset.sum_add_distrib]
  simp_rw [←Finset.sum_add_distrib]
  rw [←Fintype.sum_prod_type (f := fun p => F p+G p)]
  apply Finset.sum_congr_set (s := {p : Fin n × Fin n | p.1<p.2})
  · intro p hp
    simp only [F,G,show p.1<p.2 from hp,dite_eq_left]
    ring
  · intro p hp
    simp [F,G,show ¬p.1<p.2 from hp]

lemma edgeCoefficient_sq_le {n : ℕ} (x y : Fin n → ℝ) :
    ∑ e : Edge n, (x e.1.1*y e.1.2+x e.1.2*y e.1.1)^2 ≤
      2*(∑ i, x i^2)*(∑ i, y i^2) := by
  have he : (∑ p, bilinearCoefficient x y p^2) =
      ∑ e : Edge n, (x e.1.1*y e.1.2+x e.1.2*y e.1.1)^2 := by
    apply Finset.sum_congr_set (s := {p : Fin n × Fin n | p.1<p.2})
    · intro p hp
      simp only [bilinearCoefficient,show p.1<p.2 from hp,ite_true, if_true]
    · intro p hp
      simp only [bilinearCoefficient,show ¬p.1<p.2 from hp,ite_false, if_false,zero_pow (by decide : (2:ℕ) ≠ 0)]
  rw [←he]
  exact bilinearCoefficient_sq_le x y

lemma coupling_inner {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (g : Disorder n) :
    inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g) x) y =
      ∑ e : Edge n, (y e.1.1*x e.1.2+y e.1.2*x e.1.1)*g e := by
  erw [real_inner_comm,Matrix.inner_toEuclideanCLM]
  change (∑ i, y i*∑ j, coupling g i j*x j) = _
  simp only [Finset.mul_sum,←mul_assoc]
  exact coupling_bilinear y x g

lemma subgaussian_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c d : ℝ≥0} (hX : HasSubgaussianMGF X c μ) (hcd : c ≤ d) :
    HasSubgaussianMGF X d μ where
  integrable_exp_mul := hX.integrable_exp_mul
  mgf_le t := (hX.mgf_le t).trans (Real.exp_le_exp.mpr (by
    have h : (c:ℝ) ≤ d := hcd
    gcongr))

lemma bounded_zero_subgaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hXm : AEMeasurable X μ)
    (T : ℝ≥0) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ T) (hmean : ∫ ω, X ω ∂μ = 0) :
    HasSubgaussianMGF X (T^2) μ := by
  have hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (-(T:ℝ)) T := by
    filter_upwards [hbound] with ω hω
    exact abs_le.mp hω
  have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hXm hb hmean
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply NNReal.coe_injective
  change (T:ℝ) = |(T:ℝ)-(-(T:ℝ))|/2
  rw [abs_of_nonneg (by linarith [T.coe_nonneg])]
  ring

lemma independent_subgaussian_linear {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (hXi : iIndepFun X μ) {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) (a : ι → ℝ) :
    HasSubgaussianMGF (fun ω => ∑ i, a i*X i ω) (∑ i, (NNReal.mk (a i^2) (sq_nonneg (a i)))*c) μ := by
  have hi := hXi.comp (fun i z => a i*z) (fun i => measurable_const.mul measurable_id)
  have hh := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ => (hX i).const_mul (a i))
  exact hh

lemma bounded_matrix_inner_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n)
    (X : Edge n → Ω → ℝ) (hXi : iIndepFun X μ) {T : ℝ≥0} (hT : 0<T)
    (hX : ∀ e, HasSubgaussianMGF (X e) (T^2) μ)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖≤1) (hy : ‖y‖≤1)
    {u : ℝ} (hu : 0≤u) :
    μ {ω | u ≤ |inner (𝕜 := ℝ)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => X e ω/n)) x) y|} ≤
      2*ENNReal.ofReal (Real.exp (-u^2*(n:ℝ)^2/(4*(T:ℝ)^2))) := by
  let a : Edge n → ℝ := fun e => (y e.1.1*x e.1.2+y e.1.2*x e.1.1)/(n:ℝ)
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hcoef : ∑ e : Edge n, a e^2 ≤ 2/(n:ℝ)^2 := by
    dsimp only [a]
    simp only [div_pow,←Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hh := edgeCoefficient_sq_le y x
    rw [←EuclideanSpace.real_norm_sq_eq,←EuclideanSpace.real_norm_sq_eq] at hh
    have hx2 : ‖x‖^2≤1 := by nlinarith [norm_nonneg x]
    have hy2 : ‖y‖^2≤1 := by nlinarith [norm_nonneg y]
    nlinarith [mul_le_mul hy2 hx2 (sq_nonneg ‖x‖) (by norm_num : (0:ℝ)≤1)]
  have hv : (∑ e : Edge n, (NNReal.mk (a e^2) (sq_nonneg (a e)))*T^2) ≤ Real.toNNReal (2*(T:ℝ)^2/(n:ℝ)^2) := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_mk,←Finset.sum_mul,Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2*(T:ℝ)^2/(n:ℝ)^2)]
    calc
      _ ≤ (2/(n:ℝ)^2)*(T:ℝ)^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = _ := by ring
  have hh := subgaussian_abs_tail
    (subgaussian_mono (independent_subgaussian_linear X hXi hX a) hv) u hu
  have hid (ω : Ω) : inner (𝕜 := ℝ)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => X e ω/n)) x) y =
      ∑ e : Edge n, a e*X e ω := by
    rw [coupling_inner]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [a]
    ring
  simp_rw [hid]
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  congr 2
  rw [Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2*(T:ℝ)^2/(n:ℝ)^2)]
  have htR : (T:ℝ) ≠ 0 := ne_of_gt hT
  field_simp
  ring

lemma bounded_matrix_opNorm_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n)
    (X : Edge n → Ω → ℝ) (hXi : iIndepFun X μ) {T : ℝ≥0} (hT : 0<T)
    (hX : ∀ e, HasSubgaussianMGF (X e) (T^2) μ)
    {u : ℝ} (hu : 0≤u) :
    μ {ω | 2*u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => X e ω/n))‖} ≤
      ENNReal.ofReal (2*(81:ℝ)^n*Real.exp (-u^2*(n:ℝ)^2/(4*(T:ℝ)^2))) := by
  have h := opNorm_tail_of_bilinear μ _ hu _
    (fun x y hx hy => bounded_matrix_inner_tail hn X hXi hT hX x y hx hy hu)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤81)]
  ring

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianSquareMatrix
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology _root_.OAI.SKRatio.Planted.law_probability _root_.OAI.SKRatioGaussian.instNonemptyUnitBall
attribute [-simp] _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Fields.expectation_const
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma independent_sum_upper_tail {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hXi : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (s : Finset ι) {t M : ℝ} (ht : 0<t)
    (hi : ∀ i ∈ s, Integrable (fun ω => exp (t*X i ω)) μ)
    (hmgf : ∀ i ∈ s, cgf (X i) μ t ≤ M) (hM : 0≤M)
    {n : ℕ} (hn : 0<n) (hcard : s.card≤n) (a : ℝ) :
    μ {ω | a ≤ (∑ i∈s, X i ω)/(n:ℝ)} ≤ ENNReal.ofReal (exp (-((t*a-M)*n))) := by
  have hsum := hXi.integrable_exp_mul_sum hXm (s := s) hi
  have hb := measure_ge_le_exp_cgf (μ := μ) (X := ∑ i∈s, X i) (a*n) ht.le hsum
  rw [hXi.cgf_sum hXm hi] at hb
  have hm : ∑ i∈s, cgf (X i) μ t ≤ (n:ℝ)*M := by
    calc
      _ ≤ ∑ _i∈s, M := Finset.sum_le_sum hmgf
      _ = (s.card:ℝ)*M := by simp
      _ ≤ (n:ℝ)*M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
  have he : {ω | a*(n:ℝ) ≤ (∑ i∈s, X i) ω} = {ω | a ≤ (∑ i∈s, X i ω)/(n:ℝ)} := by
    ext ω
    simp only [Finset.sum_apply,mem_ofPred_eq,le_div_iff₀ (Nat.cast_pos.mpr hn : (0:ℝ)<n)]
  rw [he] at hb
  have h := ENNReal.ofReal_le_ofReal hb
  simp only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_))
  linarith

lemma gaussian_squareTail_row_bound {a : ℝ} (ha : 0<a) :
    ∃ R c : ℝ, 0<R ∧ 0 < c ∧
      (∫ z, squareTail R z ∂gaussianReal 0 1) < a ∧
      ∀ {ι : Type} [Fintype ι] (s : Finset ι) {n : ℕ}, 0<n → s.card ≤ n →
      standardArrayLaw ι {z | a ≤ (∑ i∈s, squareTail R (z i))/(n:ℝ)} ≤
        ENNReal.ofReal (exp (-c*n)) := by
  have ht : Tendsto (fun R : ℕ => log (∫ z, exp (squareTail R z/4) ∂gaussianReal 0 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,log_one] using (continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp
      (tendsto_squareTail_mgf gaussian_integrable_exp_quarter_sq)
  have hsq : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).integrable_sq
  have hm : Tendsto (fun R : ℕ => ∫ z, squareTail R z ∂gaussianReal 0 1) atTop (𝓝 0) := by
    have hb := tendsto_integral_of_dominated_convergence (fun z : ℝ => z^2)
      (μ := gaussianReal 0 1)
      (F := fun R : ℕ => squareTail R) (f := fun _ => (0:ℝ))
      (fun R => (measurable_squareTail R).aestronglyMeasurable) hsq
    have h := hb (fun R => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (squareTail_nonneg _ _)]
      exact squareTail_le _ _)) (ae_of_all _ (fun z => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈|z|⌉₊] with R hR
        have hz : |z| ≤ (R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
        simp [squareTail,not_lt.mpr hz]))
    simpa using h
  obtain ⟨R,hR,hmg,hmean⟩ := ((eventually_ge_atTop 1).and
    ((ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<a/4))).and
      (hm.eventually (gt_mem_nhds ha)))).exists
  let M := log (∫ z, exp (squareTail R z/4) ∂gaussianReal 0 1)
  have hM : 0≤M := by
    apply log_nonneg
    calc
      1 = ∫ _z : ℝ, (1:ℝ) ∂gaussianReal 0 1 := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_exp_squareTail gaussian_integrable_exp_quarter_sq R)
        (by intro z; exact one_le_exp_iff.mpr (div_nonneg (squareTail_nonneg _ _) (by norm_num)))
  refine ⟨R,a/4-M,by exact_mod_cast hR,sub_pos.mpr hmg,hmean,?_⟩
  intro ι _ s n hn hs
  have hc (i : ι) : cgf (fun z : ι → ℝ => squareTail R (z i)) (standardArrayLaw ι) (1/4) = M := by
    unfold cgf mgf M
    congr 1
    have hh := (coordinate_hasLaw i).integral_comp (f := fun z : ℝ => exp (squareTail R z/4)) (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable)
    simpa only [one_div_mul_eq_div, Function.comp_def] using hh
  have hi (i : ι) : Integrable (fun z : ι → ℝ => exp ((1/4)*squareTail R (z i))) (standardArrayLaw ι) := by
    have hh := integrable_exp_squareTail gaussian_integrable_exp_quarter_sq (R:ℝ)
    rw [←(coordinate_hasLaw i).map_eq] at hh
    have h := (integrable_map_measure (((measurable_squareTail R).div_const 4).exp.aestronglyMeasurable) (coordinate_hasLaw i).aemeasurable).mp hh
    simpa only [one_div_mul_eq_div, Function.comp_def] using h
  have hb := independent_sum_upper_tail (fun i (z : ι → ℝ) => squareTail R (z i))
    (coordinates_independent.comp (fun _ => squareTail R) (fun _ => measurable_squareTail R))
    (fun i => (measurable_squareTail R).comp (measurable_pi_apply i)) s
    (by norm_num : (0:ℝ)<1/4) (fun i _ => hi i) (fun i _ => le_of_eq (hc i)) hM hn hs a
  simpa only [one_div_mul_eq_div,neg_mul] using hb

lemma incidentEdges_card_le {n : ℕ} (i : Fin n) : (incidentEdges i).card ≤ n := by
  let other (e : Edge n) : Fin n := if e.1.1 = i then e.1.2 else e.1.1
  have h := Finset.card_le_card_of_injOn other
    (t := (Finset.univ : Finset (Fin n))) (s := incidentEdges i)
    (fun _ _ => Finset.mem_univ _) (by
      intro e he f hf hef
      have he' : e.1.1 = i ∨ e.1.2 = i := (Finset.mem_filter.mp he).2
      have hf' : f.1.1 = i ∨ f.1.2 = i := (Finset.mem_filter.mp hf).2
      have ehe := e.2
      have ehf := f.2
      apply Subtype.ext
      apply Prod.ext
      all_goals dsimp [other] at hef; split_ifs at hef <;> rcases he' with he' | he' <;>
        rcases hf' with hf' | hf' <;> simp_all <;> omega)
  simpa using h

lemma sum_coupling_row {n : ℕ} (g : Disorder n) (i : Fin n) :
    ∑ j, coupling g i j = ∑ e ∈ incidentEdges i, g e := by
  have he := coupling_bilinear (fun j => if j=i then 1 else 0) (fun _ => 1) g
  simp only [mul_one,ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true] at he
  rw [he,incidentEdges,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hh : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  by_cases h1 : e.1.1=i <;> by_cases h2 : e.1.2=i <;> simp_all

lemma abs_coupling {n : ℕ} (g : Disorder n) (i j : Fin n) :
    |coupling g i j| = coupling (fun e => |g e|) i j := by
  unfold coupling
  split_ifs <;> simp

lemma coupling_nonneg {n : ℕ} {g : Disorder n} (hg : ∀ e, 0 ≤ g e) (i j : Fin n) :
    0 ≤ coupling g i j := by
  unfold coupling
  split_ifs <;> first | exact hg _ | exact le_refl 0

lemma coupling_add {n : ℕ} (g h : Disorder n) :
    coupling (g+h) = coupling g + coupling h := by
  funext i j
  change coupling (g+h) i j = coupling g i j + coupling h i j
  unfold coupling
  split_ifs <;> simp_all

lemma coupling_const_mul {n : ℕ} (c : ℝ) (g : Disorder n) :
    coupling (fun e => c*g e) = c • coupling g := by
  funext i j
  change coupling (fun e => c*g e) i j = c*coupling g i j
  unfold coupling
  split_ifs <;> simp_all

lemma coupling_const_norm_le {n : ℕ} (c : ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun _ => c))‖ ≤ n*|c| := by
  apply matrix_opNorm_le_schur _ (n*|c|) (by positivity)
  all_goals
    intro i
    calc
      _ ≤ ∑ _j : Fin n, |c| := Finset.sum_le_sum (fun j _ => by
        unfold coupling; split_ifs <;> simp [abs_nonneg])
      _ = _ := by simp

lemma integrable_standard_square : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) := by
  simpa only [id_eq] using (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).integrable_sq

lemma standard_square_integral : ∫ z : ℝ, z^2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal,sub_zero,NNReal.coe_one] using h

lemma continuous_clippedSquare (R : ℝ) : Continuous (clippedSquare R) := by
  unfold clippedSquare; fun_prop

lemma clippedSquare_nonneg (R z : ℝ) : 0 ≤ clippedSquare R z := le_min (sq_nonneg _) (sq_nonneg _)

lemma clippedSquare_le (R z : ℝ) : clippedSquare R z ≤ R^2 := min_le_right _ _

lemma square_sub_clip_nonneg (R z : ℝ) : 0 ≤ z^2-clippedSquare R z :=
  sub_nonneg.mpr (min_le_left _ _)

lemma square_sub_clip_le {R : ℝ} (hR : 0 ≤ R) (z : ℝ) :
    z^2-clippedSquare R z ≤ squareTail R z := by
  by_cases hz : R < |z|
  · simp only [squareTail,hz,ite_true, if_true]
    linarith [clippedSquare_nonneg R z]
  · have h : z^2 ≤ R^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z) hR).2 (le_of_not_gt hz)
    simp only [clippedSquare,min_eq_left h,sub_self,squareTail,hz,ite_false, if_false,le_refl]

lemma clippedSquare_integrable (R : ℝ) : Integrable (clippedSquare R) (gaussianReal 0 1) := by
  apply Integrable.of_bound (continuous_clippedSquare R).aestronglyMeasurable (R^2)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (clippedSquare_nonneg _ _)]; exact clippedSquare_le _ _)

lemma clippedSquare_mean_bounds (R : ℝ) :
    0 ≤ ∫ z, clippedSquare R z ∂gaussianReal 0 1 ∧
      (∫ z, clippedSquare R z ∂gaussianReal 0 1) ≤ R^2 := by
  constructor
  · exact integral_nonneg (clippedSquare_nonneg R)
  · simpa using integral_mono (clippedSquare_integrable R) (integrable_const (R^2))
      (clippedSquare_le R)

lemma clippedSquare_mean_error {R : ℝ} (hR : 0 ≤ R) :
    |(∫ z, clippedSquare R z ∂gaussianReal 0 1)-1| ≤
      ∫ z, squareTail R z ∂gaussianReal 0 1 := by
  have hi : Integrable (squareTail R) (gaussianReal 0 1) :=
    integrable_standard_square.mono' (measurable_squareTail R).aestronglyMeasurable
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (squareTail_nonneg _ _)]; exact squareTail_le _ _))
  have hm : (∫ z, clippedSquare R z ∂gaussianReal 0 1) ≤ 1 := by
    rw [← standard_square_integral]
    exact integral_mono (clippedSquare_integrable R) integrable_standard_square (fun _ => min_le_left _ _)
  have h := integral_mono (integrable_standard_square.sub (clippedSquare_integrable R)) hi
    (square_sub_clip_le hR)
  simp only [Pi.sub_apply] at h
  rw [integral_sub integrable_standard_square (clippedSquare_integrable R),standard_square_integral] at h
  rw [abs_of_nonpos (sub_nonpos.mpr hm)]
  linarith only [h]

lemma centered_clip_subgaussian {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R) (i : ι) :
    HasSubgaussianMGF
      (fun z : ι → ℝ => clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))
      ((Real.toNNReal (R^2))^2) (standardArrayLaw ι) := by
  apply bounded_zero_subgaussian _
    (((continuous_clippedSquare R).measurable.comp (measurable_pi_apply i)).sub measurable_const).aemeasurable
  · exact ae_of_all _ (fun z => by
      simp only [Pi.sub_apply,Function.comp_def]
      rw [Real.coe_toNNReal _ (sq_pos_of_pos hR).le,abs_le]
      have h := clippedSquare_mean_bounds R
      constructor <;> linarith [clippedSquare_le R (z i),clippedSquare_nonneg R (z i)])
  · have hc := (coordinate_hasLaw i).integral_comp
      (f := fun x : ℝ => clippedSquare R x-(∫ y, clippedSquare R y ∂gaussianReal 0 1))
      (((continuous_clippedSquare R).sub continuous_const).aestronglyMeasurable)
    simp only [Function.comp_def] at hc
    simp only [Pi.sub_apply,Function.comp_def]
    rw [hc,integral_sub (clippedSquare_integrable R) (integrable_const _)]
    simp

lemma clipped_square_matrix_rare {R u : ℝ} (hR : 0 < R) (hu : 0 < u) :
    ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (coupling (fun e => (clippedSquare R (z e)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))/n))‖}) := by
  apply exponentiallyRare_of_geom_quadratic _ _ (C := 2) (b := 81) (a := (u/2)^2/(4*(R^2)^2))
    (by norm_num) (by positivity) (by norm_num)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hb := bounded_matrix_opNorm_tail hn
    (fun e (z : Edge n → ℝ) => clippedSquare R (z e)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))
    (coordinates_independent.comp
      (fun _ x => clippedSquare R x-(∫ y, clippedSquare R y ∂gaussianReal 0 1))
      (fun _ => ((continuous_clippedSquare R).sub continuous_const).measurable))
    (show 0 < Real.toNNReal (R^2) from Real.toNNReal_pos.mpr (by positivity))
    (centered_clip_subgaussian hR) (u := u/2) (by positivity)
  rw [show 2*(u/2) = u by ring,Real.coe_toNNReal _ (sq_nonneg _)] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring_nf

lemma square_remainder_norm_le {n : ℕ} (hn : 0<n) (z : Disorder n)
    {R a : ℝ} (hR : 0≤R) (ha : 0≤a)
    (hrow : ∀ i, (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ) ≤ a) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (z e^2-clippedSquare R (z e))/n))‖ ≤ a := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  let g : Disorder n := fun e => (z e^2-clippedSquare R (z e))/n
  have hg : ∀ e, 0≤g e := fun e => div_nonneg (square_sub_clip_nonneg _ _) hnR.le
  have hr (i : Fin n) : ∑ j, |coupling g i j| ≤ a := by
    simp_rw [abs_of_nonneg (coupling_nonneg hg _ _)]
    rw [sum_coupling_row]
    change (∑ e ∈ incidentEdges i, (z e^2-clippedSquare R (z e))/(n:ℝ)) ≤ a
    rw [←Finset.sum_div]
    exact (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun e _ => square_sub_clip_le hR _)) hnR.le).trans (hrow i)
  exact matrix_opNorm_le_schur (coupling g) a ha hr (fun j => by
    simpa only [coupling_symm] using hr j)

lemma coupling_norm_add_three {n : ℕ} (A B D : Disorder n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (A+B+D))‖ ≤
      (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling A)‖ +
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling B)‖) +
          ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling D)‖ := by
  rw [coupling_add,coupling_add]
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    ((Matrix.of (coupling A)+Matrix.of (coupling B))+Matrix.of (coupling D))‖ ≤ _
  rw [map_add,map_add]
  exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)

lemma centered_square_mean_norm_le {n : ℕ} (hn : 0<n) {R : ℝ} (hR : 0≤R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling
      (fun _ => ((∫ x, clippedSquare R x ∂gaussianReal 0 1)-1)/n))‖ ≤
        ∫ x, squareTail R x ∂gaussianReal 0 1 := by
  let m := ∫ x, clippedSquare R x ∂gaussianReal 0 1
  have hh := coupling_const_norm_le (n := n) ((m-1)/n)
  have hnR : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hm : (n:ℝ)*|(m-1)/n| = |m-1| := by
    rw [abs_div,show |(n:ℝ)|=(n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
    field_simp
  rw [hm] at hh
  exact hh.trans (clippedSquare_mean_error hR)

lemma centered_square_norm_le {n : ℕ} (hn : 0<n) (z : Disorder n)
    {R a : ℝ} (hR : 0≤R) (ha : 0≤a)
    (hrow : ∀ i, (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ) ≤ a) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (z e^2-1)/n))‖ ≤
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (clippedSquare R (z e)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))/n))‖ +
      (∫ x, squareTail R x ∂gaussianReal 0 1) + a := by
  let m := ∫ x, clippedSquare R x ∂gaussianReal 0 1
  let A : Disorder n := fun e => (clippedSquare R (z e)-m)/n
  let B : Disorder n := fun _ => (m-1)/n
  let D : Disorder n := fun e => (z e^2-clippedSquare R (z e))/n
  have he : (fun e => (z e^2-1)/(n:ℝ)) = A+B+D := by
    funext e
    dsimp only [A,B,D,Pi.add_apply]
    ring
  have hB := centered_square_mean_norm_le hn hR
  have hD := square_remainder_norm_le hn z hR ha hrow
  rw [he]
  exact (coupling_norm_add_three A B D).trans (add_le_add (add_le_add_right hB _) hD)

theorem centered_gaussian_square_matrix_rare {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (coupling (fun e => (z e^2-1)/n))‖}) := by
  obtain ⟨R,c,hR,hc,hmean,hb⟩ := gaussian_squareTail_row_bound (a := u/3) (by positivity)
  have htail : ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => ⋃ i : Fin n, {z | u/3 ≤ (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ)}) := by
    apply exponentiallyRare_iUnion_polynomial _ _ hc (hC := zero_lt_one) (hD := zero_lt_one) 1
    · apply Eventually.of_forall
      intro n
      simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      intro i
      simpa only [one_mul] using hb (incidentEdges i) hn (incidentEdges_card_le i)
  apply ((clipped_square_matrix_rare hR (show 0<u/3 by positivity)).union htail).mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro z hz
  by_contra hnot
  have hclip : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (clippedSquare R (z e)-(∫ x, clippedSquare R x ∂gaussianReal 0 1))/n))‖ ≤ u/3 :=
    le_of_not_gt (fun h => hnot (Or.inl h))
  have hrows : ∀ i, (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ) ≤ u/3 := by
    intro i
    exact (not_le.mp (fun hi => hnot (Or.inr (mem_iUnion.mpr ⟨i,hi⟩)))).le
  have hh := centered_square_norm_le hn z hR.le (by positivity : 0≤u/3) hrows
  change u < _ at hz
  linarith

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PlantedSquares
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

lemma affineDisorder_hasLaw {n : ℕ} (hn : 0<n) (β : ℝ) :
    HasLaw (affineDisorder (n := n) β) (law β n) (standardArrayLaw (Edge n)) := by
  have hi := (coordinates_independent (ι := Edge n)).comp (fun _ (x : ℝ) => (β/sqrt n)*x+β^2/n)
    (fun _ => by fun_prop)
  apply iIndepFun.hasLaw_pi (μ := fun _ => gaussianReal (β^2/n) (Real.toNNReal (β^2/n))) _ hi
  intro e
  have h := gaussianReal_add_const (gaussianReal_const_mul (coordinate_hasLaw e) (β/sqrt n)) (β^2/n)
  have hv : (NNReal.mk ((β/sqrt n)^2) (sq_nonneg _) : ℝ≥0)*1 = Real.toNNReal (β^2/n) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mk,mul_one,
      Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))]
    rw [div_pow,sq_sqrt (Nat.cast_pos.mpr hn).le]
  simpa only [mul_zero,zero_add,hv,Function.comp_def] using h

lemma coupling_scaled_norm {n : ℕ} (c : ℝ) (g : Disorder n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => c*g e))‖ =
      |c| *‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g)‖ := by
  rw [coupling_const_mul]
  change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (c • Matrix.of (coupling g))‖ = _
  rw [map_smul,norm_smul,Real.norm_eq_abs]
  rfl

lemma normalized_absolute_row_le {n : ℕ} (hn : 0<n) (z : Disorder n) (i : Fin n) :
    (∑ e ∈ incidentEdges i, |z e|)/(n:ℝ) ≤
      (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ)+1 := by
  have hsum : ∑ e ∈ incidentEdges i, |z e| ≤ (∑ e ∈ incidentEdges i, z e^2)+(n:ℝ) := by
    calc
      _ ≤ ∑ e ∈ incidentEdges i, (z e^2+1) := Finset.sum_le_sum (fun e _ => by
        nlinarith [sq_nonneg (|z e|-1),sq_abs (z e)])
      _ = (∑ e ∈ incidentEdges i, z e^2)+((incidentEdges i).card:ℝ) := by simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add_right (by exact_mod_cast incidentEdges_card_le i) _
  have hd := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : (0:ℝ)≤n)
  simpa only [add_div,div_self (show (n:ℝ)≠0 from Nat.cast_ne_zero.mpr hn.ne')] using hd

lemma normalized_matrix_norm_le_row_square {n : ℕ} (hn : 0<n) (z : Disorder n)
    {C : ℝ} (hC : 0≤C) (hrow : ∀ i, (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ C) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => z e/n))‖ ≤ C+1 := by
  have hr (i : Fin n) : ∑ j, |coupling (fun e => z e/n) i j| ≤ C+1 := by
    simp_rw [abs_coupling]
    rw [sum_coupling_row]
    simp only [abs_div,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n),←Finset.sum_div]
    exact (normalized_absolute_row_le hn z i).trans (add_le_add_left (hrow i) _)
  exact matrix_opNorm_le_schur _ (C+1) (by linarith) hr
    (fun j => by simpa only [coupling_symm] using hr j)

lemma gaussian_rows_square_bounded :
    ∃ C : ℝ, 0<C ∧ ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | ∃ i : Fin n, C < (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ)}) := by
  obtain ⟨R,c,hR,hc,_,ht⟩ := gaussian_squareTail_row_bound (a := 1) zero_lt_one
  refine ⟨R^2+1,by positivity,?_⟩
  have hr : ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => ⋃ i : Fin n, {z | 1 ≤ (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ)}) := by
    apply exponentiallyRare_iUnion_polynomial _ _ hc (hC := zero_lt_one) (hD := zero_lt_one) 1
    · exact Eventually.of_forall (fun n => by simp)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      intro i
      simpa only [one_mul] using ht (incidentEdges i) hn (incidentEdges_card_le i)
  apply hr.mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  rintro z ⟨i,hi⟩
  apply mem_iUnion.mpr
  refine ⟨i,?_⟩
  have hb : (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ R^2+
      (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ) := by
    have hs : ∑ e ∈ incidentEdges i, z e^2 ≤
        (n:ℝ)*R^2+∑ e ∈ incidentEdges i, squareTail R (z e) := by
      calc
        _ ≤ ∑ e ∈ incidentEdges i, (R^2+squareTail R (z e)) :=
          Finset.sum_le_sum (fun e _ => by
            linarith [clippedSquare_le R (z e),square_sub_clip_le hR.le (z e)])
        _ = ((incidentEdges i).card:ℝ)*R^2+∑ e ∈ incidentEdges i, squareTail R (z e) := by simp [Finset.sum_add_distrib]
        _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right
          (by exact_mod_cast incidentEdges_card_le i) (sq_nonneg R)) _
    have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n : (0:ℝ)≤n)
    simpa only [add_div,mul_div_cancel_left₀ _ (show (n:ℝ)≠0 from Nat.cast_ne_zero.mpr hn.ne')] using hd
  change (1:ℝ) ≤ (∑ e ∈ incidentEdges i, squareTail R (z e))/(n:ℝ)
  linarith only [hb,hi]

lemma affine_square_decomposition {n : ℕ} (hn : 0<n) (β : ℝ) (z : Disorder n) :
    (fun e => affineDisorder β z e^2-β^2/n) =
      (fun e => β^2*((z e^2-1)/n)) +
      (fun e => (2*β^3/sqrt n)*(z e/n)) + (fun _ => β^4/(n:ℝ)^2) := by
  have hnR : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hs : sqrt (n:ℝ)≠0 := (sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  funext e
  dsimp only [affineDisorder,Pi.add_apply]
  rw [add_sq,mul_pow,div_pow,sq_sqrt (Nat.cast_nonneg n)]
  field_simp
  ring

lemma affine_square_norm_le {n : ℕ} (hn : 0<n) (β : ℝ) (z : Disorder n)
    {C : ℝ} (hC : 0≤C) (hrow : ∀ i, (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ C) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => affineDisorder β z e^2-β^2/n))‖ ≤
      β^2*‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => (z e^2-1)/n))‖ +
        |2*β^3/sqrt n| *(C+1)+β^4/n := by
  rw [affine_square_decomposition hn]
  apply (coupling_norm_add_three _ _ _).trans
  rw [coupling_scaled_norm,coupling_scaled_norm,abs_of_nonneg (sq_nonneg β)]
  apply add_le_add
  · apply add_le_add_right
    exact mul_le_mul_of_nonneg_left (normalized_matrix_norm_le_row_square hn z hC hrow) (abs_nonneg _)
  · have hh := coupling_const_norm_le (n := n) (β^4/(n:ℝ)^2)
    have hm : (n:ℝ)*|β^4/(n:ℝ)^2| = β^4/n := by
      rw [abs_of_nonneg (by positivity)]
      field_simp
    simpa only [hm] using hh

lemma affine_square_matrix_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (coupling (fun e => affineDisorder β z e^2-β^2/n))‖}) := by
  obtain ⟨C,hC,hrows⟩ := gaussian_rows_square_bounded
  have hsq := centered_gaussian_square_matrix_rare (u := u/(2*(β^2+1))) (by positivity)
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  have hl : Tendsto (fun n : ℕ => |2*β^3/sqrt n| *(C+1)+β^4/n) atTop (𝓝 0) := by
    have h1 := ((tendsto_const_nhds (x := 2*β^3)).div_atTop (tendsto_sqrt_atTop.comp hn)).abs.mul_const (C+1)
    have h2 := (tendsto_const_nhds (x := β^4)).div_atTop hn
    simpa only [abs_zero,zero_mul,zero_add,Function.comp_def] using h1.add h2
  apply (hsq.union hrows).mono
  filter_upwards [eventually_gt_atTop 0,hl.eventually (gt_mem_nhds (by positivity : (0:ℝ)<u/2))] with n hn hb
  intro z hz
  by_contra hnot
  have hgood : ∀ i, (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ C := by
    intro i
    exact le_of_not_gt (fun hi => hnot (Or.inr ⟨i,hi⟩))
  have hsmall : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => (z e^2-1)/n))‖ ≤ u/(2*(β^2+1)) :=
    le_of_not_gt (fun hi => hnot (Or.inl hi))
  have ha := affine_square_norm_le hn β z hC.le hgood
  have hh := mul_le_mul_of_nonneg_left hsmall (sq_nonneg β)
  have ht : β^2*(u/(2*(β^2+1))) ≤ u/2 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (by positivity : (0:ℝ)<2*(β^2+1))).mpr (by nlinarith)
  change u < _ at hz
  linarith only [ha,hh,ht,hb,hz]

theorem square_matrix_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (law β)
      (fun n => {g | u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (coupling (fun e => g e^2-β^2/n))‖}) := by
  obtain ⟨C,c,hC,hc,hb⟩ := affine_square_matrix_rare β hu
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [hb,eventually_gt_atTop 0] with n hn hdim
  have hm : MeasurableSet {g : Disorder n | u <
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => g e^2-β^2/n))‖} := by
    apply measurableSet_lt measurable_const
    exact ((Gaussian.continuous_operator_norm (n := n)).comp (continuous_pi (fun e =>
      ((continuous_apply e).pow 2).sub continuous_const))).measurable
  rw [←(affineDisorder_hasLaw hdim β).measure_eq hm]
  exact hn

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_WeightedSquares
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

lemma squareError_decomposition {n : ℕ} (β : ℝ) (g : Disorder n) :
    squareError β g = Matrix.of (coupling (fun e => g e^2-β^2/n)) -
      Matrix.diagonal (fun _ => β^2/(n:ℝ)) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [squareError,coupling]
  · rcases lt_or_gt_of_ne h with hij | hij
    · simp [squareError,coupling,hij,h]
    · simp [squareError,coupling,hij,not_lt_of_gt hij,h]

lemma squareError_symmetric {n : ℕ} (β : ℝ) (g : Disorder n) (i j : Fin n) :
    squareError β g i j = squareError β g j i := by
  simp only [squareError,coupling_symm g i j]

theorem squareError_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (law β) (fun n => {g | u <
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (squareError β g)‖}) := by
  have h := square_matrix_rare β (half_pos hu)
  have ht : Tendsto (fun n : ℕ => β^2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply h.mono
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hu))] with n hn
  intro g hg
  change u/2 < _
  apply lt_of_not_ge
  intro hsmall
  have hd := matrix_diagonal_opNorm_le (n := n) (fun _ => β^2/(n:ℝ))
    (β^2/(n:ℝ)) (by positivity) (fun _ => le_of_eq (abs_of_nonneg (by positivity)))
  have hh : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (squareError β g)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => g e^2-β^2/n))‖+
      β^2/(n:ℝ) := by
    rw [squareError_decomposition,map_sub]
    exact (norm_sub_le _ _).trans (add_le_add_right hd _)
  change u < _ at hg
  change _ ≤ u/2 at hsmall
  linarith only [hh,hg,hsmall,hn]

lemma coupling_sq {n : ℕ} (g : Disorder n) (i j : Fin n) :
    coupling g i j^2 = coupling (fun e => g e^2) i j := by
  unfold coupling
  split_ifs <;> simp

lemma affine_square_row_bound {n : ℕ} (hn : 0<n) (β : ℝ) (z : Disorder n)
    {C : ℝ} (hrow : ∀ i, (∑ e ∈ incidentEdges i, z e^2)/(n:ℝ) ≤ C) (i : Fin n) :
    ∑ j, coupling (affineDisorder β z) i j^2 ≤ 2*β^2*C+2*β^4 := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hc : ((incidentEdges i).card:ℝ) ≤ n := by exact_mod_cast incidentEdges_card_le i
  have hne : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have ht : ∑ e ∈ incidentEdges i, affineDisorder β z e^2 ≤
      (2*β^2)*((∑ e ∈ incidentEdges i, z e^2)/(n:ℝ))+
        ((incidentEdges i).card:ℝ)*(2*β^4/(n:ℝ)^2) := by
    calc
      _ ≤ ∑ e ∈ incidentEdges i, (2*(β/sqrt n)^2*z e^2+2*(β^2/(n:ℝ))^2) := by
        apply Finset.sum_le_sum
        intro e _
        dsimp only [affineDisorder]
        nlinarith only [sq_nonneg ((β/sqrt n)*z e-β^2/n)]
      _ = _ := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum]
        simp only [Finset.sum_const,nsmul_eq_mul,div_pow,sq_sqrt (Nat.cast_nonneg n)]
        ring
  have hb : ((incidentEdges i).card:ℝ)*(2*β^4/(n:ℝ)^2) ≤ 2*β^4 := by
    calc
      _ ≤ (n:ℝ)*(2*β^4/(n:ℝ)^2) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (2*β^4)/(n:ℝ) := by field_simp
      _ ≤ _ := div_le_self (by positivity) hn1
  simp_rw [coupling_sq]
  rw [sum_coupling_row]
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_left (hrow i) (by positivity)) hb)

theorem square_rows_bounded (β : ℝ) :
    ∃ C : ℝ, 0<C ∧ ExponentiallyRare (law β)
      (fun n => {g | ∃ i : Fin n, C < ∑ j, coupling g i j^2}) := by
  obtain ⟨C,hC,hrows⟩ := gaussian_rows_square_bounded
  let D := 2*β^2*C+2*β^4+1
  have hD : 0<D := by dsimp [D]; positivity
  have ht : ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | ∃ i : Fin n, D < ∑ j, coupling (affineDisorder β z) i j^2}) := by
    apply hrows.mono
    filter_upwards [eventually_gt_atTop 0] with n hn
    rintro z ⟨i,hi⟩
    by_contra hnot
    have hrow : ∀ j, (∑ e ∈ incidentEdges j, z e^2)/(n:ℝ) ≤ C := by
      intro j
      exact le_of_not_gt (fun hj => hnot ⟨j,hj⟩)
    have hs := affine_square_row_bound hn β z hrow i
    dsimp [D] at hi
    linarith only [hs,hi]
  obtain ⟨A,c,hA,hc,hb⟩ := ht
  refine ⟨D,hD,A,c,hA,hc,?_⟩
  filter_upwards [hb,eventually_gt_atTop 0] with n hn hn0
  have hm : MeasurableSet {g : Disorder n | ∃ i : Fin n, D < ∑ j, coupling g i j^2} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    exact (continuous_finsetSum _ (fun j _ => (continuous_coupling i j).pow 2)).measurable
  rw [←(affineDisorder_hasLaw hn0 β).measure_eq hm]
  exact hn

lemma squareError_absolute_row {n : ℕ} (β : ℝ) (g : Disorder n) (i : Fin n) :
    ∑ j, |squareError β g i j| ≤ (∑ j, coupling g i j^2)+β^2 := by
  calc
    _ ≤ ∑ j, (coupling g i j^2+β^2/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (by positivity)])
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := i.isLt; omega)
      rw [mul_div_cancel₀ _ hn]

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_WeightedKernelOperator
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet

theorem weighted_square_operator_rare {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (β : ℝ) (G : X × X → ℝ) (hG : Continuous G) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (law β) (fun n => {g | ∃ x : Fin n → X,
      u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (Matrix.of fun i j => squareError β g i j*G (x i,x j))‖}) := by
  obtain ⟨C,hC,hrow⟩ := square_rows_bounded β
  obtain ⟨δ,hδ,hmask⟩ := continuous_kernel_insertion G hG
    (show 0≤C+β^2 by positivity) hu
  apply (hrow.union (squareError_rare β hδ)).mono
  refine Filter.Eventually.of_forall ?_
  rintro n g ⟨x,hx⟩
  by_contra hn
  have hr : ∀ i, ∑ j, |squareError β g i j| ≤ C+β^2 := by
    intro i
    exact (squareError_absolute_row β g i).trans (add_le_add_left
      (le_of_not_gt (fun hi => hn (Or.inl ⟨i,hi⟩))) _)
  have hc : ∀ j, ∑ i, |squareError β g i j| ≤ C+β^2 := by
    intro j
    simpa only [squareError_symmetric β g] using hr j
  have hd : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (squareError β g)‖ ≤ δ :=
    le_of_not_gt (fun h => hn (Or.inr h))
  exact (not_lt_of_ge (hmask (squareError β g) hr hc hd x)) hx

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_ExponentialProducts
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace SKRatioClock.Regression

lemma ExponentiallyRare.prod_snd {H K : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (K n)]
    {ρ : ∀ n, Measure (H n)} (μ : ∀ n, Measure (K n))
    [∀ n, SFinite (ρ n)] [∀ n, IsProbabilityMeasure (μ n)]
    {A : ∀ n, Set (H n)} (hA : ExponentiallyRare ρ A) :
    ExponentiallyRare (fun n => (μ n).prod (ρ n)) (fun n => Prod.snd ⁻¹' A n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he] with n hn
  have heq : (Prod.snd ⁻¹' A n : Set (K n × H n)) = univ ×ˢ A n := by ext; simp
  rw [heq,Measure.prod_prod,measure_univ,one_mul]
  exact hn

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_PlantedEntries
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

lemma affine_coordinates_max_rare (β : ℝ) {u : ℝ} (hu : 0<u)
    (I : ℕ → Type) [∀ n, Fintype (I n)] {D : ℝ} (hD : 0<D) (k : ℕ)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (I n):ℝ) ≤ D*(n:ℝ)^k) :
    ExponentiallyRare (fun n => standardArrayLaw (I n))
      (fun n => {z | ∃ i, u < |β/sqrt n*z i+β^2/(n:ℝ)|}) := by
  by_cases hβ : β=0
  · apply (exponentiallyRare_empty (fun n => standardArrayLaw (I n))).mono
    refine Eventually.of_forall ?_
    intro n z hz
    obtain ⟨i,hi⟩ := hz
    simp [hβ] at hi
    linarith
  have hβ2 : 0<β^2 := sq_pos_of_ne_zero hβ
  have hc : 0<u^2/(8*β^2) := by positivity
  have ht := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (β^2)
  have he : ∀ᶠ n in atTop, ∀ i : I n,
      standardArrayLaw (I n) {z | u < |β/sqrt n*z i+β^2/(n:ℝ)|} ≤
        ENNReal.ofReal (2*exp (-(u^2/(8*β^2))*n)) := by
    filter_upwards [eventually_ge_atTop 1,
      ht.eventually (gt_mem_nhds (by linarith : (0:ℝ)<u/2))] with n hn hm i
    have hn0 : 0<n := lt_of_lt_of_le (by norm_num) hn
    have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn0
    have hsn : sqrt (n:ℝ)≠0 := (sqrt_pos.mpr hnr).ne'
    have hbpos : 0 < |β| := abs_pos.mpr hβ
    have hs := subgaussian_abs_tail
      (gaussian_hasSubgaussianMGF (coordinate_hasLaw i))
      (u*sqrt n/(2*|β|)) (by positivity)
    have hex : -(u*sqrt n/(2*|β|))^2/(2*(1:ℝ)) = -(u^2/(8*β^2))*(n:ℝ) := by
      simp only [div_pow,mul_pow,sq_sqrt hnr.le,sq_abs]
      field_simp
      ring
    simp only [NNReal.coe_one,hex] at hs
    rw [←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num)] at hs
    refine (measure_mono (show {z : I n → ℝ | u < |β/sqrt n*z i+β^2/(n:ℝ)|} ⊆
      {z : I n → ℝ | u*sqrt n/(2*|β|) ≤ |z i|} from ?_)).trans hs
    intro z hz
    change u < |β/sqrt n*z i+β^2/(n:ℝ)| at hz
    have hb := abs_add_le (β/sqrt n*z i) (β^2/(n:ℝ))
    rw [abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ)),abs_mul,abs_div,
      abs_of_nonneg (sqrt_nonneg _)] at hb
    have hi : u/2 ≤ |β|/sqrt n*|z i| := by
      linarith
    apply (div_le_iff₀ (by positivity : 0<2*|β|)).mpr
    have hii := (le_div_iff₀ (sqrt_pos.mpr hnr)).mp
      (show u/2 ≤ |β| *|z i|/sqrt n by simpa only [div_mul_eq_mul_div] using hi)
    nlinarith only [hii]
  have hr := exponentiallyRare_iUnion_polynomial (fun n => standardArrayLaw (I n))
    (fun n i => {z | u < |β/sqrt n*z i+β^2/(n:ℝ)|}) hc
    (by norm_num : (0:ℝ)<2) hD k hcard he
  apply hr.mono
  exact Eventually.of_forall (fun n z hz => mem_iUnion.mpr hz)

lemma affine_max_entry_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | ∃ e : Edge n, u < |affineDisorder β z e|}) := by
  apply affine_coordinates_max_rare β hu (Edge) (D := 1) (by norm_num) 2
  refine Eventually.of_forall ?_
  intro n
  have hc := Fintype.card_subtype_le (fun e : Fin n × Fin n => e.1<e.2)
  have hh : Fintype.card (Edge n)≤n*n := by simpa [Edge] using hc
  have hreal : (Fintype.card (Edge n):ℝ) ≤ (n:ℝ)*(n:ℝ) := by exact_mod_cast hh
  simpa only [one_mul,pow_two] using hreal

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PlantedGOE
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma augmentedDisorder_gaussian (β : ℝ) :
    HasGaussianLaw (augmentedDisorder (n := n) β) (standardArrayLaw (Fin n × Fin n)) := by
  let L : ((Fin n × Fin n) → ℝ) →L[ℝ] Disorder n :=
    β • ContinuousLinearMap.pi (fun e : Edge n => (entryCLM e.1.1 e.1.2).comp (goeCLM n))
  have h := gaussian_add_constant (coordinates_gaussian.map_fun L) (fun _ : Edge n => β^2/(n:ℝ))
  apply h.congr
  exact Eventually.of_forall (fun g => by
    funext e
    simp only [L,smul_apply,
      ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,entryCLM_apply,
      goeCLM_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,augmentedDisorder,augmented])

lemma augmented_mean (β : ℝ) (i j : Fin n) :
    (∫ g, augmented β g i j ∂standardArrayLaw (Fin n × Fin n)) = β^2/(n:ℝ) := by
  unfold augmented
  rw [integral_add (((goe_gaussian n).eval i |>.eval j).integrable.const_mul β)
    (integrable_const _),integral_const_mul,goe_entry_mean]
  simp

lemma augmented_covariance (hn : 0 < n) (β : ℝ) (i j k l : Fin n) :
    cov[fun g => augmented β g i j, fun g => augmented β g k l;
      standardArrayLaw (Fin n × Fin n)] =
      (β^2/(n:ℝ))*((if i=k ∧ j=l then 1 else 0)+(if i=l ∧ j=k then 1 else 0)) := by
  unfold augmented
  rw [covariance_add_const_left (((goe_gaussian n).eval i |>.eval j).integrable.const_mul β),
    covariance_add_const_right (((goe_gaussian n).eval k |>.eval l).integrable.const_mul β),
    covariance_const_mul_left,covariance_const_mul_right,goe_entry_covariance hn]
  ring

lemma augmentedDisorder_covariance (hn : 0 < n) (β : ℝ) (e f : Edge n) :
    cov[fun g => augmentedDisorder β g e,fun g => augmentedDisorder β g f;
      standardArrayLaw (Fin n × Fin n)] = if e=f then β^2/(n:ℝ) else 0 := by
  unfold augmentedDisorder
  rw [augmented_covariance hn]
  have heq : e=f ↔ e.1.1=f.1.1 ∧ e.1.2=f.1.2 := by
    simp only [Subtype.ext_iff,Prod.ext_iff]
  have hcross : ¬(e.1.1=f.1.2 ∧ e.1.2=f.1.1) := by
    rintro ⟨h₁,h₂⟩
    have h := e.2
    rw [h₁,h₂] at h
    exact lt_asymm f.2 h
  simp only [ite_eq_right hcross,add_zero,←heq]
  split_ifs <;> simp

theorem augmentedDisorder_hasLaw (hn : 0 < n) (β : ℝ) :
    HasLaw (augmentedDisorder (n := n) β) (law β n) (standardArrayLaw (Fin n × Fin n)) := by
  have hg := augmentedDisorder_gaussian (n := n) β
  have hl (e : Edge n) : HasLaw (fun g => augmentedDisorder β g e)
      (gaussianReal (β^2/(n:ℝ)) (Real.toNNReal (β^2/(n:ℝ))))
      (standardArrayLaw (Fin n × Fin n)) := by
    refine ⟨(hg.eval e).aemeasurable,?_⟩
    rw [(hg.eval e).map_eq_gaussianReal,show (∫ g, augmentedDisorder β g e
      ∂standardArrayLaw (Fin n × Fin n)) = β^2/(n:ℝ) from augmented_mean β _ _,
      ←covariance_self (hg.eval e).aemeasurable,augmentedDisorder_covariance hn,ite_eq_left rfl]
  exact iIndepFun.hasLaw_pi hl (hg.iIndepFun_of_covariance_eq_zero
    (fun e f h => by rw [augmentedDisorder_covariance hn,ite_eq_right h]))

lemma coupling_augmentedDisorder (β : ℝ) (g : (Fin n × Fin n) → ℝ) :
    Matrix.of (coupling (augmentedDisorder β g)) = augmented β g - Matrix.diagonal (fun i => augmented β g i i) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [coupling]
  · rcases lt_or_gt_of_ne h with hij | hij
    · simp [coupling,hij,h,augmentedDisorder]
    · simp [coupling,hij,not_lt_of_gt hij,h,augmentedDisorder,augmented,goe,add_comm]

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_WeightedGaussianSquares
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma bounded_weights_sum_square {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    {A : ℝ} (hA : 0≤A) (ha : ∀ i∈s, |a i|≤A) {n : ℕ} (hn : s.card≤n) :
    ∑ i∈s, a i^2 ≤ (n:ℝ)*A^2 := by
  calc
    _ ≤ ∑ _i∈s, A^2 := Finset.sum_le_sum (fun i hi => by
      nlinarith [sq_abs (a i),ha i hi,abs_nonneg (a i)])
    _ = (s.card:ℝ)*A^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (sq_nonneg _)

lemma weighted_centered_clip_tail {ι : Type*} [Fintype ι]
    (s : Finset ι) (a : ι → ℝ) {A R : ℝ} (hA : 0<A) (hR : 0<R)
    (ha : ∀ i∈s, |a i| ≤ A) {n : ℕ} (hn : 0<n) (hc : s.card≤n)
    {u : ℝ} (hu : 0≤u) :
    standardArrayLaw ι {z | u ≤ |(∑ i∈s,
      a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ)|} ≤
      2*ENNReal.ofReal (exp (-u^2*(n:ℝ)/(2*A^2*R^4))) := by
  let X (i : ι) (z : ι → ℝ) := clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)
  have hi : iIndepFun X (standardArrayLaw ι) := coordinates_independent.comp
    (fun _ x => clippedSquare R x-(∫ y, clippedSquare R y ∂gaussianReal 0 1))
    (fun _ => ((continuous_clippedSquare R).sub continuous_const).measurable)
  have his := hi.comp (fun i z => a i*z) (fun _ => measurable_const.mul measurable_id)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun his (s := s)
    (fun i _ => (centered_clip_subgaussian hR i).const_mul (a i))
  have hv : (∑ i∈s, (NNReal.mk (a i^2) (sq_nonneg (a i)))*(Real.toNNReal (R^2))^2) ≤
      Real.toNNReal ((n:ℝ)*A^2*R^4) := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_mk,
      Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ (n:ℝ)*A^2*R^4),
      ←Finset.sum_mul,show (R^2)^2=R^4 by ring]
    exact mul_le_mul_of_nonneg_right (bounded_weights_sum_square s a hA.le ha hc) (by positivity)
  have ht := subgaussian_abs_tail (subgaussian_mono hsum hv) (u*n) (by positivity)
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have he (z : ι → ℝ) : (u*(n:ℝ) ≤ |∑ i∈s, a i*X i z|) ↔
      u ≤ |(∑ i∈s, a i*X i z)/(n:ℝ)| := by
    rw [abs_div,abs_of_pos hnR,le_div_iff₀ hnR]
  simp only [Function.comp_apply] at ht
  simp_rw [he] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  rw [Real.coe_toNNReal _ (by positivity : (0:ℝ)≤(n:ℝ)*A^2*R^4)]
  field_simp [hnR.ne']

lemma weighted_square_truncation_error {ι : Type*} (s : Finset ι) (a z : ι → ℝ)
    {A R : ℝ} (hA : 0≤A) (hR : 0≤R) (ha : ∀ i∈s, |a i|≤A)
    {n : ℕ} (hn : 0<n) (hc : s.card≤n) :
    |(∑ i∈s, a i*(z i^2-1))/(n:ℝ)-
      (∑ i∈s, a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ)| ≤
      A*((∑ i∈s, squareTail R (z i))/(n:ℝ)+(∫ x, squareTail R x ∂gaussianReal 0 1)) := by
  let m := ∫ x, clippedSquare R x ∂gaussianReal 0 1
  let t := ∫ x, squareTail R x ∂gaussianReal 0 1
  have ht : 0≤t := integral_nonneg (squareTail_nonneg R)
  have hm : |m-1| ≤ t := clippedSquare_mean_error hR
  have he : (∑ i∈s, a i*(z i^2-1)) - (∑ i∈s, a i*(clippedSquare R (z i)-m)) =
      ∑ i∈s, a i*(z i^2-clippedSquare R (z i)+(m-1)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : |(∑ i∈s, a i*(z i^2-1)) - (∑ i∈s, a i*(clippedSquare R (z i)-m))| ≤
      A*((∑ i∈s, squareTail R (z i))+(n:ℝ)*t) := by
    rw [he]
    calc
      _ ≤ ∑ i∈s, |a i*(z i^2-clippedSquare R (z i)+(m-1))| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ i∈s, A*(squareTail R (z i)+t) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        apply mul_le_mul (ha i hi) _ (abs_nonneg _) hA
        apply (abs_add_le _ _).trans
        rw [abs_of_nonneg (square_sub_clip_nonneg R (z i))]
        exact add_le_add (square_sub_clip_le hR _) hm
      _ = A*((∑ i∈s, squareTail R (z i))+(s.card:ℝ)*t) := by
        simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hc : (s.card:ℝ)≤n) ht) _) hA
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  rw [←sub_div,abs_div,abs_of_pos hnR]
  apply (div_le_div_of_nonneg_right hb hnR.le).trans_eq
  dsimp only [t]
  field_simp

theorem weighted_standard_square_tail {A u : ℝ} (hA : 0≤A) (hu : 0<u) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ι : Type} [Fintype ι] (s : Finset ι) (a : ι → ℝ),
      (∀ i∈s, |a i|≤A) → ∀ {n : ℕ}, 0<n → s.card≤n →
      standardArrayLaw ι {z | u ≤ |(∑ i∈s, a i*(z i^2-1))/(n:ℝ)|} ≤
        ENNReal.ofReal (3*exp (-c*n)) := by
  let d := u/(4*(A+1))
  have hd : 0<d := by dsimp [d]; positivity
  obtain ⟨R,c,hR,hc,hm,hrow⟩ := gaussian_squareTail_row_bound hd
  let c' := (u/2)^2/(2*(A+1)^2*R^4)
  have hc' : 0 < c' := by dsimp [c']; positivity
  refine ⟨min c c',lt_min hc hc',?_⟩
  intro ι _ s a ha n hn hs
  let E : Set (ι → ℝ) := {z | d ≤ (∑ i∈s, squareTail R (z i))/(n:ℝ)}
  let F : Set (ι → ℝ) := {z | u/2 ≤ |(∑ i∈s,
    a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ)|}
  have hsub : {z | u ≤ |(∑ i∈s, a i*(z i^2-1))/(n:ℝ)|} ⊆ E ∪ F := by
    intro z hz
    by_cases he : z∈E
    · exact Or.inl he
    apply Or.inr
    change u/2 ≤ _
    have hh := weighted_square_truncation_error s a z hA hR.le ha hn hs
    have hze : (∑ i∈s, squareTail R (z i))/(n:ℝ) < d := not_le.mp he
    have haerr : A*(2*d) ≤ u/2 := by
      dsimp [d]
      rw [show 2*(u/(4*(A+1)))=u/(2*(A+1)) by field_simp; ring,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(A+1))).mpr
      nlinarith
    have hb := mul_le_mul_of_nonneg_left (show
      (∑ i∈s, squareTail R (z i))/(n:ℝ)+(∫ x, squareTail R x ∂gaussianReal 0 1) ≤ 2*d
      by linarith) hA
    have htri := abs_add_le
      ((∑ i∈s, a i*(z i^2-1))/(n:ℝ)-
        (∑ i∈s, a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ))
      ((∑ i∈s, a i*(clippedSquare R (z i)-(∫ x, clippedSquare R x ∂gaussianReal 0 1)))/(n:ℝ))
    simp only [sub_add_cancel] at htri
    change u ≤ _ at hz
    linarith only [hz,hh,hb,haerr,htri]
  have hE := hrow s hn hs
  have hF := weighted_centered_clip_tail s a (by positivity : 0<A+1) hR
    (fun i hi => (ha i hi).trans (by linarith)) hn hs (by positivity : 0≤u/2)
  have hcn : exp (-c*n) ≤ exp (-min c c'*n) := exp_le_exp.mpr (by
    have := min_le_left c c'; nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hcn' : exp (-c'*n) ≤ exp (-min c c'*n) := exp_le_exp.mpr (by
    have := min_le_right c c'; nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hc'id : -(u/2)^2*(n:ℝ)/(2*(A+1)^2*R^4) = -c'*n := by dsimp [c']; ring
  rw [hc'id] at hF
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le E F
    _ ≤ ENNReal.ofReal (exp (-c*n))+2*ENNReal.ofReal (exp (-c'*n)) := add_le_add hE hF
    _ ≤ ENNReal.ofReal (exp (-min c c'*n))+2*ENNReal.ofReal (exp (-min c c'*n)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hcn) (mul_le_mul_right (ENNReal.ofReal_le_ofReal hcn') _)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]; norm_num; ring

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_ConditionalGaussianSquares
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma weighted_square_product_tail {A u c : ℝ}
    (ht : ∀ {ι : Type} [Fintype ι] (s : Finset ι) (a : ι → ℝ),
      (∀ i∈s, |a i|≤A) → ∀ {n : ℕ}, 0<n → s.card≤n →
      standardArrayLaw ι {z | u ≤ |(∑ i∈s, a i*(z i^2-1))/(n:ℝ)|} ≤
        ENNReal.ofReal (3*exp (-c*n)))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type} [Fintype ι] (s : Finset ι) (a : Ω → ι → ℝ)
    (hma : ∀ i, Measurable (fun ω => a ω i)) (ha : ∀ ω i, i∈s → |a ω i|≤A)
    {n : ℕ} (hn : 0<n) (hc : s.card≤n) :
    (μ.prod (standardArrayLaw ι)) {p | u ≤ |(∑ i∈s, a p.1 i*(p.2 i^2-1))/(n:ℝ)|} ≤
      ENNReal.ofReal (3*exp (-c*n)) := by
  have hE : MeasurableSet {p : Ω × (ι → ℝ) |
      u ≤ |(∑ i∈s, a p.1 i*(p.2 i^2-1))/(n:ℝ)|} := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun i _ => ((hma i).comp measurable_fst).mul
      (((measurable_pi_apply i).comp measurable_snd).pow_const 2 |>.sub measurable_const))
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (3*exp (-c*n)) ∂μ :=
      lintegral_mono (fun ω => ht s (a ω) (ha ω) hn hc)
    _ = _ := by simp

theorem weighted_square_conditioned_tail {A u : ℝ} (hA : 0≤A) (hu : 0<u) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ι : Type} [Fintype ι] (s : Finset ι)
      (a : ({i // i∉s} → ℝ) → s → ℝ),
      (∀ i, Measurable (fun y => a y i)) → (∀ y i, |a y i|≤A) →
      ∀ {n : ℕ}, 0<n → s.card≤n →
      standardArrayLaw ι {z | u ≤ |(∑ i : s,
        a (fun j => z j) i * (z i^2-1))/(n:ℝ)|} ≤
          ENNReal.ofReal (3*exp (-c*n)) := by
  classical
  obtain ⟨c,hc,ht⟩ := weighted_standard_square_tail hA hu
  refine ⟨c,hc,?_⟩
  intro ι _ s a hm ha n hn hs
  let E : Set (({i // i∉s} → ℝ) × (s → ℝ)) :=
    {p | u ≤ |(∑ i : s, a p.1 i*(p.2 i^2-1))/(n:ℝ)|}
  have hE : MeasurableSet E := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun i _ => ((hm i).comp measurable_fst).mul
      (((measurable_pi_apply i).comp measurable_snd).pow_const 2 |>.sub measurable_const))
  have hp := measurePreserving_piEquivPiSubtypeProd
    (fun _ : ι => gaussianReal 0 1) (fun i => i∈s)
  have hp' := Measure.measurePreserving_swap.comp hp
  have he : {z : ι → ℝ | u ≤ |(∑ i : s, a (fun j => z j) i*(z i^2-1))/(n:ℝ)|} =
      (fun z => ((fun j : {i // i∉s} => z j), (fun j : s => z j))) ⁻¹' E := rfl
  rw [he]
  have hmap : MeasurePreserving (fun z : ι → ℝ =>
      ((fun j : {i // i∉s} => z j), (fun j : s => z j)))
      (standardArrayLaw ι) ((standardArrayLaw {i // i∉s}).prod (standardArrayLaw s)) := by
    convert! hp' using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [standardArrayLaw]
    congr 1
    congr 1
    exact Subsingleton.elim _ _

  rw [hmap.measure_preimage hE.nullMeasurableSet]
  exact weighted_square_product_tail ht (standardArrayLaw {i // i∉s})
    Finset.univ a hm (fun y i _ => ha y i) hn (by simpa using hs)

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_ConditionalAffineSquares
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma weighted_square_conditioned_product_tail {A u : ℝ} (hA : 0≤A) (hu : 0<u) :
    ∃ c : ℝ, 0 < c ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type} [Fintype ι]
      (s : Finset ι) (a : Ω → ({i // i∉s} → ℝ) → s → ℝ),
      (∀ i, Measurable (fun p : Ω × ({i // i∉s} → ℝ) => a p.1 p.2 i)) →
      (∀ ω y i, |a ω y i|≤A) → ∀ {n : ℕ}, 0<n → s.card≤n →
      (μ.prod (standardArrayLaw ι)) {p | u ≤ |(∑ i : s,
        a p.1 (fun j => p.2 j) i * (p.2 i^2-1))/(n:ℝ)|} ≤
          ENNReal.ofReal (3*exp (-c*n)) := by
  obtain ⟨c,hc,ht⟩ := weighted_square_conditioned_tail hA hu
  refine ⟨c,hc,?_⟩
  intro Ω _ μ _ ι _ s a hm ha n hn hs
  have hE : MeasurableSet {p : Ω × (ι → ℝ) | u ≤ |(∑ i : s,
      a p.1 (fun j => p.2 j) i * (p.2 i^2-1))/(n:ℝ)|} := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    have hr : Measurable (fun p : Ω × (ι → ℝ) => (p.1, fun j : {i // i∉s} => p.2 j)) := by
      fun_prop
    exact ((hm i).comp hr).mul
      (((measurable_pi_apply (i : ι)).comp measurable_snd).pow_const 2 |>.sub measurable_const)
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (3*exp (-c*n)) ∂μ := by
      apply lintegral_mono
      intro ω
      exact ht s (a ω) (fun i => (hm i).comp (measurable_const.prodMk measurable_id)) (ha ω) hn hs
    _ = _ := by simp

lemma average_abs_le_square_add_one {ι : Type*} [Fintype ι] (z : ι → ℝ)
    {n : ℕ} (hn : Fintype.card ι≤n) :
    (∑ i, |z i|)/(n:ℝ) ≤ (∑ i, z i^2)/(n:ℝ)+1 := by
  by_cases hn0 : n=0
  · simp [hn0]
  have hsum : ∑ i, |z i| ≤ (∑ i, z i^2)+(n:ℝ) := by
    calc
      _ ≤ ∑ i, (z i^2+1) := Finset.sum_le_sum (fun i _ => by
        nlinarith [sq_nonneg (|z i|-1),sq_abs (z i),abs_nonneg (z i)])
      _ = (∑ i, z i^2)+(Fintype.card ι:ℝ) := by simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add_right (by exact_mod_cast hn : (Fintype.card ι:ℝ) ≤ n) _
  have h := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : (0:ℝ)≤n)
  simpa [add_div,hn0] using h

lemma weighted_affine_square_error {ι : Type*} [Fintype ι]
    (β : ℝ) (a z : ι → ℝ) {A C : ℝ} (hA : 0≤A)
    (ha : ∀ i, |a i|≤A) {n : ℕ} (hn : 0<n) (hs : Fintype.card ι≤n)
    (hz : (∑ i, z i^2)/(n:ℝ)≤C) :
    |(∑ i, a i*((β/sqrt n*z i+β^2/(n:ℝ))^2-β^2/n))-
      β^2*((∑ i, a i*(z i^2-1))/(n:ℝ))| ≤
      A*(|2*β^3/sqrt n| *(C+1)+β^4/n) := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hsR : sqrt (n:ℝ) ≠ 0 := (sqrt_pos.mpr hnR).ne'
  have he (x : ℝ) : (β/sqrt n*x+β^2/(n:ℝ))^2-β^2/n =
      β^2*((x^2-1)/(n:ℝ))+(2*β^3/sqrt n)*(x/n)+β^4/(n:ℝ)^2 := by
    rw [add_sq,mul_pow,div_pow,sq_sqrt hnR.le]
    field_simp
    ring
  have hzs : (∑ i, |z i|)/(n:ℝ) ≤ C+1 :=
    (average_abs_le_square_add_one z hs).trans (add_le_add_left hz 1)
  have heq : (∑ i, a i*((β/sqrt n*z i+β^2/(n:ℝ))^2-β^2/n))-
      β^2*((∑ i, a i*(z i^2-1))/(n:ℝ)) =
      ∑ i, a i*((2*β^3/sqrt n)*(z i/n)+β^4/(n:ℝ)^2) := by
    simp_rw [he]
    rw [Finset.sum_div,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i, |a i*((2*β^3/sqrt n)*(z i/n)+β^4/(n:ℝ)^2)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i, A*(|2*β^3/sqrt n| *(|z i|/n)+β^4/(n:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul (ha i) _ (abs_nonneg _) hA
      apply (abs_add_le _ _).trans_eq
      rw [abs_mul,abs_div (z i),abs_of_pos hnR,abs_of_nonneg (by positivity : 0≤β^4/(n:ℝ)^2)]
    _ = A*(|2*β^3/sqrt n| *((∑ i, |z i|)/n)+(Fintype.card ι:ℝ)*(β^4/(n:ℝ)^2)) := by
      simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul,mul_div_assoc]
    _ ≤ A*(|2*β^3/sqrt n| *(C+1)+(n:ℝ)*(β^4/(n:ℝ)^2)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add (mul_le_mul_of_nonneg_left hzs (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hs : (Fintype.card ι:ℝ)≤n) (by positivity))
    _ = _ := by
      have hh : (n:ℝ)*(β^4/(n:ℝ)^2)=β^4/n := by field_simp [hnR.ne']
      rw [hh]

theorem weighted_affine_conditioned_tail (β C : ℝ) {A u : ℝ}
    (hA : 0≤A) (hu : 0<u) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {ι : Type} [Fintype ι] (s : Finset ι)
      (a : Ω → ({i // i∉s} → ℝ) → s → ℝ), s.card≤n →
      (∀ i, Measurable (fun p : Ω × ({i // i∉s} → ℝ) => a p.1 p.2 i)) →
      (∀ ω y i, |a ω y i|≤A) →
      (μ.prod (standardArrayLaw ι)) {p |
        u < |∑ i : s, a p.1 (fun j => p.2 j) i *
          ((β/sqrt n*p.2 i+β^2/(n:ℝ))^2-β^2/n)| ∧
        (∑ i : s, p.2 i^2)/(n:ℝ) ≤ C} ≤
          ENNReal.ofReal (3*exp (-c*n)) := by
  let d := u/(2*(β^2+1))
  have hd : 0<d := by dsimp [d]; positivity
  obtain ⟨c,hc,ht⟩ := weighted_square_conditioned_product_tail hA hd
  have hconv : Tendsto (fun n : ℕ => A*(|2*β^3/sqrt n| *(C+1)+β^4/n)) atTop (𝓝 0) := by
    have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
    have h₁ := ((tendsto_const_nhds (x := 2*β^3)).div_atTop (tendsto_sqrt_atTop.comp hn)).abs.mul_const (C+1)
    have h₂ := (tendsto_const_nhds (x := β^4)).div_atTop hn
    simpa only [abs_zero,zero_mul,zero_add,mul_zero,Function.comp_def] using (h₁.add h₂).const_mul A
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_gt_atTop 0,hconv.eventually (gt_mem_nhds (half_pos hu))] with n hn hb
  intro Ω _ μ _ ι _ s a hs hm ha
  apply (measure_mono (t := {p : Ω × (ι → ℝ) | d ≤ |(∑ i : s,
    a p.1 (fun j => p.2 j) i*(p.2 i^2-1))/(n:ℝ)|}) ?_).trans (ht μ s a hm ha hn hs)
  rintro p ⟨hp,hrow⟩
  change d ≤ _
  apply le_of_not_gt
  intro hsmall
  have hh := weighted_affine_square_error β (a p.1 (fun j => p.2 j)) (fun i : s => p.2 i)
    hA (ha _ _) hn (by simpa using hs) hrow
  have hs' : β^2*|(∑ i : s, a p.1 (fun j => p.2 j) i*(p.2 i^2-1))/(n:ℝ)| ≤ u/2 := by
    apply (mul_le_mul_of_nonneg_left hsmall.le (sq_nonneg β)).trans
    dsimp only [d]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(β^2+1))).mpr
    nlinarith
  have htri := abs_sub_le (∑ i : s, a p.1 (fun j => p.2 j) i *
    ((β/sqrt n*p.2 i+β^2/(n:ℝ))^2-β^2/n))
    (β^2*((∑ i : s, a p.1 (fun j => p.2 j) i*(p.2 i^2-1))/(n:ℝ))) 0
  simp only [sub_zero,abs_mul,abs_of_nonneg (sq_nonneg β)] at htri
  linarith only [hp,hh,hb,hs',htri]

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RowGeometry
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Set Real
namespace SKRatio.Planted
open MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma mem_incident (i : Fin n) (e : Edge n) :
    e∈incidentEdges i ↔ e.1.1=i ∨ e.1.2=i := by simp [incidentEdges]

lemma otherEnd_ne {i : Fin n} {e : Edge n} (he : e∈incidentEdges i) :
    otherEnd i e ≠ i := by
  have h := (mem_incident i e).mp he
  unfold otherEnd
  split_ifs with h₁
  · have hlt := e.2
    rw [h₁] at hlt
    exact ne_of_gt hlt
  · exact h₁

lemma coupling_otherEnd {i : Fin n} {e : Edge n} (g : Disorder n)
    (he : e∈incidentEdges i) : coupling g i (otherEnd i e)=g e := by
  have h := (mem_incident i e).mp he
  rcases h with h | h
  · simp only [otherEnd,ite_eq_left h]
    subst i
    simp [coupling,e.2]
  · have h₁ : e.1.1 ≠ i := by rw [←h]; exact ne_of_lt e.2
    simp only [otherEnd,ite_eq_right h₁]
    subst i
    simp [coupling,not_lt_of_gt e.2,e.2]

lemma sum_coupling_weighted_row (g : Disorder n) (i : Fin n) (f : Fin n → ℝ) :
    ∑ j, coupling g i j*f j = ∑ e∈incidentEdges i, g e*f (otherEnd i e) := by
  have he := coupling_bilinear (fun j => if j=i then 1 else 0) f g
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true] at he
  rw [he,incidentEdges,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hne : e.1.1≠e.1.2 := ne_of_lt e.2
  by_cases h₁ : e.1.1=i <;> by_cases h₂ : e.1.2=i <;>
    simp_all [otherEnd,mul_comm]

lemma coupling_eraseRow (i : Fin n) (g : Disorder n) (j k : Fin n) :
    coupling (eraseRow i g) j k = if j=i ∨ k=i then 0 else coupling g j k := by
  unfold coupling eraseRow
  split_ifs <;> simp_all [mem_incident]

lemma diagonalField_eraseRow (ζ : Fin n → ℝ) (g : Disorder n) (i j : Fin n)
    (hji : j≠i) :
    diagonalField ζ g j-diagonalField ζ (eraseRow i g) j = coupling g i j := by
  have h (k : Fin n) : coupling g j k - coupling (eraseRow i g) j k =
      if k=i then coupling g j i else 0 := by
    rw [coupling_eraseRow]
    by_cases hk : k=i <;> simp [hji,hk]
  simp only [diagonalField,add_sub_add_left_eq_sub,←Finset.sum_sub_distrib,h,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,coupling_symm g j i]

lemma outsideDisorder_eq (β : ℝ) (i : Fin n) (z : Disorder n) :
    outsideDisorder β i (fun e => z e) = eraseRow i (affineDisorder β z) := by
  funext e
  simp only [outsideDisorder,eraseRow,affineDisorder]
  split_ifs <;> rfl

lemma outside_field_error (β : ℝ) (i : Fin n) (ζ : Fin n → ℝ) (z : Disorder n)
    (e : incidentEdges i) :
    diagonalField ζ (affineDisorder β z) (otherEnd i e) -
      diagonalField ζ (outsideDisorder β i (fun j => z j)) (otherEnd i e) =
        affineDisorder β z e := by
  rw [outsideDisorder_eq,diagonalField_eraseRow ζ _ i _ (otherEnd_ne e.2),coupling_otherEnd _ e.2]

lemma continuous_diagonalField (j : Fin n) :
    Continuous (fun p : (Fin n → ℝ) × Disorder n => diagonalField p.1 p.2 j) := by
  apply ((continuous_apply j).comp continuous_fst).add
  exact continuous_finsetSum _ (fun k _ => (continuous_coupling j k).comp continuous_snd)

lemma continuous_outsideDisorder (β : ℝ) (i : Fin n) :
    Continuous (outsideDisorder β i) := by
  apply continuous_pi
  intro e
  unfold outsideDisorder
  split_ifs <;> fun_prop

lemma continuous_outside_field (β : ℝ) (i j : Fin n) :
    Continuous (fun p : (Fin n → ℝ) × ({e // e∉incidentEdges i} → ℝ) =>
      diagonalField p.1 (outsideDisorder β i p.2) j) :=
  (continuous_diagonalField j).comp (continuous_fst.prodMk ((continuous_outsideDisorder β i).comp continuous_snd))

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_WeightedDiagonalSquares
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real Metric
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

lemma incident_absolute_square_error {n : ℕ} (hn : 0<n) (β : ℝ)
    (z : Disorder n) {C : ℝ}
    (hrow : ∀ i, (∑ e∈incidentEdges i, z e^2)/(n:ℝ) ≤ C) (i : Fin n) :
    ∑ e : incidentEdges i, |affineDisorder β z e^2-β^2/(n:ℝ)| ≤
      2*β^2*C+2*β^4+β^2 := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hc : ((incidentEdges i).card:ℝ) ≤ n := by exact_mod_cast incidentEdges_card_le i
  have hs : ∑ e : incidentEdges i, affineDisorder β z e^2 ≤ 2*β^2*C+2*β^4 := by
    have h := affine_square_row_bound hn β z hrow i
    simp_rw [coupling_sq] at h
    rw [sum_coupling_row] at h
    simpa only [Finset.sum_subtype (incidentEdges i) (fun _ => Iff.rfl)] using h
  calc
    _ ≤ ∑ e : incidentEdges i, (affineDisorder β z e^2+β^2/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro e _
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg (by positivity)])
    _ = (∑ e : incidentEdges i, affineDisorder β z e^2)+
        ((incidentEdges i).card:ℝ)*(β^2/(n:ℝ)) := by simp [Finset.sum_add_distrib]
    _ ≤ (2*β^2*C+2*β^4)+β^2 := by
      apply add_le_add hs
      calc
        _ ≤ (n:ℝ)*(β^2/(n:ℝ)) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := mul_div_cancel₀ _ hnr.ne'

lemma weighted_sum_difference_le {ι : Type*} [Fintype ι]
    (a f g : ι → ℝ) {δ R : ℝ} (hδ : 0≤δ)
    (ha : ∑ i, |a i| ≤ R) (hfg : ∀ i, |f i-g i|≤δ) :
    |(∑ i, a i*f i)-(∑ i, a i*g i)| ≤ δ*R := by
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |a i*f i-a i*g i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |f i-g i| := by simp only [←mul_sub,abs_mul]
    _ ≤ ∑ i, |a i| * δ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hfg i) (abs_nonneg _))
    _ = δ*(∑ i, |a i|) := by rw [←Finset.sum_mul,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left ha hδ

lemma compact_first_mesh {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {δ : ℝ} (hδ : 0<δ) :
    ∃ (s : Finset X) (q : X → s), ∀ x : X, dist x (q x : X) < δ := by
  classical
  obtain ⟨s,_,hs,hcov⟩ := finite_cover_balls_of_compact (X := X) isCompact_univ hδ
  have hnear (x : X) : ∃ y : {z // z∈hs.toFinset}, dist x y<δ := by
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_univ x))
    exact ⟨⟨y,hs.mem_toFinset.mpr hy⟩,hxy⟩
  choose q hq using hnear
  exact ⟨hs.toFinset,q,hq⟩

theorem continuous_weighted_diagonal_rare {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) (b : ℝ → X) {K : ℝ≥0} (hb : LipschitzWith K b)
    (β : ℝ) (μ : ∀ n, Measure (Fin n → ℝ)) [∀ n, IsProbabilityMeasure (μ n)]
    {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => (μ n).prod (standardArrayLaw (Edge n)))
      (fun n => {p | ∃ i : Fin n, ∃ a : X,
        u < |∑ e : incidentEdges i, (affineDisorder β p.2 e^2-β^2/(n:ℝ))*
          G (a,b (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e)))|}) := by
  obtain ⟨C,hC,hrows⟩ := gaussian_rows_square_bounded
  let R := 2*β^2*C+2*β^4+β^2
  have hR : 0≤R := by dsimp [R]; positivity
  let v := u/(2*(R+1))
  have hv : 0<v := by dsimp [v]; positivity
  have hvR : v*R ≤ u/2 := by
    dsimp [v]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<2*(R+1))).mpr
    nlinarith only [hu.le]
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hG) v hv
  obtain ⟨s,q,hq⟩ := compact_first_mesh (X := X) hδ
  obtain ⟨A,hA⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  have hA0 : 0≤A := (abs_nonneg (G (b 0,b 0))).trans (by
    simpa only [Real.norm_eq_abs] using hA (b 0,b 0) (mem_univ _))
  have hAb (x y : X) : |G (x,y)|≤A := by
    simpa only [Real.norm_eq_abs] using hA (x,y) (mem_univ _)
  obtain ⟨c,hc,ht⟩ := weighted_affine_conditioned_tail β C hA0 (half_pos hu)
  let bad (a : s) (n : ℕ) : Set ((Fin n → ℝ) × Disorder n) :=
    ⋃ i : Fin n, {p | u/2 < |∑ e : incidentEdges i,
      G (a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e)))*
        ((β/sqrt n*p.2 e+β^2/(n:ℝ))^2-β^2/(n:ℝ))| ∧
      (∑ e : incidentEdges i, p.2 e^2)/(n:ℝ)≤C}
  have hbad (a : s) : ExponentiallyRare
      (fun n => (μ n).prod (standardArrayLaw (Edge n))) (bad a) := by
    apply exponentiallyRare_iUnion_polynomial _ _ hc (by norm_num : (0:ℝ)<3)
      (by norm_num : (0:ℝ)<1) 1
    · exact Eventually.of_forall (fun n => by simp)
    · filter_upwards [ht] with n hn i
      apply hn (μ n) (incidentEdges i)
        (fun ζ y e => G (a,b (diagonalField ζ (outsideDisorder β i y) (otherEnd i e))))
        (incidentEdges_card_le i)
      · intro e
        exact (hG.comp (continuous_const.prodMk (hb.continuous.comp
          (continuous_outside_field β i (otherEnd i e))))).measurable
      · intro ζ y e
        exact hAb _ _
  let d := δ/(2*((K:ℝ)+1))
  have hd : 0<d := by dsimp [d]; positivity
  have hKd : (K:ℝ)*d<δ := by
    dsimp [d]
    have hpos : (0:ℝ)<2*((K:ℝ)+1) := by positivity
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hpos).mpr
    nlinarith [K.coe_nonneg]
  apply (((hrows.prod_snd μ).union ((affine_max_entry_rare β hd).prod_snd μ)).union
    (ExponentiallyRare.iUnion_finite hbad)).mono
  filter_upwards [eventually_gt_atTop 0] with n hn p hp
  by_contra hfail
  have hr : ∀ i, (∑ e∈incidentEdges i, p.2 e^2)/(n:ℝ)≤C := by
    intro i
    exact le_of_not_gt (fun hi => hfail (Or.inl (Or.inl ⟨i,hi⟩)))
  have he : ∀ e, |affineDisorder β p.2 e|≤d := by
    intro e
    exact le_of_not_gt (fun hh => hfail (Or.inl (Or.inr ⟨e,hh⟩)))
  have hg : ∀ a : s, ∀ i : Fin n,
      |∑ e : incidentEdges i,
        (affineDisorder β p.2 e^2-β^2/(n:ℝ))*
          G (a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e)))|≤u/2 := by
    intro a i
    apply le_of_not_gt
    intro hh
    apply hfail
    right
    apply mem_iUnion.mpr
    refine ⟨a,mem_iUnion.mpr ⟨i,?_,?_⟩⟩
    · simpa only [affineDisorder,mul_comm] using hh
    · simpa only [Finset.sum_subtype (incidentEdges i) (fun _ => Iff.rfl)] using hr i
  obtain ⟨i,a,hi⟩ := hp
  have hsr : ∑ e : incidentEdges i, |affineDisorder β p.2 e^2-β^2/(n:ℝ)|≤R :=
    incident_absolute_square_error hn β p.2 hr i
  have hf (e : incidentEdges i) :
      |G (a,b (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e)))-
        G (q a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e)))|≤v := by
    apply le_of_lt
    rw [←Real.dist_eq]
    apply hcont
    rw [Prod.dist_eq,max_lt_iff]
    refine ⟨hq a,?_⟩
    have hdist := hb.dist_le_mul
      (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e))
      (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e))
    rw [Real.dist_eq,outside_field_error] at hdist
    exact (hdist.trans (mul_le_mul_of_nonneg_left (he e) K.coe_nonneg)).trans_lt hKd
  have herr := weighted_sum_difference_le
    (fun e : incidentEdges i => affineDisorder β p.2 e^2-β^2/(n:ℝ))
    (fun e => G (a,b (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e))))
    (fun e => G (q a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e))))
    hv.le hsr hf
  have htri := abs_sub_abs_le_abs_sub
    (∑ e : incidentEdges i, (affineDisorder β p.2 e^2-β^2/(n:ℝ))*
      G (a,b (diagonalField p.1 (affineDisorder β p.2) (otherEnd i e))))
    (∑ e : incidentEdges i, (affineDisorder β p.2 e^2-β^2/(n:ℝ))*
      G (q a,b (diagonalField p.1 (outsideDisorder β i (fun j => p.2 j)) (otherEnd i e))))
  have hgood := hg (q a) i
  linarith only [htri,herr,hgood,hvR,hi]

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_AugmentedSquares
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma continuous_affineDisorder (β : ℝ) : Continuous (affineDisorder (n := n) β) := by
  unfold affineDisorder
  fun_prop

lemma diagonal_affine_hasLaw (hn : 0<n) (β : ℝ) (μ : Measure (Fin n → ℝ)) [SFinite μ] :
    HasLaw (fun p : (Fin n → ℝ) × Disorder n => (p.1,affineDisorder β p.2))
      (μ.prod (law β n)) (μ.prod (standardArrayLaw (Edge n))) := by
  refine ⟨(continuous_fst.prodMk ((continuous_affineDisorder β).comp continuous_snd)).aemeasurable,?_⟩
  change Measure.map (Prod.map id (affineDisorder β)) _ = _
  rw [←Measure.map_prod_map μ _ measurable_id (continuous_affineDisorder β).measurable,
    Measure.map_id,(affineDisorder_hasLaw hn β).map_eq]

lemma continuous_diagonalSquareError {X : Type*} [TopologicalSpace X]
    (β : ℝ) {G : X × X → ℝ} (hG : Continuous G) {b : ℝ → X} (hb : Continuous b)
    (i : Fin n) : Continuous (fun p => diagonalSquareError β G b p i) := by
  apply continuous_finsetSum
  intro e _
  apply Continuous.mul (by fun_prop)
  exact hG.comp ((hb.comp (continuous_diagonalField i)).prodMk
    (hb.comp (continuous_diagonalField (otherEnd i e))))

lemma diagonal_square_event_measurable {X : Type*} [TopologicalSpace X]
    (β : ℝ) {G : X × X → ℝ} (hG : Continuous G) {b : ℝ → X} (hb : Continuous b)
    (u : ℝ) : MeasurableSet {p : (Fin n → ℝ) × Disorder n |
      ∃ i, u < |diagonalSquareError β G b p i|} := by
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion (fun i => isOpen_lt continuous_const
    (continuous_diagonalSquareError β hG hb i).abs |>.measurableSet)

theorem planted_weighted_diagonal_rare {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) (b : ℝ → X) {K : ℝ≥0} (hb : LipschitzWith K b)
    (β : ℝ) (μ : ∀ n, Measure (Fin n → ℝ)) [∀ n, IsProbabilityMeasure (μ n)]
    {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => (μ n).prod (law β n))
      (fun n => {p | ∃ i : Fin n, u < |diagonalSquareError β G b p i|}) := by
  obtain ⟨C,c,hC,hc,ht⟩ := continuous_weighted_diagonal_rare G hG b hb β μ hu
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  rw [←(diagonal_affine_hasLaw hn0 β (μ n)).measure_eq
    (diagonal_square_event_measurable β hG hb.continuous u)]
  refine (measure_mono ?_).trans hn
  rintro p ⟨i,hi⟩
  exact ⟨i,b (diagonalField p.1 (affineDisorder β p.2) i),hi⟩

lemma augmentedPair_gaussian (β : ℝ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ =>
      (augmentedDiagonal β g,augmentedDisorder β g)) (standardArrayLaw (Fin n × Fin n)) := by
  let L : ((Fin n × Fin n) → ℝ) →L[ℝ] ((Fin n → ℝ) × Disorder n) :=
    (β • ContinuousLinearMap.pi (fun i : Fin n => (entryCLM i i).comp (goeCLM n))).prod
      (β • ContinuousLinearMap.pi (fun e : Edge n => (entryCLM e.1.1 e.1.2).comp (goeCLM n)))
  let c := ((fun _ : Fin n => β^2/(n:ℝ)),(fun _ : Edge n => β^2/(n:ℝ)))
  have hL := coordinates_gaussian.map_fun L
  have h : HasGaussianLaw (fun g => L g+c) (standardArrayLaw (Fin n × Fin n)) := by
    have := hL.isGaussian_map
    refine ⟨?_⟩
    change IsGaussian ((standardArrayLaw (Fin n × Fin n)).map ((fun x => x+c) ∘ L))
    rw [← AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable (fun x => x+c) ((standardArrayLaw (Fin n × Fin n)).map L)) hL.aemeasurable]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  apply h.congr
  exact Eventually.of_forall (fun g => by
    ext x <;> simp [L,c,entryCLM_apply,goeCLM_apply,augmented,augmentedDiagonal,augmentedDisorder])

lemma augmentedDiagonal_independent (hn : 0<n) (β : ℝ) :
    IndepFun (augmentedDiagonal (n := n) β) (augmentedDisorder β)
      (standardArrayLaw (Fin n × Fin n)) := by
  apply (augmentedPair_gaussian β).indepFun_of_covariance_eval
  intro i e
  change cov[fun g => augmented β g i i,fun g => augmented β g e.1.1 e.1.2;
    standardArrayLaw (Fin n × Fin n)] = 0
  rw [augmented_covariance hn]
  have h1 : ¬(i=e.1.1 ∧ i=e.1.2) := by rintro ⟨rfl,h⟩; exact (ne_of_lt e.2) h
  have h2 : ¬(i=e.1.2 ∧ i=e.1.1) := by rintro ⟨h,rfl⟩; exact (ne_of_lt e.2) h
  simp only [ite_eq_right h1,ite_eq_right h2,add_zero,mul_zero]

lemma continuous_augmentedDiagonal (β : ℝ) : Continuous (augmentedDiagonal (n := n) β) := by
  unfold augmentedDiagonal augmented goe
  fun_prop

instance diagonalLaw_probability (β : ℝ) : IsProbabilityMeasure (diagonalLaw β n) :=
  (Measure.isProbabilityMeasure_map_iff (continuous_augmentedDiagonal β).aemeasurable).2
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Continuous.aemeasurable; apply continuous_augmentedDiagonal <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))

lemma augmentedPair_hasLaw (hn : 0<n) (β : ℝ) :
    HasLaw (fun g : (Fin n × Fin n) → ℝ => (augmentedDiagonal β g,augmentedDisorder β g))
      ((diagonalLaw β n).prod (law β n)) (standardArrayLaw (Fin n × Fin n)) :=
  (augmentedDiagonal_independent hn β).hasLaw_prod
    ⟨(continuous_augmentedDiagonal β).aemeasurable,rfl⟩ (augmentedDisorder_hasLaw hn β)

lemma diagonalField_augmented (β : ℝ) (g : (Fin n × Fin n) → ℝ) (i : Fin n) :
    diagonalField (augmentedDiagonal β g) (augmentedDisorder β g) i = augmentedField β g i := by
  have h := coupling_augmentedDisorder β g
  change augmented β g i i+∑ j, coupling (augmentedDisorder β g) i j = _
  simp_rw [show coupling (augmentedDisorder β g) = fun i j =>
    augmented β g i j - Matrix.diagonal (fun k => augmented β g k k) i j from h]
  simp [Finset.sum_sub_distrib,Matrix.diagonal_apply,augmentedField]

theorem augmented_weighted_diagonal_rare {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) (b : ℝ → X) {K : ℝ≥0} (hb : LipschitzWith K b)
    (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ i : Fin n, u < |∑ e : incidentEdges i,
        (augmentedDisorder β g e^2-β^2/(n:ℝ))*
          G (b (augmentedField β g i),b (augmentedField β g (otherEnd i e)))|}) := by
  obtain ⟨C,c,hC,hc,ht⟩ := planted_weighted_diagonal_rare G hG b hb β (diagonalLaw β) hu
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  have hl := (augmentedPair_hasLaw hn0 β).measure_eq
    (diagonal_square_event_measurable β hG hb.continuous u)
  simpa only [diagonalSquareError,diagonalField_augmented] using hl.le.trans hn

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_AugmentedBounds
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma centered_augmentedDiagonal_hasLaw (hn : 0<n) (β : ℝ) (i : Fin n) :
    HasLaw (fun g : (Fin n × Fin n) → ℝ => β*goe g i i)
      (gaussianReal 0 (Real.toNNReal (2*β^2/(n:ℝ)))) (standardArrayLaw (Fin n × Fin n)) := by
  have hg : HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ => β*goe g i i)
      (standardArrayLaw (Fin n × Fin n)) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
      smul_eq_mul,mul_comm] using (((goe_gaussian n).eval i |>.eval i).map_fun
        ((ContinuousLinearMap.id ℝ ℝ).smulRight β))
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,integral_const_mul,goe_entry_mean,mul_zero,
    ←covariance_self hg.aemeasurable,covariance_const_mul_left,covariance_const_mul_right,
    goe_entry_covariance hn]
  congr 2
  simp only [and_self,ite_true, if_true]
  ring

lemma augmented_diagonal_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ i : Fin n, u< |augmentedDiagonal β g i|}) := by
  by_cases hb : β=0
  · apply (exponentiallyRare_empty (fun n => standardArrayLaw (Fin n × Fin n))).mono
    refine Eventually.of_forall ?_
    intro n g hg
    obtain ⟨i,hi⟩ := hg
    simp [augmentedDiagonal,augmented,hb,hu.not_gt] at hi
  have hb2 : 0<β^2 := sq_pos_of_ne_zero hb
  have hc : 0<u^2/(16*β^2) := by positivity
  have ht := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (β^2)
  have hbound : ∀ᶠ n in atTop, ∀ i : Fin n,
      standardArrayLaw (Fin n × Fin n) {g | u< |augmentedDiagonal β g i|} ≤
        ENNReal.ofReal (2*exp (-(u^2/(16*β^2))*n)) := by
    filter_upwards [eventually_gt_atTop 0,ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<u/2))]
      with n hn hm i
    have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hs := subgaussian_abs_tail (gaussian_hasSubgaussianMGF (centered_augmentedDiagonal_hasLaw hn β i))
      (u/2) (by positivity)
    have hv : (Real.toNNReal (2*β^2/(n:ℝ)) : ℝ)=2*β^2/(n:ℝ) := Real.coe_toNNReal _ (by positivity)
    have he : -(u/2)^2/(2*(2*β^2/(n:ℝ)))=-(u^2/(16*β^2))*(n:ℝ) := by field_simp; ring
    rw [hv,he,←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num)] at hs
    refine (measure_mono ?_).trans hs
    intro g hg
    change u/2 ≤ |β*goe g i i|
    have ha := abs_add_le (β*goe g i i) (β^2/(n:ℝ))
    rw [abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ))] at ha
    change u< |β*goe g i i+β^2/(n:ℝ)| at hg
    linarith
  have hh := exponentiallyRare_iUnion_polynomial (fun n => standardArrayLaw (Fin n × Fin n))
    (fun n i => {g | u< |augmentedDiagonal β g i|}) hc (by norm_num : (0:ℝ)<2)
    (D := 1) (by norm_num) 1 (Eventually.of_forall (fun n => by simp)) hbound
  apply hh.mono
  exact Eventually.of_forall (fun n g hg => mem_iUnion.mpr hg)

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_CompactField
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus

lemma compactWeight_lipschitz : LipschitzWith 1 compactWeight := by
  apply LipschitzWith.of_dist_le_mul
  intro h t
  change |w h-w t| ≤ (1:ℝ)*|h-t|
  simpa only [w,m,sub_sub_sub_cancel_left,abs_sub_comm,one_mul] using tanh_lipschitz_abs h t

lemma compactV_nonneg (a : FieldWeight) : 0 ≤ compactV a :=
  mul_nonneg a.2.1 (sub_nonneg.mpr a.2.2)
lemma compactV_le_one (a : FieldWeight) : compactV a≤1 := by
  dsimp [compactV]
  nlinarith [sq_nonneg ((a:ℝ)-1)]
lemma compactV_le (a : FieldWeight) : compactV a≤2*a := by
  dsimp [compactV]
  nlinarith [sq_nonneg (a:ℝ)]
lemma compactF_nonneg (p : FieldWeight × FieldWeight) : 0 ≤ compactF p := by
  unfold compactF
  exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (add_nonneg p.1.2.1 p.2.2.1)
lemma compactK_nonneg (p : FieldWeight × FieldWeight) : 0 ≤ compactK p := by
  unfold compactK
  exact div_nonneg (mul_nonneg (compactV_nonneg _) (compactV_nonneg _)) (add_nonneg p.1.2.1 p.2.2.1)

lemma compactF_bound (p : FieldWeight × FieldWeight) : compactF p ≤ 4*(p.2:ℝ) := by
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · simp only [compactF,hz,div_zero]
    exact mul_nonneg (by norm_num) p.2.2.1
  have hd : 0<(p.1:ℝ)+(p.2:ℝ) := lt_of_le_of_ne (add_nonneg p.1.2.1 p.2.2.1) (Ne.symm hz)
  apply (div_le_iff₀ hd).mpr
  have hs : (2-(p.2:ℝ))^2≤4 := by nlinarith [p.2.2.1,p.2.2.2]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (p.2:ℝ))
  nlinarith only [hm,mul_nonneg p.1.2.1 p.2.2.1]

lemma compactK_bound (p : FieldWeight × FieldWeight) : compactK p ≤ 4*(p.2:ℝ) := by
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · simp only [compactK,hz,div_zero]
    exact mul_nonneg (by norm_num) p.2.2.1
  have hd : 0<(p.1:ℝ)+(p.2:ℝ) := lt_of_le_of_ne (add_nonneg p.1.2.1 p.2.2.1) (Ne.symm hz)
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul (compactV_le p.1) (compactV_le p.2)
    (compactV_nonneg p.2) (mul_nonneg (by norm_num : (0:ℝ)≤2) p.1.2.1)
  nlinarith only [hm,sq_nonneg (p.2:ℝ)]

lemma continuous_compactV : Continuous compactV := by unfold compactV; fun_prop

lemma continuous_compact_div {f : FieldWeight × FieldWeight → ℝ}
    (hnonneg : ∀ p, 0≤f p) (hbound : ∀ p, f p≤4*(p.2:ℝ))
    (hoff : ∀ p, (p.1:ℝ)+(p.2:ℝ)≠0 → ContinuousAt f p) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · have h2 : (p.2:ℝ)=0 := by linarith [p.1.2.1,p.2.2.1]
    have hp : f p=0 := le_antisymm (by simpa [h2] using hbound p) (hnonneg p)
    rw [ContinuousAt,hp]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun q : FieldWeight × FieldWeight => 4*(q.2:ℝ))
      (by simpa only [ContinuousAt,h2,mul_zero] using
        (show Continuous (fun q : FieldWeight × FieldWeight => 4*(q.2:ℝ)) by fun_prop).continuousAt (x := p))
      hnonneg hbound
  · exact hoff p hz

lemma continuous_compactF : Continuous compactF := by
  apply continuous_compact_div compactF_nonneg compactF_bound
  intro p hp
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hp

lemma continuous_compactK : Continuous compactK := by
  apply continuous_compact_div compactK_nonneg compactK_bound
  intro p hp
  exact ContinuousAt.div
    ((continuous_compactV.comp continuous_fst).mul (continuous_compactV.comp continuous_snd)).continuousAt
    (by fun_prop) hp

lemma compactV_weight (h : ℝ) : compactV (compactWeight h) = v h := by
  unfold compactV compactWeight w v
  dsimp
  ring

lemma compactF_weight (h t : ℝ) : compactF (compactWeight h,compactWeight t) =
    v t^2/(w h+w t) := by
  unfold compactF
  simp only [compactWeight_coe,←mul_pow]
  rw [show w t*(2-w t)=v t from compactV_weight t]

lemma compactK_weight (h t : ℝ) : compactK (compactWeight h,compactWeight t) =
    kernel h t := by
  unfold compactK kernel
  rw [compactV_weight,compactV_weight]
  rfl

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FormAlgebra
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma continuous_varianceKernel : Continuous varianceKernel :=
  continuous_compactV.comp continuous_snd
lemma continuous_meanVarianceKernel : Continuous meanVarianceKernel := by
  unfold meanVarianceKernel
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
    (continuous_compactV.comp continuous_snd)

lemma quadratic_sub (A B : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    quadratic (A-B) p = quadratic A p-quadratic B p := by
  simp only [quadratic,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma quadratic_inner (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    quadratic A p = inner ℝ (WithLp.toLp 2 p)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A (WithLp.toLp 2 p)) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [quadratic,dotProduct,Matrix.mulVec,Finset.mul_sum]
  congr 1
  ext i
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_abs_le (A : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) :
    |quadratic A p| ≤ euclideanOpNorm A*(∑ i, p i^2) := by
  rw [quadratic_inner]
  let P : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 p
  have hb := (abs_real_inner_le_norm P (Matrix.toEuclideanCLM (𝕜 := ℝ) A P)).trans
    (mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm P) (norm_nonneg P))
  calc
    _ ≤ ‖P‖*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖*‖P‖) := hb
    _ = euclideanOpNorm A*(∑ i, p i^2) := by
      rw [show ‖P‖*(‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖*‖P‖) =
        euclideanOpNorm A*‖P‖^2 by unfold euclideanOpNorm; ring]
      rw [EuclideanSpace.real_norm_sq_eq]

lemma weightedForm_sub (A B : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x : Fin n → FieldWeight) (p : Fin n → ℝ) :
    weightedForm A G x p-weightedForm B G x p = weightedForm (A-B) G x p := by
  simp only [weightedForm,quadratic,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma diagonalForm_sub (A B : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x : Fin n → FieldWeight) (p : Fin n → ℝ) :
    diagonalForm A G x p-diagonalForm B G x p = diagonalForm (A-B) G x p := by
  simp only [diagonalForm,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma diagonalForm_abs_le (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x : Fin n → FieldWeight) (p : Fin n → ℝ)
    {C : ℝ} (hC : ∀ i, |∑ j, A i j*G (x i,x j)| ≤ C) :
    |diagonalForm A G x p| ≤ C*∑ i, p i^2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, C*p i^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,abs_of_nonneg (sq_nonneg (p i))]
      exact mul_le_mul_of_nonneg_right (hC i) (sq_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm

lemma sum_offdiag_eq_full {F : Fin n → Fin n → ℝ} (hF : ∀ i, F i i=0) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, F i j) = ∑ i, ∑ j, F i j := by
  apply Finset.sum_congr rfl
  intro i _
  simpa only [hF i,add_zero] using Finset.sum_erase_add Finset.univ (F i) (Finset.mem_univ i)

lemma gradient_pair_expansion (J : Interaction n) (hJ : ∀ i j, J i j=J j i)
    (hdiag : ∀ i, J i i=0) (H p : Fin n → ℝ) :
    pairSum (fun i j => J i j^2*(v (H j)*p i+v (H i)*p j)^2/(w (H i)+w (H j))) =
      diagonalForm (fun i j => J i j^2) compactF (fun i => compactWeight (H i)) p +
      weightedForm (fun i j => J i j^2) compactK (fun i => compactWeight (H i)) p := by
  have hd : ∀ i, J i i^2*(v (H i)^2/(w (H i)+w (H i)))*p i^2=0 := by simp [hdiag]
  have hk : ∀ i, J i i^2*kernel (H i) (H i)*p i*p i=0 := by simp [hdiag]
  simp only [diagonalForm,weightedForm,quadratic,compactF_weight,compactK_weight,Finset.sum_mul]
  rw [←sum_offdiag_eq_full hd,←sum_offdiag_eq_full hk,sum_offdiag_pairs,sum_offdiag_pairs,←pairSum_add]
  unfold pairSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only []
  rw [hJ j i]
  dsimp [kernel]
  rw [add_comm (w (H j)) (w (H i))]
  ring

theorem gradientForm_eq_compactForm (J : Interaction n) (hJ : ∀ i j, J i j=J j i)
    (hdiag : ∀ i, J i i=0) (p : Fin n → ℝ) :
    gradientForm J p = compactForm J (fun i => compactWeight (∑ j, J i j)) p := by
  have hm (i : Fin n) : mean J (plusSpin n) i = m (∑ j, J i j) := by
    simp [mean,field,plusSpin,spin,m]
  have hv (i : Fin n) : conditionalVariance J (plusSpin n) i = v (∑ j, J i j) := by
    simp only [conditionalVariance,hm,v]
  have hw (i : Fin n) : gradientWeight J (plusSpin n) i = w (∑ j, J i j) := by
    simp [gradientWeight,plusSpin,spin,hm,w]
  simp only [gradientForm,hm,hv,hw,gradient_pair_expansion J hJ hdiag,
    compactForm,weightedForm,quadratic,varianceKernel,meanVarianceKernel,
    compactV_weight,compactWeight_coe]
  have h₁ : (∑ i, ∑ j ∈ Finset.univ.erase i, J i j*p i*v (∑ k, J j k)*p j) =
      ∑ i, ∑ j, J i j*v (∑ k, J j k)*p i*p j := by
    rw [sum_offdiag_eq_full (by intro i; simp [hdiag])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₂ : (∑ i, ∑ j ∈ Finset.univ.erase i, J i j^2*p i*m (∑ k, J j k)*v (∑ k, J j k)*p j) =
      ∑ i, ∑ j, J i j^2*((1-w (∑ k, J j k))*v (∑ k, J j k))*p i*p j := by
    rw [sum_offdiag_eq_full (by intro i; simp [hdiag])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [w]
    ring
  rw [h₁,h₂]
  ring

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_FormContinuity
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
attribute [-simp] _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.siteRefresh_const
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma weightedForm_field_sub (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ) :
    weightedForm A G x p-weightedForm A G y p =
      quadratic (fun i j => A i j*(G (x i,x j)-G (y i,y j))) p := by
  simp only [weightedForm,quadratic,mul_sub,sub_mul,Finset.sum_sub_distrib]

lemma weightedForm_field_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ)
    {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hr : ∀ i, ∑ j, |A i j| ≤ C) (hc : ∀ j, ∑ i, |A i j| ≤ C)
    (he : ∀ i j, |G (x i,x j)-G (y i,y j)| ≤ a) :
    |weightedForm A G x p-weightedForm A G y p| ≤ a*C*∑ i, p i^2 := by
  rw [weightedForm_field_sub]
  exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right
    (kernel_error_norm_le A _ _ ha hC hr hc he) (Finset.sum_nonneg (fun i _ => sq_nonneg (p i))))

lemma diagonalForm_field_bound (A : Matrix (Fin n) (Fin n) ℝ)
    (G : FieldWeight × FieldWeight → ℝ) (x y : Fin n → FieldWeight) (p : Fin n → ℝ)
    {a C : ℝ} (ha : 0≤a)
    (hr : ∀ i, ∑ j, |A i j| ≤ C)
    (he : ∀ i j, |G (x i,x j)-G (y i,y j)| ≤ a) :
    |diagonalForm A G x p-diagonalForm A G y p| ≤ a*C*∑ i, p i^2 := by
  have hid : diagonalForm A G x p-diagonalForm A G y p =
      ∑ i, (∑ j, A i j*(G (x i,x j)-G (y i,y j)))*p i^2 := by
    simp only [diagonalForm,mul_sub,sub_mul,Finset.sum_sub_distrib]
  have hb (i : Fin n) : |∑ j, A i j*(G (x i,x j)-G (y i,y j))| ≤ a*C := by
    calc
      _ ≤ ∑ j, |A i j*(G (x i,x j)-G (y i,y j))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, a*|A i j| := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (he i j) (abs_nonneg _))
      _ = a*(∑ j, |A i j|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr i) ha
  rw [hid]
  calc
    _ ≤ ∑ i, |(∑ j, A i j*(G (x i,x j)-G (y i,y j)))*p i^2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (a*C)*p i^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,abs_of_nonneg (sq_nonneg (p i))]
      exact mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm

lemma weightedForm_variance_eq (J : Interaction n) (x : Fin n → FieldWeight) (p : Fin n → ℝ) :
    weightedForm J varianceKernel x p = quadratic ((Matrix.of J)*
      Matrix.diagonal (fun i => compactV (x i))) p := by
  simp only [weightedForm,quadratic,varianceKernel,Matrix.mul_diagonal,Matrix.of_apply]

lemma weightedForm_variance_field_bound (J : Interaction n) (x y : Fin n → FieldWeight)
    (p : Fin n → ℝ) {a : ℝ} (ha : 0≤a)
    (he : ∀ i, |compactV (x i)-compactV (y i)| ≤ a) :
    |weightedForm J varianceKernel x p-weightedForm J varianceKernel y p| ≤
      a*euclideanOpNorm J*∑ i, p i^2 := by
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => compactV (x i)-compactV (y i))
  have heq : (Matrix.of J)*Matrix.diagonal (fun i => compactV (x i)) -
      (Matrix.of J)*Matrix.diagonal (fun i => compactV (y i)) = (Matrix.of J)*D := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sub_apply,Matrix.mul_diagonal,Matrix.of_apply,D]
    ring
  rw [weightedForm_variance_eq,weightedForm_variance_eq,←quadratic_sub,heq]
  have hnD : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) D‖ ≤ a :=
    matrix_diagonal_opNorm_le _ a ha he
  have hn : euclideanOpNorm ((Matrix.of J)*D) ≤ a*euclideanOpNorm J := by
    unfold euclideanOpNorm
    rw [map_mul,mul_comm a]
    apply (norm_mul_le _ _).trans
    exact mul_le_mul_of_nonneg_left hnD (norm_nonneg _)
  exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right hn
    (Finset.sum_nonneg (fun i _ => sq_nonneg (p i))))

lemma compactForm_field_bound (J : Interaction n) (hJ : ∀ i j, J i j=J j i)
    (x y : Fin n → FieldWeight) (p : Fin n → ℝ) {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hr : ∀ i, ∑ j, J i j^2 ≤ C)
    (hv : ∀ i, |compactV (x i)-compactV (y i)| ≤ a)
    (hm : ∀ i j, |meanVarianceKernel (x i,x j)-meanVarianceKernel (y i,y j)| ≤ a)
    (hf : ∀ i j, |compactF (x i,x j)-compactF (y i,y j)| ≤ a)
    (hk : ∀ i j, |compactK (x i,x j)-compactK (y i,y j)| ≤ a) :
    |compactForm J x p-compactForm J y p| ≤ a*(euclideanOpNorm J+4*C)*(∑ i, p i^2) := by
  have hr' (i : Fin n) : ∑ j, |J i j^2| ≤ C := by simpa only [abs_pow,sq_abs] using hr i
  have hc' (j : Fin n) : ∑ i, |J i j^2| ≤ C := by simpa only [hJ,abs_pow,sq_abs] using hr j
  let L := weightedForm J varianceKernel x p-weightedForm J varianceKernel y p
  let M := weightedForm (fun i j => J i j^2) meanVarianceKernel x p-weightedForm (fun i j => J i j^2) meanVarianceKernel y p
  let D := diagonalForm (fun i j => J i j^2) compactF x p-diagonalForm (fun i j => J i j^2) compactF y p
  let K := weightedForm (fun i j => J i j^2) compactK x p-weightedForm (fun i j => J i j^2) compactK y p
  have hid : compactForm J x p-compactForm J y p=L+2*M+D+K := by dsimp [compactForm,L,M,D,K]; ring
  have hL : |L| ≤ a*euclideanOpNorm J*(∑ i, p i^2) := weightedForm_variance_field_bound J x y p ha hv
  have hM : |M| ≤ a*C*(∑ i, p i^2) := weightedForm_field_bound _ _ x y p ha hC hr' hc' hm
  have hD : |D| ≤ a*C*(∑ i, p i^2) := diagonalForm_field_bound _ _ x y p ha hr' hf
  have hK : |K| ≤ a*C*(∑ i, p i^2) := weightedForm_field_bound _ _ x y p ha hC hr' hc' hk
  rw [hid]
  have ht := (abs_add_le (L+2*M+D) K).trans
    (add_le_add ((abs_add_le (L+2*M) D).trans (add_le_add (abs_add_le L (2*M)) le_rfl)) le_rfl)
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
  nlinarith only [ht,hL,hM,hD,hK]

lemma form_kernels_uniform {a : ℝ} (ha : 0<a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x y x' y' : FieldWeight,
      dist x x'<δ → dist y y'<δ →
      |compactV y-compactV y'|≤a ∧
      |meanVarianceKernel (x,y)-meanVarianceKernel (x',y')|≤a ∧
      |compactF (x,y)-compactF (x',y')|≤a ∧
      |compactK (x,y)-compactK (x',y')|≤a := by
  let G : FieldWeight × FieldWeight → Fin 4 → ℝ := fun p =>
    ![varianceKernel p,meanVarianceKernel p,compactF p,compactK p]
  have hG : Continuous G := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_varianceKernel
    · exact continuous_meanVarianceKernel
    · exact continuous_compactF
    · exact continuous_compactK
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hG) a ha
  refine ⟨δ,hδ,?_⟩
  intro x y x' y' hx hy
  have hh := (dist_pi_lt_iff ha).mp (hcont (a := (x,y)) (b := (x',y'))
    (by simpa only [Prod.dist_eq,max_lt_iff] using And.intro hx hy))
  exact ⟨(hh 0).le,(hh 1).le,(hh 2).le,(hh 3).le⟩

lemma compactForm_uniform_field_change {C K u : ℝ} (hC : 0≤C) (hK : 0≤K) (hu : 0<u) :
    ∃ δ : ℝ, 0<δ ∧ ∀ {n : ℕ} (J : Interaction n), (∀ i j, J i j=J j i) →
      euclideanOpNorm J≤K → (∀ i, ∑ j, J i j^2≤C) →
      ∀ H H' p : Fin n → ℝ, (∀ i, |H i-H' i|≤δ) →
      |compactForm J (fun i => compactWeight (H i)) p-
        compactForm J (fun i => compactWeight (H' i)) p| ≤ u*(∑ i, p i^2) := by
  let a := u/(K+4*C+1)
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨δ,hδ,hcont⟩ := form_kernels_uniform ha
  refine ⟨δ/2,by positivity,?_⟩
  intro n J hJ hnorm hr H H' p hnear
  have hd (i : Fin n) : dist (compactWeight (H i)) (compactWeight (H' i))<δ := by
    have hb := compactWeight_lipschitz.dist_le_mul (H i) (H' i)
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hb
    exact lt_of_le_of_lt (hb.trans (hnear i)) (by linarith)
  have hb := compactForm_field_bound J hJ _ _ p ha.le hC hr
    (fun i => (hcont _ _ _ _ (hd i) (hd i)).1)
    (fun i j => (hcont _ _ _ _ (hd i) (hd j)).2.1)
    (fun i j => (hcont _ _ _ _ (hd i) (hd j)).2.2.1)
    (fun i j => (hcont _ _ _ _ (hd i) (hd j)).2.2.2)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hden : 0<K+4*C+1 := by positivity
  have hid : a*(K+4*C+1)=u := div_mul_cancel₀ _ hden.ne'
  nlinarith only [hid,mul_nonneg ha.le (sub_nonneg.mpr hnorm),ha.le]

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ReducedForm
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet Calculus Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma weighted_operator_event_measurable {X : Type*} (β u : ℝ) (G : X × X → ℝ) :
    MeasurableSet {g : Disorder n | ∃ x : Fin n → X,
      u < euclideanOpNorm (fun i j => squareError β g i j*G (x i,x j))} := by
  let : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n)) := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearMap.continuousSMul
  simp only [ofPred_exists]
  apply IsOpen.measurableSet
  apply isOpen_iUnion
  intro x
  apply isOpen_lt continuous_const
  apply continuous_norm.comp
  apply ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((continuous_coupling i j).pow 2).sub continuous_const).mul_const _

lemma augmented_weighted_operator_rare {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (β : ℝ) (G : X × X → ℝ) (hG : Continuous G) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ x : Fin n → X, u < euclideanOpNorm
        (fun i j => squareError β (augmentedDisorder β g) i j*G (x i,x j))}) := by
  obtain ⟨C,c,hC,hc,ht⟩ := weighted_square_operator_rare β G hG hu
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  rw [(augmentedDisorder_hasLaw hn0 β).measure_eq (weighted_operator_event_measurable β u G)]
  exact hn

lemma squareError_row (β : ℝ) (g : Disorder n) (f : Fin n → ℝ) (i : Fin n) :
    (∑ j, squareError β g i j*f j) =
      (∑ e : incidentEdges i, (g e^2-β^2/(n:ℝ))*f (otherEnd i e))-β^2/(n:ℝ)*f i := by
  have he := squareError_decomposition β g
  simp_rw [show (fun i j => squareError β g i j)=
    (fun i j => coupling (fun e => g e^2-β^2/(n:ℝ)) i j-
      Matrix.diagonal (fun _ => β^2/(n:ℝ)) i j) from congrArg (fun m => fun i j => m i j) he]
  simp only [sub_mul,Finset.sum_sub_distrib]
  rw [sum_coupling_weighted_row]
  simp only [←Finset.sum_attach (s := incidentEdges i)]
  congr 1
  · simp only [sub_mul,Finset.sum_sub_distrib, Finset.attach_eq_univ]
  · simp [Matrix.diagonal_apply,ite_mul]

lemma diagonal_weight_bound (G : FieldWeight × FieldWeight → ℝ) (x : Fin n → FieldWeight)
    (p ζ : Fin n → ℝ) {u : ℝ} (hζ : ∀ i, |ζ i| ≤ u)
    (hG : ∀ a : FieldWeight, |G (a,a)| ≤ 1) :
    |weightedForm (Matrix.diagonal ζ) G x p| ≤ u*∑ i, p i^2 := by
  have hf : weightedForm (Matrix.diagonal ζ) G x p = ∑ i, ζ i*G (x i,x i)*p i^2 := by
    simp only [weightedForm,quadratic,Matrix.diagonal_apply,ite_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hf]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, u*p i^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg (p i))]
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (hG (x i)) (abs_nonneg _)).trans (by simpa only [mul_one] using hζ i))
        (sq_nonneg _))
    _ = _ := (Finset.mul_sum ..).symm

lemma compactF_le_eight (a b : FieldWeight) : |compactF (a,b)|≤8 := by
  rw [abs_of_nonneg (compactF_nonneg _)]
  exact (compactF_bound _).trans (by nlinarith [b.2.2])

lemma compactForm_reduced_error (β : ℝ) (g : (Fin n × Fin n) → ℝ)
    (p : Fin n → ℝ) {a d : ℝ}
    (hdiag : ∀ i, |augmentedDiagonal β g i|≤a)
    (hm : ∀ x : Fin n → FieldWeight, euclideanOpNorm
      (fun i j => squareError β (augmentedDisorder β g) i j*meanVarianceKernel (x i,x j)) ≤ a)
    (hk : ∀ x : Fin n → FieldWeight, euclideanOpNorm
      (fun i j => squareError β (augmentedDisorder β g) i j*compactK (x i,x j)) ≤ a)
    (hf : ∀ i, |∑ e : incidentEdges i, (augmentedDisorder β g e^2-β^2/(n:ℝ))*
      compactF (compactWeight (augmentedField β g i),compactWeight (augmentedField β g (otherEnd i e)))| ≤ d) :
    |compactForm (coupling (augmentedDisorder β g))
      (fun i => compactWeight (augmentedField β g i)) p-reducedForm β g p| ≤
      (4*a+d+8*β^2/(n:ℝ))*(∑ i, p i^2) := by
  let J := coupling (augmentedDisorder β g)
  let x := fun i => compactWeight (augmentedField β g i)
  let L := weightedForm J varianceKernel x p-weightedForm (augmented β g) varianceKernel x p
  let Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => J i j^2)
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => β^2/(n:ℝ))
  let M := weightedForm Q meanVarianceKernel x p-weightedForm B meanVarianceKernel x p
  let D := diagonalForm Q compactF x p-diagonalForm B compactF x p
  let K := weightedForm Q compactK x p-weightedForm B compactK x p
  have hL : |L|≤a*(∑ i, p i^2) := by
    have hd := diagonal_weight_bound varianceKernel x p (augmentedDiagonal β g) hdiag
      (fun b => by simpa only [varianceKernel,abs_of_nonneg (compactV_nonneg b)] using compactV_le_one b)
    have he : weightedForm (augmented β g) varianceKernel x p =
        weightedForm J varianceKernel x p+weightedForm (Matrix.diagonal (augmentedDiagonal β g)) varianceKernel x p := by
      have hmat : augmented β g = (Matrix.of J)+Matrix.diagonal (augmentedDiagonal β g) := by
        dsimp only [J]
        rw [coupling_augmentedDisorder]
        change augmented β g = (augmented β g - Matrix.diagonal (augmentedDiagonal β g)) + Matrix.diagonal (augmentedDiagonal β g)
        exact (sub_add_cancel _ _).symm
      rw [hmat]
      simp only [weightedForm,quadratic,Matrix.add_apply,add_mul,Finset.sum_add_distrib,Matrix.of_apply]
    dsimp [L]
    rw [he,sub_add_cancel_left,abs_neg]
    exact hd
  have hM : |M|≤a*(∑ i, p i^2) := by
    dsimp only [M]
    rw [weightedForm_sub]
    exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right (hm x)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hK : |K|≤a*(∑ i, p i^2) := by
    dsimp only [K]
    rw [weightedForm_sub]
    exact (quadratic_abs_le _ p).trans (mul_le_mul_of_nonneg_right (hk x)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hD : |D|≤(d+8*β^2/(n:ℝ))*(∑ i, p i^2) := by
    dsimp only [D]
    rw [diagonalForm_sub]
    apply diagonalForm_abs_le
    intro i
    change |∑ j, squareError β (augmentedDisorder β g) i j*compactF (x i,x j)|≤_
    rw [squareError_row]
    apply (abs_sub _ _).trans
    apply add_le_add (hf i)
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ))]
    have hh := mul_le_mul_of_nonneg_left (compactF_le_eight (x i) (x i))
      (show 0≤β^2/(n:ℝ) by positivity)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hid : compactForm J x p-reducedForm β g p=L+2*M+D+K := by
    dsimp [compactForm,reducedForm,L,M,D,K,x,Q,B]
    simp only [weightedForm,diagonalForm,Matrix.of_apply]
    ring
  change |compactForm J x p-reducedForm β g p| ≤ _
  rw [hid]
  have ht := (abs_add_le (L+2*M+D) K).trans
    (add_le_add ((abs_add_le (L+2*M) D).trans (add_le_add (abs_add_le L (2*M)) le_rfl)) le_rfl)
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
  nlinarith only [ht,hL,hM,hD,hK]

theorem reduced_error_rare_oai {β : ℝ} (hβ : 0<β) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ p : Fin n → ℝ, u*(∑ i, p i^2)<
        |gradientForm (coupling (augmentedDisorder β g)) p-reducedForm β g p|}) := by
  let K := 2*β+β^2+1
  have hK : 0≤K := by dsimp [K]; positivity
  let a := u/8
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨δ,hδ,hfield⟩ := compactForm_uniform_field_change (sq_nonneg K) hK ha
  have hN := augmented_norm_rare hβ (by norm_num : (0:ℝ)<1)
  have hD := augmented_diagonal_rare β (lt_min hδ ha)
  have hM := augmented_weighted_operator_rare β meanVarianceKernel continuous_meanVarianceKernel ha
  have hC := augmented_weighted_operator_rare β compactK continuous_compactK ha
  have hF := augmented_weighted_diagonal_rare compactF continuous_compactF compactWeight compactWeight_lipschitz β ha
  apply ((((hN.union hD).union hM).union hC).union hF).mono
  have ht : ∀ᶠ n : ℕ in atTop, 8*β^2/(n:ℝ)≤a :=
    ((tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (8*β^2)).eventually (gt_mem_nhds ha)).mono
      (fun _ hn => hn.le)
  filter_upwards [ht] with n hn
  rintro g ⟨p,hp⟩
  by_contra hb
  have hnorm : euclideanOpNorm (coupling (augmentedDisorder β g))≤K :=
    le_of_not_gt (fun h => hb (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  have hdiag : ∀ i, |augmentedDiagonal β g i|≤ min δ a :=
    fun i => le_of_not_gt (fun h => hb (Or.inl (Or.inl (Or.inl (Or.inr ⟨i,h⟩)))))
  have hm : ∀ x : Fin n → FieldWeight, euclideanOpNorm
      (fun i j => squareError β (augmentedDisorder β g) i j*meanVarianceKernel (x i,x j))≤a :=
    fun x => le_of_not_gt (fun h => hb (Or.inl (Or.inl (Or.inr ⟨x,h⟩))))
  have hk : ∀ x : Fin n → FieldWeight, euclideanOpNorm
      (fun i j => squareError β (augmentedDisorder β g) i j*compactK (x i,x j))≤a :=
    fun x => le_of_not_gt (fun h => hb (Or.inl (Or.inr ⟨x,h⟩)))
  have hf : ∀ i, |∑ e : incidentEdges i, (augmentedDisorder β g e^2-β^2/(n:ℝ))*
      compactF (compactWeight (augmentedField β g i),compactWeight (augmentedField β g (otherEnd i e)))|≤a :=
    fun i => le_of_not_gt (fun h => hb (Or.inr ⟨i,h⟩))
  let J := coupling (augmentedDisorder β g)
  have hefield (i : Fin n) : |(∑ j, J i j)-augmentedField β g i|≤δ := by
    rw [←diagonalField_augmented]
    change |(∑ j, J i j)-(augmentedDiagonal β g i+(∑ j, J i j))|≤δ
    rw [sub_add_cancel_right,abs_neg]
    exact (hdiag i).trans (min_le_left _ _)
  have h₁ := hfield J (coupling_symm _) hnorm
    (row_squares_le_opNorm J (coupling_symm _) hK hnorm) _ _ p hefield
  have h₂ := compactForm_reduced_error β g p (fun i => (hdiag i).trans (min_le_right _ _)) hm hk hf
  have hgrad := gradientForm_eq_compactForm J (coupling_symm _) (coupling_diag _) p
  rw [hgrad] at hp
  have habs := abs_sub_le (compactForm J (fun i => compactWeight (∑ j, J i j)) p)
    (compactForm J (fun i => compactWeight (augmentedField β g i)) p) (reducedForm β g p)
  have hnorm0 : 0≤∑ i, p i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hn hnorm0
  dsimp [a] at h₁ h₂ hh
  nlinarith only [hp,habs,h₁,h₂,hh,hu,hnorm0]

end SKRatio.Planted

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Planted.reduced_error_rare_oai := @OAI.SKRatio.Planted.reduced_error_rare_oai
