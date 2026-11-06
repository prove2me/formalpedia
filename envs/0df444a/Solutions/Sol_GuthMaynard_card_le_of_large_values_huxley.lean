-- Prove2me | solution 1 for GuthMaynard.card_le_of_large_values_huxley
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:28:28.940322+00:00
-- url     : https://prove2.me/submissions/b96478ff-ecef-42ba-9711-9a2cb54ce54f

import Mathlib
section
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.ExponentialSum

noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def phaseWeight (x : ℝ) : ℂ :=
  -(1 : ℂ) / 2 - (Real.cot (Real.pi * x) : ℂ) * Complex.I / 2

lemma phase_norm (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cot_antitone_unit {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    Real.cot (Real.pi * y) ≤ Real.cot (Real.pi * x) := by
  have hpi := Real.pi_pos
  have hxpi : 0 < Real.pi * x := mul_pos hpi hx
  have hypi : 0 < Real.pi * y := by nlinarith
  have hxpi' : Real.pi * x < Real.pi := by nlinarith
  have hypi' : Real.pi * y < Real.pi := by nlinarith
  have hsx := Real.sin_pos_of_pos_of_lt_pi hxpi hxpi'
  have hsy := Real.sin_pos_of_pos_of_lt_pi hypi hypi'
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ hsy hsx).2
  have hs : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith
  rw [Real.sin_sub] at hs
  nlinarith

lemma sin_pi_lower {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    2 * β ≤ Real.sin (Real.pi * x) := by
  have hp := Real.pi_pos
  by_cases hx : x ≤ 1 / 2
  · have h := Real.mul_le_sin (x := Real.pi * x) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at h
    linarith
  · have h := Real.mul_le_sin (x := Real.pi * (1 - x)) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq] at h
    have harg : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [harg, Real.sin_pi_sub] at h
    linarith

lemma abs_cot_pi_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    |Real.cot (Real.pi * x)| ≤ 1 / (2 * β) := by
  have hs := sin_pi_lower hβ hlo hhi
  have hsp : 0 < Real.sin (Real.pi * x) := by linarith
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsp]
  exact (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsp.le).trans
    (one_div_le_one_div_of_le (by positivity) hs)

lemma phaseWeight_identity {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (phase x - 1) * phaseWeight x = 1 := by
  have hs : Real.sin (Real.pi * x) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))
  unfold phase phaseWeight
  rw [Complex.exp_ofReal_mul_I]
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.cot_eq_cos_div_sin]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_div]
  have hsc : (Real.sin (Real.pi * x) : ℂ) ^ 2 + (Real.cos (Real.pi * x) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi * x)
  have hsC : (Real.sin (Real.pi * x) : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp
  ring_nf
  norm_num only [Complex.ofReal_one, Complex.I_sq]
  linear_combination -2 * (Real.cos (Real.pi * x) : ℂ) * Complex.I * hsc

lemma phaseWeight_norm_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    ‖phaseWeight x‖ ≤ 1 / 2 + 1 / (4 * β) := by
  have hc := abs_cot_pi_le hβ hlo hhi
  have hn2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  calc
    ‖phaseWeight x‖ ≤ ‖-(1 : ℂ) / 2‖ + ‖(Real.cot (Real.pi * x) : ℂ) * Complex.I / 2‖ :=
      norm_sub_le _ _
    _ = 1 / 2 + |Real.cot (Real.pi * x)| / 2 := by
      simp only [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, hn2, mul_one]
    _ ≤ 1 / 2 + (1 / (2 * β)) / 2 := by gcongr
    _ = 1 / 2 + 1 / (4 * β) := by ring

lemma phaseWeight_difference_norm {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    ‖phaseWeight x - phaseWeight y‖ =
      (Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 := by
  have hc := cot_antitone_unit hx hxy hy
  have heq : phaseWeight x - phaseWeight y =
      (((Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 : ℝ) : ℂ) * (-Complex.I) := by
    unfold phaseWeight
    push_cast
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

lemma phase_step_weight (f : ℕ → ℝ) (i : ℕ)
    (hlo : 0 < f (i + 1) - f i) (hhi : f (i + 1) - f i < 1) :
    (phase (f (i + 1)) - phase (f i)) * phaseWeight (f (i + 1) - f i) = phase (f i) := by
  have heq : phase (f (i + 1)) = phase (f i) * phase (f (i + 1) - f i) := by
    rw [← phase_add]
    congr 1
    ring
  rw [heq]
  calc
    (phase (f i) * phase (f (i + 1) - f i) - phase (f i)) *
        phaseWeight (f (i + 1) - f i) =
      phase (f i) * ((phase (f (i + 1) - f i) - 1) * phaseWeight (f (i + 1) - f i)) := by ring
    _ = phase (f i) := by rw [phaseWeight_identity hlo hhi, mul_one]

/-- Summation by parts for a sequence whose differences have a reciprocal weight. -/
lemma weighted_telescope (z w : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ i < N, (z (i + 1) - z i) * w i = z i) :
    (∑ i ∈ Finset.range N, z i) = z N * w N - z 0 * w 0 +
      ∑ i ∈ Finset.range N, z (i + 1) * (w i - w (i + 1)) := by
  calc
    (∑ i ∈ Finset.range N, z i) =
        ∑ i ∈ Finset.range N,
          ((z (i + 1) * w (i + 1) - z i * w i) + z (i + 1) * (w i - w (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hstep i (Finset.mem_range.mp hi)
      linear_combination -h
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun i => z i * w i)]

/-- Endpoint-efficient form: the last weight is attached to the last summand. -/
lemma weighted_telescope_succ (z w : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ i ≤ N, (z (i + 1) - z i) * w i = z i) :
    (∑ i ∈ Finset.range (N + 1), z i) = z (N + 1) * w N - z 0 * w 0 +
      ∑ i ∈ Finset.range N, z (i + 1) * (w i - w (i + 1)) := by
  rw [Finset.sum_range_succ, weighted_telescope z w N (fun i hi => hstep i hi.le)]
  have h := hstep N le_rfl
  linear_combination -h

/-- Cancellation using only the increments attached to the summands. -/
theorem first_derivative_sum_bound_succ (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i ≤ N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range (N + 1), phase (f i)‖ ≤ 2 / β := by
  let d : ℕ → ℝ := fun i => f (i + 1) - f i
  let w : ℕ → ℂ := fun i => phaseWeight (d i)
  have hdlo : ∀ i ≤ N, 0 < d i := fun i hi => lt_of_lt_of_le hβ (hlo i hi)
  have hdhi : ∀ i ≤ N, d i < 1 := by intro i hi; have := hhi i hi; dsimp [d]; linarith
  have htel := weighted_telescope_succ (fun i => phase (f i)) w N (by
    intro i hi
    exact phase_step_weight f i (hdlo i hi) (hdhi i hi))
  have hvariation : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
      (Real.cot (Real.pi * d 0) - Real.cot (Real.pi * d N)) / 2 := by
    calc
      (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
          ∑ i ∈ Finset.range N,
            (Real.cot (Real.pi * d i) - Real.cot (Real.pi * d (i + 1))) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < N := Finset.mem_range.mp hi
        exact phaseWeight_difference_norm (hdlo i hiN.le)
          (hmono (show i ≤ N from hiN.le) (show i + 1 ≤ N by omega) (by omega)) (hdhi (i + 1) (by omega))
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub']
  have hc0 := abs_cot_pi_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hcN := abs_cot_pi_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hvbound : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) ≤ 1 / (2 * β) := by
    rw [hvariation]
    have h0 := (abs_le.mp hc0).2
    have hN := (abs_le.mp hcN).1
    change Real.cot (Real.pi * d 0) ≤ _ at h0
    change _ ≤ Real.cot (Real.pi * d N) at hN
    linarith
  have hw0 := phaseWeight_norm_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hwN := phaseWeight_norm_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hsum : ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ ≤
      ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, ‖phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, phase_norm, one_mul]
  have hβle : β ≤ 1 := by have := hlo 0 (Nat.zero_le N); have := hhi 0 (Nat.zero_le N); linarith
  have hinv : 1 ≤ 1 / β := (le_div_iff₀ hβ).2 (by simpa using hβle)
  rw [htel]
  calc
    _ ≤ ‖phase (f (N + 1)) * w N - phase (f 0) * w 0‖ +
        ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_add_le _ _
    _ ≤ (‖phase (f (N + 1)) * w N‖ + ‖phase (f 0) * w 0‖) +
        ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := add_le_add (norm_sub_le _ _) hsum
    _ = (‖w N‖ + ‖w 0‖) + ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
      simp only [norm_mul, phase_norm, one_mul]
    _ ≤ (1 / 2 + 1 / (4 * β)) + (1 / 2 + 1 / (4 * β)) + 1 / (2 * β) := by
      exact add_le_add (add_le_add hwN hw0) hvbound
    _ = 1 + 1 / β := by ring
    _ ≤ 1 / β + 1 / β := by simpa [add_comm] using add_le_add_right hinv (1 / β)
    _ = 2 / β := by ring

lemma phase_int (q : ℤ) : phase (q : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I q using 2
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

lemma phase_neg (x : ℝ) : phase (-x) = (starRingEnd ℂ) (phase x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma phase_sub_int_mul (x : ℝ) (q : ℤ) (n : ℕ) :
    phase (x - (q : ℝ) * n) = phase x := by
  have heq : x - (q : ℝ) * n = x + ((-(q * (n : ℤ)) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [heq, phase_add, phase_int, mul_one]

theorem first_derivative_sum_bound_strip_succ (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (q : ℤ)
    (hβ : 0 < β)
    (hlo : ∀ i ≤ N, (q : ℝ) + β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range (N + 1), phase (f i)‖ ≤ 2 / β := by
  let g : ℕ → ℝ := fun i => f i - (q : ℝ) * i
  have hg : ∀ i, g (i + 1) - g i = (f (i + 1) - f i) - q := by
    intro i
    dsimp [g]
    push_cast
    ring
  have H := first_derivative_sum_bound_succ g N β hβ
    (by intro i hi; rw [hg]; have := hlo i hi; linarith)
    (by intro i hi; rw [hg]; have := hhi i hi; linarith)
    (by
      intro i hi j hj hij
      dsimp only
      rw [hg, hg]
      exact sub_le_sub_right (hmono hi hj hij) _)
  simpa only [g, phase_sub_int_mul] using H

/-- Both directions of monotonicity are allowed in the discrete
first-derivative estimate. -/
theorem first_derivative_sum_bound_either_succ (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (q : ℤ)
    (hβ : 0 < β)
    (hlo : ∀ i ≤ N, (q : ℝ) + β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N) ∨
      AntitoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range (N + 1), phase (f i)‖ ≤ 2 / β := by
  rcases hmono with hmono | hanti
  · exact first_derivative_sum_bound_strip_succ f N β q hβ hlo hhi hmono
  · have H := first_derivative_sum_bound_strip_succ (fun i => -f i) N β (-q - 1) hβ
      (by intro i hi; push_cast; have := hhi i hi; linarith)
      (by intro i hi; push_cast; have := hlo i hi; linarith)
      (by
        intro i hi j hj hij
        have := hanti hi hj hij
        dsimp only
        linarith)
    simpa only [phase_neg, ← map_sum, Complex.norm_conj] using H

/-- The first-derivative bound on a contiguous block of natural indices. -/
theorem first_derivative_sum_bound_Icc (f : ℕ → ℝ) (a b : ℕ) (β : ℝ) (q : ℤ)
    (hβ : 0 < β)
    (hlo : ∀ i, a ≤ i → i ≤ b → (q : ℝ) + β ≤ f (i + 1) - f i)
    (hhi : ∀ i, a ≤ i → i ≤ b → f (i + 1) - f i ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Icc a b) ∨
      AntitoneOn (fun i => f (i + 1) - f i) (Set.Icc a b)) :
    ‖∑ i ∈ Finset.Icc a b, phase (f i)‖ ≤ 2 / β := by
  by_cases hab : a ≤ b
  · have H := first_derivative_sum_bound_either_succ (fun i => f (a + i)) (b - a) β q hβ
      (by
        intro i hi
        simpa only [Nat.add_assoc] using hlo (a + i) (by omega) (by omega))
      (by
        intro i hi
        simpa only [Nat.add_assoc] using hhi (a + i) (by omega) (by omega))
      (by
        rcases hmono with hm | hm
        · left
          intro i hi j hj hij
          dsimp only
          simpa only [Nat.add_assoc] using hm
            (show a + i ∈ Set.Icc a b by constructor <;> simp only [Set.mem_Iic] at hi hj <;> omega)
            (show a + j ∈ Set.Icc a b by constructor <;> simp only [Set.mem_Iic] at hi hj <;> omega)
            (show a + i ≤ a + j by omega)
        · right
          intro i hi j hj hij
          dsimp only
          simpa only [Nat.add_assoc] using hm
            (show a + i ∈ Set.Icc a b by constructor <;> simp only [Set.mem_Iic] at hi hj <;> omega)
            (show a + j ∈ Set.Icc a b by constructor <;> simp only [Set.mem_Iic] at hi hj <;> omega)
            (show a + i ≤ a + j by omega))
    have hset : Finset.Icc a b = Finset.Ico a (b + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hlen : b + 1 - a = b - a + 1 := by omega
    rw [hlen]
    exact H
  · have he : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [he]
    simp only [Finset.sum_empty, norm_zero]
    positivity

end Problem337.ExponentialSum

end OAI
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section
/-!
# Blueprint: Huxley 1972 (2.9), the Montgomery–Halász–Huxley large values estimate

Route (elementary, no ζ):
* `partial_sum_cpow_le` (van der Corput second-derivative test via Kusmin–Landau):
  `|∑_{m ≤ c} m^{-it}| ≪ |t|^{1/2} log(|t|+2)` for `c ≤ 11|t|+2`.
* `block_sum_sub_integral_le` (sum vs integral on a dyadic block where the phase is slow).
* `kernel_bound`: the tent-weighted kernel `K(s) = ∑ w(m) m^{-s}` is
  `≪ N/t² + |t|^{1/2} log(|t|+2) + log(N+2)`.
* `halasz_ineq`, `sum_inv_sq_le_of_separated`, `card_le_of_separated`, `card_le_of_halasz`:
  Halász–Montgomery, giving `R ≪ GN/V²` when `V² ≫ G (T^{1/2} log(T+2) + log(N+2))`.
* `huxley_main`: subdivision of the `t`-range into pieces of length `T₀`.
-/
/-- The tent weight: `1` on `x ≤ N`, `2 - x/N` on `[N, 2N]`, `0` beyond. -/
def tentW (N : ℕ) (x : ℝ) : ℝ := if x ≤ N then 1 else if x ≤ 2 * N then 2 - x / N else 0

/-- The Halász–Montgomery kernel `∑_{1 ≤ m ≤ 2N} w(m) m^{-s}`. -/
def kernel (N : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (2 * N), ((tentW N m : ℝ) : ℂ) * (m : ℂ) ^ (-s)

/-- The Dirichlet polynomial `∑_{1 ≤ m ≤ N} a(m) m^{-s}`. -/
def dirPoly (N : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ := ∑ m ∈ Finset.Icc 1 N, a m * (m : ℂ) ^ (-s)

end
end GuthMaynard.CitedLV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.PartV
open OAI.Problem337.ExponentialSum
noncomputable section
/-!
# Part V: `|∑_{m ≤ c} m^{-it}| ≪ |t|^{1/2} log(|t|+2)` for `c ≤ 11|t|+2`

Van der Corput's second-derivative test, derived from the Kusmin–Landau inequality
`OAI.Problem337.ExponentialSum.first_derivative_sum_bound_Icc`.

* `one_round`: on a block where the increments `d(i) = f(i+1)-f(i)` grow by at least `λ` per step and
  stay in `[k, k+1]`, the sum is at most `2(δ/λ+1) + 2/δ` (two short ends bounded trivially, the middle
  by Kusmin–Landau).
* `multi_round`, `sd_bound`: chaining rounds, `|S| ≤ (d(b)-d(a)+2)(2(δ/λ+1)+2/δ)`.
* `block_bound`: for `f(m) = -(t/2π) log m` on a block `[a, b]` with `√t ≤ a`, `b < 2a`, `b + 1 ≤ 14t`,
  the sum is at most `500 √t`.
* `dyadic`: blocks `[A 2^j, A 2^{j+1})` with `A = ⌈√t⌉`; the first `A - 1` terms are bounded trivially.
-/
lemma norm_sum_phase_le_card (f : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ i ∈ s, phase (f i)‖ ≤ s.card := by
  calc _ ≤ ∑ i ∈ s, ‖phase (f i)‖ := norm_sum_le _ _
    _ = s.card := by simp [phase_norm]

lemma step_accum (d : ℕ → ℝ) (a b : ℕ) (lam : ℝ)
    (hstep : ∀ i, a ≤ i → i < b → d i + lam ≤ d (i + 1)) :
    ∀ k : ℕ, a + k ≤ b → d a + k * lam ≤ d (a + k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hstep (a + k) (by omega) (by omega)
    rw [show a + (k + 1) = a + k + 1 by omega]
    push_cast
    linarith

/-- Accumulated growth between two indices of the block. -/
lemma step_accum' (d : ℕ → ℝ) (a b : ℕ) (lam : ℝ)
    (hstep : ∀ i, a ≤ i → i < b → d i + lam ≤ d (i + 1)) (i j : ℕ) (hai : a ≤ i) (hij : i ≤ j)
    (hjb : j ≤ b) : d i + ((j - i : ℕ) : ℝ) * lam ≤ d j := by
  have := step_accum d i b lam (fun l hl1 hl2 => hstep l (by omega) hl2) (j - i) (by omega)
  rwa [show i + (j - i) = j by omega] at this

lemma one_round (f : ℕ → ℝ) (a b : ℕ) (lam δ : ℝ) (k : ℤ) (hlam : 0 < lam) (hδ : 0 < δ)
    (hab : a ≤ b)
    (hstep : ∀ i, a ≤ i → i < b → (f (i + 1) - f i) + lam ≤ (f (i + 1 + 1) - f (i + 1)))
    (hk0 : (k : ℝ) ≤ f (a + 1) - f a) (hk1 : f (b + 1) - f b ≤ k + 1) :
    ‖∑ i ∈ Ico a (b + 1), phase (f i)‖ ≤ 2 * (δ / lam + 1) + 2 / δ := by
  set d : ℕ → ℝ := fun i => f (i + 1) - f i with hd
  have hst : ∀ i, a ≤ i → i < b → d i + lam ≤ d (i + 1) := hstep
  set L := ⌈δ / lam⌉₊ with hL
  have hL1 : δ / lam ≤ L := Nat.le_ceil _
  have hL2 : (L : ℝ) < δ / lam + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLl : δ ≤ L * lam := by rwa [div_le_iff₀ hlam] at hL1
  have h2δ : 0 ≤ 2 / δ := by positivity
  by_cases hlen : b + 1 < a + 2 * L
  · calc _ ≤ ((Ico a (b + 1)).card : ℝ) := norm_sum_phase_le_card _ _
      _ ≤ 2 * L := by
        rw [Nat.card_Ico]; exact_mod_cast (show b + 1 - a ≤ 2 * L by omega)
      _ ≤ _ := by linarith
  · push Not at hlen
    have hsplit : ∑ i ∈ Ico a (b + 1), phase (f i) =
        (∑ i ∈ Ico a (a + L), phase (f i) + ∑ i ∈ Ico (a + L) (b + 1 - L), phase (f i)) +
          ∑ i ∈ Ico (b + 1 - L) (b + 1), phase (f i) := by
      rw [Finset.sum_Ico_consecutive _ (by omega) (by omega),
        Finset.sum_Ico_consecutive _ (by omega) (by omega)]
    have hfirst : ‖∑ i ∈ Ico a (a + L), phase (f i)‖ ≤ L := by
      calc _ ≤ ((Ico a (a + L)).card : ℝ) := norm_sum_phase_le_card _ _
        _ = L := by rw [Nat.card_Ico]; congr 1; omega
    have hlast : ‖∑ i ∈ Ico (b + 1 - L) (b + 1), phase (f i)‖ ≤ L := by
      calc _ ≤ ((Ico (b + 1 - L) (b + 1)).card : ℝ) := norm_sum_phase_le_card _ _
        _ = L := by rw [Nat.card_Ico]; congr 1; omega
    have hmid : ‖∑ i ∈ Ico (a + L) (b + 1 - L), phase (f i)‖ ≤ 2 / δ := by
      by_cases hpq : a + L < b + 1 - L
      · have hIcc : Ico (a + L) (b + 1 - L) = Icc (a + L) (b - L) := by
          ext i; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
        rw [hIcc]
        refine first_derivative_sum_bound_Icc f (a + L) (b - L) δ k hδ ?_ ?_ (Or.inl ?_)
        · intro i hi1 hi2
          have h := step_accum' d a b lam hst a i le_rfl (by omega) (by omega)
          have hc : (L : ℝ) ≤ ((i - a : ℕ) : ℝ) := by exact_mod_cast (show L ≤ i - a by omega)
          have : (L : ℝ) * lam ≤ ((i - a : ℕ) : ℝ) * lam := mul_le_mul_of_nonneg_right hc hlam.le
          change (k : ℝ) + δ ≤ d i
          change (k : ℝ) ≤ d a at hk0
          linarith
        · intro i hi1 hi2
          have h := step_accum' d a b lam hst i b (by omega) (by omega) le_rfl
          have hc : (L : ℝ) ≤ ((b - i : ℕ) : ℝ) := by exact_mod_cast (show L ≤ b - i by omega)
          have : (L : ℝ) * lam ≤ ((b - i : ℕ) : ℝ) * lam := mul_le_mul_of_nonneg_right hc hlam.le
          change d i ≤ (k : ℝ) + 1 - δ
          change d b ≤ (k : ℝ) + 1 at hk1
          linarith
        · intro i hi j hj hij
          simp only [Set.mem_Icc] at hi hj
          have h := step_accum' d a b lam hst i j (by omega) hij (by omega)
          have : 0 ≤ ((j - i : ℕ) : ℝ) * lam := by positivity
          change d i ≤ d j
          linarith
      · rw [Finset.Ico_eq_empty_of_le (by omega)]
        simpa using h2δ
    rw [hsplit]
    calc _ ≤ ‖∑ i ∈ Ico a (a + L), phase (f i) + ∑ i ∈ Ico (a + L) (b + 1 - L), phase (f i)‖ +
          ‖∑ i ∈ Ico (b + 1 - L) (b + 1), phase (f i)‖ := norm_add_le _ _
      _ ≤ (‖∑ i ∈ Ico a (a + L), phase (f i)‖ + ‖∑ i ∈ Ico (a + L) (b + 1 - L), phase (f i)‖) +
          ‖∑ i ∈ Ico (b + 1 - L) (b + 1), phase (f i)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (L + 2 / δ) + L := by gcongr
      _ ≤ _ := by linarith

lemma multi_round (f : ℕ → ℝ) (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) :
    ∀ n : ℕ, ∀ a b : ℕ, a ≤ b →
    (∀ i, a ≤ i → i < b → (f (i + 1) - f i) + lam ≤ (f (i + 1 + 1) - f (i + 1))) →
    ⌊f (b + 1) - f b⌋ - ⌊f (a + 1) - f a⌋ ≤ (n : ℤ) →
    ‖∑ i ∈ Ico a (b + 1), phase (f i)‖ ≤ (n + 1) * (2 * (δ / lam + 1) + 2 / δ) := by
  have hK : 0 ≤ 2 * (δ / lam + 1) + 2 / δ := by positivity
  intro n
  induction n with
  | zero =>
    intro a b hab hstep hfl
    have h1 : ⌊f (b + 1) - f b⌋ ≤ ⌊f (a + 1) - f a⌋ := by push_cast at hfl; omega
    have h2 : ((⌊f (b + 1) - f b⌋ : ℤ) : ℝ) ≤ ⌊f (a + 1) - f a⌋ := by exact_mod_cast h1
    have h3 := Int.lt_floor_add_one (f (b + 1) - f b)
    have := one_round f a b lam δ ⌊f (a + 1) - f a⌋ hlam hδ hab hstep (Int.floor_le _)
      (by linarith)
    simpa using this
  | succ n ih =>
    intro a b hab hstep hfl
    by_cases hb : f (b + 1) - f b ≤ ⌊f (a + 1) - f a⌋ + 1
    · have := one_round f a b lam δ ⌊f (a + 1) - f a⌋ hlam hδ hab hstep (Int.floor_le _) hb
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast
      nlinarith
    · push Not at hb
      set k := ⌊f (a + 1) - f a⌋ with hk
      have hex : ∃ j : ℕ, (k : ℝ) + 1 ≤ f (a + j + 1) - f (a + j) :=
        ⟨b - a, by rw [show a + (b - a) = b by omega]; linarith⟩
      classical
      have hj0 := Nat.find_spec hex
      have hj0pos : Nat.find hex ≠ 0 := by
        intro h
        rw [h] at hj0
        simp only [Nat.add_zero] at hj0
        have := Int.lt_floor_add_one (f (a + 1) - f a)
        rw [← hk] at this
        linarith
      have hj0le : Nat.find hex ≤ b - a := Nat.find_min' hex (by
        rw [show a + (b - a) = b by omega]; linarith)
      have hprev : f (a + (Nat.find hex - 1) + 1) - f (a + (Nat.find hex - 1)) < k + 1 := by
        have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        push Not at this
        exact this
      have h1 := one_round f a (a + (Nat.find hex - 1)) lam δ k hlam hδ (by omega)
        (fun i hi1 hi2 => hstep i hi1 (by omega)) (Int.floor_le _) hprev.le
      have h2 := ih (a + Nat.find hex) b (by omega) (fun i hi1 hi2 => hstep i (by omega) hi2) (by
        have : k + 1 ≤ ⌊f (a + Nat.find hex + 1) - f (a + Nat.find hex)⌋ :=
          Int.le_floor.mpr (by push_cast; exact hj0)
        push_cast at hfl ⊢
        omega)
      have hsplit : ∑ i ∈ Ico a (b + 1), phase (f i) =
          ∑ i ∈ Ico a (a + (Nat.find hex - 1) + 1), phase (f i) +
            ∑ i ∈ Ico (a + Nat.find hex) (b + 1), phase (f i) := by
        rw [show a + (Nat.find hex - 1) + 1 = a + Nat.find hex by omega]
        exact (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
      rw [hsplit]
      calc _ ≤ ‖∑ i ∈ Ico a (a + (Nat.find hex - 1) + 1), phase (f i)‖ +
            ‖∑ i ∈ Ico (a + Nat.find hex) (b + 1), phase (f i)‖ := norm_add_le _ _
        _ ≤ (2 * (δ / lam + 1) + 2 / δ) + (n + 1) * (2 * (δ / lam + 1) + 2 / δ) :=
          add_le_add h1 h2
        _ = _ := by push_cast; ring

/-- Van der Corput's second-derivative test in increment form. -/
lemma sd_bound (f : ℕ → ℝ) (a b : ℕ) (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hab : a ≤ b)
    (hstep : ∀ i, a ≤ i → i < b → (f (i + 1) - f i) + lam ≤ (f (i + 1 + 1) - f (i + 1))) :
    ‖∑ i ∈ Ico a (b + 1), phase (f i)‖ ≤
      ((f (b + 1) - f b) - (f (a + 1) - f a) + 2) * (2 * (δ / lam + 1) + 2 / δ) := by
  have hK : 0 ≤ 2 * (δ / lam + 1) + 2 / δ := by positivity
  have hmono : f (a + 1) - f a ≤ f (b + 1) - f b := by
    have h := step_accum' (fun i => f (i + 1) - f i) a b lam hstep a b le_rfl hab le_rfl
    have : 0 ≤ ((b - a : ℕ) : ℝ) * lam := by positivity

    linarith
  have hfl0 : ⌊f (a + 1) - f a⌋ ≤ ⌊f (b + 1) - f b⌋ := Int.floor_mono hmono
  set n := (⌊f (b + 1) - f b⌋ - ⌊f (a + 1) - f a⌋).toNat with hn
  have hnz : (n : ℤ) = ⌊f (b + 1) - f b⌋ - ⌊f (a + 1) - f a⌋ := Int.toNat_of_nonneg (by omega)
  have H := multi_round f lam δ hlam hδ n a b hab hstep (by omega)
  have hnr : (n : ℝ) = ((⌊f (b + 1) - f b⌋ - ⌊f (a + 1) - f a⌋ : ℤ) : ℝ) := by
    rw [← hnz]; simp
  have hle : (n : ℝ) + 1 ≤ (f (b + 1) - f b) - (f (a + 1) - f a) + 2 := by
    rw [hnr]
    push_cast
    have := Int.floor_le (f (b + 1) - f b)
    have := Int.lt_floor_add_one (f (a + 1) - f a)
    linarith
  calc _ ≤ _ := H
    _ ≤ _ := mul_le_mul_of_nonneg_right hle hK

/-! ## The concrete phase `f(m) = -(t/2π) log m` -/
/-- The phase of `m^{-it}`. -/
def ph (t : ℝ) (m : ℕ) : ℝ := -(t / (2 * Real.pi)) * Real.log m

lemma cpow_eq_phase (t : ℝ) (m : ℕ) (hm : m ≠ 0) :
    (m : ℂ) ^ (-((t : ℂ) * I)) = phase (ph t m) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hm)]
  unfold phase ph
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg m)]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

lemma log_second_diff (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 2 * Real.log (x + 1) - Real.log x - Real.log (x + 1 + 1) := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < (x + 1) ^ 2 / (x * (x + 1 + 1)) by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at h
  have he : 1 - ((x + 1) ^ 2 / (x * (x + 1 + 1)))⁻¹ = 1 / (x + 1) ^ 2 := by
    field_simp
    ring
  rw [he] at h
  push_cast at h
  linarith

lemma ph_step (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m) :
    (ph t (m + 1) - ph t m) + t / (2 * Real.pi) * (1 / ((m : ℝ) + 1) ^ 2) ≤
      ph t (m + 1 + 1) - ph t (m + 1) := by
  have hx : (0 : ℝ) < m := by exact_mod_cast hm
  have h := log_second_diff (m : ℝ) hx
  have hc : 0 < t / (2 * Real.pi) := by positivity
  have key : (ph t (m + 1 + 1) - ph t (m + 1)) - (ph t (m + 1) - ph t m) =
      t / (2 * Real.pi) * (2 * Real.log ((m : ℝ) + 1) - Real.log m - Real.log ((m : ℝ) + 1 + 1)) := by
    unfold ph; push_cast; ring
  have := mul_le_mul_of_nonneg_left h hc.le
  linarith

lemma ph_range (t : ℝ) (ht : 0 < t) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (ph t (b + 1) - ph t b) - (ph t (a + 1) - ph t a) ≤ t / a := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (le_trans ha hab)
  have hc : 0 < t / (2 * Real.pi) := by positivity
  have h1 : Real.log b ≤ Real.log ((b : ℝ) + 1) := Real.log_le_log hbpos (by linarith)
  have h2 : Real.log ((a : ℝ) + 1) - Real.log a ≤ 1 / a := by
    rw [← Real.log_div (by positivity) hapos.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < ((a : ℝ) + 1) / a by positivity)
    have he : ((a : ℝ) + 1) / a - 1 = 1 / a := by field_simp; ring
    linarith
  have key : (ph t (b + 1) - ph t b) - (ph t (a + 1) - ph t a) =
      -(t / (2 * Real.pi)) * (Real.log ((b : ℝ) + 1) - Real.log b) +
        t / (2 * Real.pi) * (Real.log ((a : ℝ) + 1) - Real.log a) := by
    unfold ph; push_cast; ring
  rw [key]
  have e1 : 0 ≤ t / (2 * Real.pi) * (Real.log ((b : ℝ) + 1) - Real.log b) :=
    mul_nonneg hc.le (by linarith)
  have e2 : t / (2 * Real.pi) * (Real.log ((a : ℝ) + 1) - Real.log a) ≤
      t / (2 * Real.pi) * (1 / a) := mul_le_mul_of_nonneg_left h2 hc.le
  have e3 : t / (2 * Real.pi) * (1 / a) ≤ t / a := by
    rw [div_mul_div_comm, mul_one]
    apply div_le_div_of_nonneg_left ht.le hapos
    have := Real.pi_gt_three
    nlinarith
  linarith

lemma final_arith (s p q : ℝ) (hs : 1 ≤ s) (hp : s ≤ p) (hq : q ≤ 2 * p) (hq' : q ≤ 14 * (s * s))
    (_hq0 : 0 < q) :
    (s * s / p + 2) * (15 * q / s + 2) ≤ 500 * s := by
  have hs0 : 0 < s := by linarith
  have hp0 : 0 < p := by linarith
  have e : (s * s / p + 2) * (15 * q / s + 2) =
      15 * s * (q / p) + 2 * s * (s / p) + 30 * (q / s) + 4 := by
    field_simp; ring
  rw [e]
  have h1 : q / p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  have h2 : s / p ≤ 1 := by rw [div_le_iff₀ hp0]; linarith
  have h3 : q / s ≤ 14 * s := by rw [div_le_iff₀ hs0]; linarith
  have h1' : 15 * s * (q / p) ≤ 15 * s * 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h2' : 2 * s * (s / p) ≤ 2 * s * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

lemma block_bound (t : ℝ) (ht : 1 ≤ t) (a b : ℕ) (hab : a ≤ b) (ha : Real.sqrt t ≤ a)
    (hb2 : b + 1 ≤ 2 * a) (hbt : (b : ℝ) + 1 ≤ 14 * t) :
    ‖∑ i ∈ Ico a (b + 1), phase (ph t i)‖ ≤ 500 * Real.sqrt t := by
  set s := Real.sqrt t with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr ht
  have hss : s * s = t := Real.mul_self_sqrt (by linarith)
  have ht0 : 0 < t := by linarith
  have ha1 : 1 ≤ a := by
    have : (1 : ℝ) ≤ a := le_trans hs1 ha
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have hs0 : 0 < s := by linarith
  set lam := t / (2 * Real.pi) * (1 / ((b : ℝ) + 1) ^ 2) with hlam
  set δ := s / ((b : ℝ) + 1) with hδ
  have hlam0 : 0 < lam := by positivity
  have hδ0 : 0 < δ := by positivity
  have H := sd_bound (ph t) a b lam δ hlam0 hδ0 hab (by
    intro i hi1 hi2
    have h := ph_step t ht0 i (by omega)
    have hmono : 1 / ((b : ℝ) + 1) ^ 2 ≤ 1 / ((i : ℝ) + 1) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (i : ℝ) + 1 ≤ (b : ℝ) + 1 := by
        have : (i : ℝ) ≤ b := by exact_mod_cast hi2.le
        linarith
      gcongr
    have : lam ≤ t / (2 * Real.pi) * (1 / ((i : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    linarith)
  have hR := ph_range t ht0 a b ha1 hab
  have hK : 2 * (δ / lam + 1) + 2 / δ ≤ 15 * ((b : ℝ) + 1) / s + 2 := by
    have e1 : δ / lam = 2 * Real.pi * ((b : ℝ) + 1) / s := by
      rw [hδ, hlam, ← hss]
      field_simp
    have e2 : 2 / δ = 2 * ((b : ℝ) + 1) / s := by
      rw [hδ]; field_simp
    rw [e1, e2]
    have hpi := Real.pi_lt_d2
    have : 2 * (2 * Real.pi * ((b : ℝ) + 1) / s + 1) + 2 * ((b : ℝ) + 1) / s =
        (4 * Real.pi + 2) * (((b : ℝ) + 1) / s) + 2 := by ring
    rw [this, show 15 * ((b : ℝ) + 1) / s = 15 * (((b : ℝ) + 1) / s) by ring]
    have : 0 ≤ ((b : ℝ) + 1) / s := by positivity
    nlinarith
  have hK0 : 0 ≤ 2 * (δ / lam + 1) + 2 / δ := by positivity
  have hD0 : 0 ≤ t / a + 2 := by positivity
  calc _ ≤ _ := H
    _ ≤ (t / a + 2) * (15 * ((b : ℝ) + 1) / s + 2) :=
      mul_le_mul (by linarith) hK hK0 hD0
    _ = (s * s / a + 2) * (15 * ((b : ℝ) + 1) / s + 2) := by rw [hss]
    _ ≤ 500 * s := by
      apply final_arith s a ((b : ℝ) + 1) hs1 ha _ (by rw [hss]; exact hbt) hq0
      exact_mod_cast hb2

lemma dyadic (t : ℝ) (ht : 1 ≤ t) (A c : ℕ) (hA : Real.sqrt t ≤ A) (hc : (c : ℝ) + 1 ≤ 14 * t) :
    ∀ j e : ℕ, e ≤ A * 2 ^ j → e ≤ c + 1 →
      ‖∑ i ∈ Ico A e, phase (ph t i)‖ ≤ j * (500 * Real.sqrt t) := by
  intro j
  induction j with
  | zero =>
    intro e he _
    rw [Finset.Ico_eq_empty_of_le (by simpa using he)]
    simp
  | succ j ih =>
    intro e he hec
    have hB : 0 ≤ 500 * Real.sqrt t := by positivity
    by_cases hej : e ≤ A * 2 ^ j
    · calc _ ≤ _ := ih e hej hec
        _ ≤ ((j + 1 : ℕ) : ℝ) * (500 * Real.sqrt t) := by
          apply mul_le_mul_of_nonneg_right _ hB; push_cast; linarith
    · push Not at hej
      have hA2 : A ≤ A * 2 ^ j := Nat.le_mul_of_pos_right A (by positivity)
      have hsplit : ∑ i ∈ Ico A e, phase (ph t i) =
          ∑ i ∈ Ico A (A * 2 ^ j), phase (ph t i) + ∑ i ∈ Ico (A * 2 ^ j) (e - 1 + 1), phase (ph t i) := by
        rw [show e - 1 + 1 = e by omega]
        exact (Finset.sum_Ico_consecutive _ hA2 hej.le).symm
      have h1 := ih (A * 2 ^ j) le_rfl (by omega)
      have h2 := block_bound t ht (A * 2 ^ j) (e - 1) (by omega)
        (by
          have : (A : ℝ) ≤ ((A * 2 ^ j : ℕ) : ℝ) := by exact_mod_cast hA2
          linarith)
        (by
          have : A * 2 ^ (j + 1) = 2 * (A * 2 ^ j) := by ring
          omega)
        (by
          have : ((e - 1 : ℕ) : ℝ) ≤ c := by exact_mod_cast (show e - 1 ≤ c by omega)
          linarith)
      rw [hsplit]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ j * (500 * Real.sqrt t) + 500 * Real.sqrt t := add_le_add h1 h2
        _ = _ := by push_cast; ring

lemma one_le_log (t : ℝ) (ht : 1 ≤ t) : 1 ≤ Real.log (t + 2) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma natlog_le (t : ℝ) (ht : 1 ≤ t) (c : ℕ) (hc : (c : ℝ) ≤ 11 * t + 2) :
    (Nat.log 2 c : ℝ) ≤ 6 * Real.log (t + 2) := by
  have hL := one_le_log t ht
  by_cases hc0 : c = 0
  · subst hc0; simp; linarith
  have h2 : ((2 : ℝ)) ^ Nat.log 2 c ≤ c := by exact_mod_cast Nat.pow_log_le_self 2 hc0
  have h4 : 11 * t + 2 ≤ (t + 2) ^ 4 := by
    have h3 : (3 : ℝ) ^ 3 ≤ (t + 2) ^ 3 := by gcongr; linarith
    have : (t + 2) ^ 4 = (t + 2) * (t + 2) ^ 3 := by ring
    rw [this]
    nlinarith
  have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 c) ≤ Real.log ((t + 2) ^ 4) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_pow, Real.log_pow] at hlog
  have := Real.log_two_gt_d9
  have hn : (0 : ℝ) ≤ Nat.log 2 c := Nat.cast_nonneg _
  push_cast at hlog
  nlinarith

lemma main_pos (t : ℝ) (ht : 1 ≤ t) (c : ℕ) (hc : (c : ℝ) ≤ 11 * t + 2) :
    ‖∑ m ∈ Icc 1 c, phase (ph t m)‖ ≤ 3502 * (Real.sqrt t * Real.log (t + 2)) := by
  set s := Real.sqrt t with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr ht
  have hL := one_le_log t ht
  have hsL : s ≤ s * Real.log (t + 2) := by nlinarith
  set A := ⌈s⌉₊ with hA
  have hA1 : s ≤ A := Nat.le_ceil _
  have hA2 : (A : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hA0 : 1 ≤ A := by
    have : (1 : ℝ) ≤ A := by linarith
    exact_mod_cast this
  have hIcc : Icc 1 c = Ico 1 (c + 1) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  have hc14 : (c : ℝ) + 1 ≤ 14 * t := by linarith
  by_cases hcA : c + 1 ≤ A
  · calc _ ≤ ((Ico 1 (c + 1)).card : ℝ) := norm_sum_phase_le_card _ _
      _ ≤ A := by rw [Nat.card_Ico]; exact_mod_cast (show c + 1 - 1 ≤ A by omega)
      _ ≤ 3502 * (s * Real.log (t + 2)) := by nlinarith
  · push Not at hcA
    have hsplit : ∑ i ∈ Ico 1 (c + 1), phase (ph t i) =
        ∑ i ∈ Ico 1 A, phase (ph t i) + ∑ i ∈ Ico A (c + 1), phase (ph t i) :=
      (Finset.sum_Ico_consecutive _ hA0 hcA.le).symm
    have h1 : ‖∑ i ∈ Ico 1 A, phase (ph t i)‖ ≤ s := by
      calc _ ≤ ((Ico 1 A).card : ℝ) := norm_sum_phase_le_card _ _
        _ = ((A - 1 : ℕ) : ℝ) := by rw [Nat.card_Ico]
        _ ≤ s := by rw [Nat.cast_sub hA0]; push_cast; linarith
    have hpow : c + 1 ≤ A * 2 ^ (Nat.log 2 c + 1) := by
      have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) c
      have : 2 ^ (Nat.log 2 c + 1) ≤ A * 2 ^ (Nat.log 2 c + 1) := Nat.le_mul_of_pos_left _ hA0
      omega
    have h2 := dyadic t ht A c hA1 hc14 (Nat.log 2 c + 1) (c + 1) hpow le_rfl
    have hn := natlog_le t ht c hc
    rw [hsplit]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ s + ((Nat.log 2 c + 1 : ℕ) : ℝ) * (500 * s) := add_le_add h1 h2
      _ ≤ 3502 * (s * Real.log (t + 2)) := by
        push_cast
        have hs0 : 0 ≤ s := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hn hs0]

theorem partial_sum_cpow_le : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| → ∀ c : ℕ,
    (c : ℝ) ≤ 11 * |t| + 2 →
    ‖∑ m ∈ Finset.Icc 1 c, (m : ℂ) ^ (-((t : ℂ) * I))‖ ≤
      C * (|t| ^ (1 / 2 : ℝ) * Real.log (|t| + 2)) := by
  refine ⟨3502, by norm_num, ?_⟩
  intro t ht c hc
  rw [← Real.sqrt_eq_rpow]
  have hsum : ∑ m ∈ Finset.Icc 1 c, (m : ℂ) ^ (-((t : ℂ) * I)) =
      ∑ m ∈ Finset.Icc 1 c, phase (ph t m) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact cpow_eq_phase t m (by simp only [Finset.mem_Icc] at hm; omega)
  rw [hsum]
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht hc ⊢
    exact main_pos t ht c hc
  · rw [abs_of_neg h0] at ht hc ⊢
    have hconj : ∑ m ∈ Finset.Icc 1 c, phase (ph t m) =
        (starRingEnd ℂ) (∑ m ∈ Finset.Icc 1 c, phase (ph (-t) m)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [← phase_neg]
      congr 1
      unfold ph
      ring
    rw [hconj, Complex.norm_conj]
    exact main_pos (-t) ht c hc

end
end GuthMaynard.CitedLV.PartV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section
/-! ## Part V: van der Corput partial sums -/
alias partial_sum_cpow_le := GuthMaynard.CitedLV.PartV.partial_sum_cpow_le

end
end GuthMaynard.CitedLV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.PartB
open OAI.Problem337.ExponentialSum
noncomputable section
/-!
# Part B: sum versus integral on a block with slowly varying phase

* `partial_le`: Kusmin–Landau gives `|∑_{a ≤ n < d} n^{-it}| ≤ 8π a/|t|` for `10|t| ≤ a`, `d ≤ 2a`.
* `unweighted`: `|∑_{a ≤ n < d} n^{-it} - ∫_a^d x^{-it} dx| ≤ 16π`, via
  `∑ - ∫ = ∫_0^1 ∑_n (z(n) - z(n+u)) du` and Abel summation against `1 - ((n+u)/n)^{-it}`.
* `weighted`: for a real weight `h` with `|h| ≤ 1` and `|h(y) - h(x)| ≤ 2/a` for `|y - x| ≤ 1`,
  Abel summation against the unweighted errors gives `≤ 48π + 2`.
-/
/-- `x^{-it}` written through the real logarithm. -/
def zt (t x : ℝ) : ℂ := Complex.exp (((-(t * Real.log x) : ℝ) : ℂ) * I)

lemma norm_zt (t x : ℝ) : ‖zt t x‖ = 1 := by
  unfold zt
  exact Complex.norm_exp_ofReal_mul_I _

lemma cpow_eq_zt (t x : ℝ) (hx : 0 < x) : (x : ℂ) ^ (-((t : ℂ) * I)) = zt t x := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  unfold zt
  congr 1
  push_cast
  ring

lemma zt_eq_phase (t : ℝ) (n : ℕ) : zt t n = phase (-(t / (2 * Real.pi)) * Real.log n) := by
  unfold zt phase
  congr 2
  have := Real.pi_pos
  field_simp

lemma continuousOn_zt (t a b : ℝ) (ha : 0 < a) : ContinuousOn (zt t) (Set.Icc a b) := by
  unfold zt
  apply Continuous.comp_continuousOn (g := fun r : ℝ => Complex.exp ((r : ℂ) * I)) (by fun_prop)
  apply ContinuousOn.neg
  apply ContinuousOn.mul continuousOn_const
  exact Real.continuousOn_log.mono (fun x hx => by
    rw [Set.mem_compl_singleton_iff]; exact ne_of_gt (lt_of_lt_of_le ha hx.1))

lemma norm_exp_sub_le (θ φ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * I) - Complex.exp ((φ : ℂ) * I)‖ ≤ |θ - φ| := by
  have e : Complex.exp ((θ : ℂ) * I) - Complex.exp ((φ : ℂ) * I) =
      Complex.exp ((φ : ℂ) * I) * (Complex.exp (I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    rw [show (φ : ℂ) * I + I * ((θ - φ : ℝ) : ℂ) = (θ : ℂ) * I by push_cast; ring]
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq (Real.norm_eq_abs _))

/-! ## Abel summation -/
lemma abel_id (z g : ℕ → ℂ) (a c : ℕ) (hac : a ≤ c) :
    ∑ n ∈ Ico a c, z n * g n = (∑ n ∈ Ico a c, z n) * g c -
      ∑ n ∈ Ico a c, (∑ m ∈ Ico a (n + 1), z m) * (g (n + 1) - g n) := by
  induction c, hac using Nat.le_induction with
  | base => simp
  | succ c hac ih =>
    rw [sum_Ico_succ_top hac, ih]
    simp only [sum_Ico_succ_top hac]
    ring

lemma abel_le (z g : ℕ → ℂ) (a c : ℕ) (hac : a ≤ c) (P : ℝ)
    (hP : ∀ d, a ≤ d → d ≤ c → ‖∑ n ∈ Ico a d, z n‖ ≤ P) :
    ‖∑ n ∈ Ico a c, z n * g n‖ ≤ P * (‖g c‖ + ∑ n ∈ Ico a c, ‖g (n + 1) - g n‖) := by
  rw [abel_id z g a c hac]
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP a le_rfl hac)
  calc _ ≤ ‖(∑ n ∈ Ico a c, z n) * g c‖ +
        ‖∑ n ∈ Ico a c, (∑ m ∈ Ico a (n + 1), z m) * (g (n + 1) - g n)‖ := norm_sub_le _ _
    _ ≤ P * ‖g c‖ + ∑ n ∈ Ico a c, P * ‖g (n + 1) - g n‖ := by
        gcongr
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hP c hac le_rfl) (norm_nonneg _)
        · refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
          rw [norm_mul]
          have := mem_Ico.mp hn
          exact mul_le_mul_of_nonneg_right (hP (n + 1) (by omega) (by omega)) (norm_nonneg _)
    _ = _ := by rw [mul_add, mul_sum]

/-! ## Kusmin–Landau partial sums -/
lemma logD (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x ∧ Real.log (x + 1) - Real.log x ≤ 1 / x := by
  rw [← Real.log_div (by positivity) hx.ne']
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (show 0 < (x + 1) / x by positivity)
    have e : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
    linarith
  · have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith

lemma partial_le_pos (t : ℝ) (ht : 1 ≤ t) (a d : ℕ) (ha : 10 * t ≤ a) (hd : d ≤ 2 * a) :
    ‖∑ n ∈ Ico a d, zt t n‖ ≤ 8 * Real.pi * a / t := by
  have hpi := Real.pi_gt_three
  have hapos : (0 : ℝ) < a := by linarith
  have ha1 : 1 ≤ a := by exact_mod_cast (show (1 : ℝ) ≤ a by linarith)
  rcases Nat.lt_or_ge a d with had | had
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.sum_congr rfl (fun n _ => zt_eq_phase t n)]
    set c : ℝ := t / (2 * Real.pi) with hc
    have hc0 : 0 < c := by positivity
    have hcle : c ≤ t := div_le_self (by linarith) (by linarith)
    set D : ℕ → ℝ := fun i => Real.log ((i : ℝ) + 1) - Real.log i with hD
    have hinc : ∀ i : ℕ, (-(t / (2 * Real.pi)) * Real.log ((i + 1 : ℕ) : ℝ)) -
        (-(t / (2 * Real.pi)) * Real.log (i : ℝ)) = -(c * D i) := by
      intro i; simp only [hD, hc]; push_cast; ring
    have hDb : ∀ i : ℕ, a ≤ i → i ≤ e → 1 / (2 * (a : ℝ)) ≤ D i ∧ D i ≤ 1 / a := by
      intro i hi1 hi2
      have hi : (a : ℝ) ≤ i := by exact_mod_cast hi1
      have hi' : (i : ℝ) + 1 ≤ 2 * a := by exact_mod_cast (show i + 1 ≤ 2 * a by omega)
      obtain ⟨l, u⟩ := logD (i : ℝ) (by linarith)
      constructor
      · refine le_trans ?_ l
        exact one_div_le_one_div_of_le (by linarith) hi'
      · refine u.trans ?_
        exact one_div_le_one_div_of_le hapos hi
    have hca : c / a ≤ 1 / 10 := by
      rw [div_le_iff₀ hapos]; linarith
    have key := first_derivative_sum_bound_Icc (fun i => -(t / (2 * Real.pi)) * Real.log i) a e
      (c / (2 * a)) (-1) (by positivity)
      (by
        intro i hi1 hi2
        rw [hinc]
        have := (hDb i hi1 hi2).2
        have h2 : c * D i ≤ c * (1 / a) := mul_le_mul_of_nonneg_left this hc0.le
        have h3 : c * (1 / a) = c / a := by ring
        have h4 : c / (2 * a) = (c / a) / 2 := by field_simp
        push_cast
        linarith)
      (by
        intro i hi1 hi2
        rw [hinc]
        have := (hDb i hi1 hi2).1
        have h2 : c * (1 / (2 * a)) ≤ c * D i := mul_le_mul_of_nonneg_left this hc0.le
        have h3 : c * (1 / (2 * a)) = c / (2 * a) := by ring
        push_cast
        linarith)
      (by
        left
        intro i hi j hj hij
        simp only
        rw [hinc, hinc]
        have hDij : D j ≤ D i := by
          rcases Nat.eq_or_lt_of_le hij with h | h
          · rw [h]
          · have hi0 : (0 : ℝ) < i := by
              have : (a : ℝ) ≤ i := by exact_mod_cast hi.1
              linarith
            have hj1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
            have u := (logD (j : ℝ) (by linarith)).2
            have l := (logD (i : ℝ) hi0).1
            have : 1 / (j : ℝ) ≤ 1 / ((i : ℝ) + 1) := one_div_le_one_div_of_le (by linarith) hj1
            simp only [hD]
            linarith
        have := mul_le_mul_of_nonneg_left hDij hc0.le
        linarith)
    refine key.trans (le_of_eq ?_)
    rw [hc]
    field_simp
    ring
  · rw [Finset.Ico_eq_empty_of_le had]
    simp only [sum_empty, norm_zero]
    positivity

lemma zt_neg (t x : ℝ) : zt t x = (starRingEnd ℂ) (zt (-t) x) := by
  unfold zt
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma partial_le (t : ℝ) (ht : 1 ≤ |t|) (a d : ℕ) (ha : 10 * |t| ≤ a) (hd : d ≤ 2 * a) :
    ‖∑ n ∈ Ico a d, zt t n‖ ≤ 8 * Real.pi * a / |t| := by
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht ha ⊢
    exact partial_le_pos t ht a d ha hd
  · rw [abs_of_neg h0] at ht ha ⊢
    rw [show ∑ n ∈ Ico a d, zt t n = ∑ n ∈ Ico a d, (starRingEnd ℂ) (zt (-t) n) from
      Finset.sum_congr rfl (fun n _ => zt_neg t n), ← map_sum, Complex.norm_conj]
    exact partial_le_pos (-t) ht a d ha hd

/-! ## Splitting an integral into unit pieces -/
lemma integral_split (f : ℝ → ℂ) (a D : ℕ) (hf : ContinuousOn f (Set.Icc (a : ℝ) D)) :
    ∀ d, a ≤ d → d ≤ D →
      ∫ x in (a : ℝ)..d, f x = ∑ n ∈ Ico a d, ∫ u in (0 : ℝ)..1, f (n + u) := by
  intro d had
  induction d, had using Nat.le_induction with
  | base => intro _; simp
  | succ d hd ih =>
    intro hdD
    have hD : (d : ℝ) + 1 ≤ D := by exact_mod_cast hdD
    have hda : (a : ℝ) ≤ d := by exact_mod_cast hd
    rw [sum_Ico_succ_top hd, ← ih (by omega), intervalIntegral.integral_comp_add_left f (d : ℝ)]
    simp only [add_zero]
    push_cast
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · apply ContinuousOn.intervalIntegrable
      refine hf.mono ?_
      rw [Set.uIcc_of_le hda]
      exact Set.Icc_subset_Icc le_rfl (by linarith)
    · apply ContinuousOn.intervalIntegrable
      refine hf.mono ?_
      rw [Set.uIcc_of_le (by linarith)]
      exact Set.Icc_subset_Icc hda hD

/-! ## The unweighted estimate -/
lemma Lfacts (u x : ℝ) (hu0 : 0 ≤ u) (hx : 1 ≤ x) :
    0 ≤ Real.log (x + u) - Real.log x ∧ Real.log (x + u) - Real.log x ≤ u / x ∧
    Real.log (x + 1 + u) - Real.log (x + 1) ≤ Real.log (x + u) - Real.log x := by
  have hx0 : 0 < x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := Real.log_le_log hx0 (show x ≤ x + u by linarith); linarith
  · rw [← Real.log_div (by linarith) hx0.ne']
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + u) / x by positivity)
    have e : (x + u) / x - 1 = u / x := by field_simp; ring
    linarith
  · rw [← Real.log_div (by linarith) (by linarith), ← Real.log_div (by linarith) hx0.ne']
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by linarith) hx0]
    nlinarith

lemma telescope (L : ℕ → ℝ) (a d : ℕ) (had : a ≤ d) :
    ∑ n ∈ Ico a d, (L n - L (n + 1)) = L a - L d := by
  induction d, had using Nat.le_induction with
  | base => simp
  | succ d hd ih => rw [sum_Ico_succ_top hd, ih]; ring

lemma unweighted_pt (t : ℝ) (ht : 1 ≤ |t|) (a d : ℕ) (ha : 10 * |t| ≤ a) (had : a ≤ d)
    (hd : d ≤ 2 * a) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖∑ n ∈ Ico a d, (zt t n - zt t (n + u))‖ ≤ 16 * Real.pi := by
  have ht0 : 0 < |t| := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  set L : ℕ → ℝ := fun n => Real.log ((n : ℝ) + u) - Real.log n with hL
  set g : ℕ → ℂ := fun n => 1 - Complex.exp (((-(t * L n)) : ℝ) * I) with hg
  have hsplit : ∀ n : ℕ, zt t n - zt t (n + u) = zt t n * g n := by
    intro n
    simp only [hg, hL, zt]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun n _ => hsplit n)]
  have hP : ∀ d', a ≤ d' → d' ≤ d → ‖∑ n ∈ Ico a d', zt t n‖ ≤ 8 * Real.pi * a / |t| :=
    fun d' _ hd' => partial_le t ht a d' ha (by omega)
  refine (abel_le _ g a d had _ hP).trans ?_
  have hLf : ∀ n : ℕ, a ≤ n → 0 ≤ L n ∧ L n ≤ 1 / a ∧ L (n + 1) ≤ L n := by
    intro n hn
    have hn' : (a : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨h1, h2, h3⟩ := Lfacts u n hu0 (by linarith)
    refine ⟨h1, h2.trans ?_, ?_⟩
    · calc u / n ≤ 1 / n := div_le_div_of_nonneg_right hu1 (by linarith)
        _ ≤ 1 / a := one_div_le_one_div_of_le hapos hn'
    · simp only [hL]; push_cast; exact h3
  have hgc : ‖g d‖ ≤ |t| / a := by
    have := norm_exp_sub_le 0 (-(t * L d))
    simp only [ofReal_zero, zero_mul, Complex.exp_zero] at this
    simp only [hg]
    refine this.trans ?_
    obtain ⟨h1, h2, _⟩ := hLf d had
    rw [zero_sub, neg_neg, abs_mul, abs_of_nonneg h1]
    calc |t| * L d ≤ |t| * (1 / a) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |t| / a := by ring
  have hgd : ∀ n ∈ Ico a d, ‖g (n + 1) - g n‖ ≤ |t| * (L n - L (n + 1)) := by
    intro n hn
    have hn := (mem_Ico.mp hn).1
    have e : g (n + 1) - g n = Complex.exp (((-(t * L n)) : ℝ) * I) -
        Complex.exp (((-(t * L (n + 1))) : ℝ) * I) := by
      simp only [hg]; ring
    rw [e]
    refine (norm_exp_sub_le _ _).trans (le_of_eq ?_)
    rw [show -(t * L n) - -(t * L (n + 1)) = t * (L (n + 1) - L n) by ring, abs_mul,
      abs_sub_comm, abs_of_nonneg (by linarith [(hLf n hn).2.2] : (0 : ℝ) ≤ L n - L (n + 1))]
  have hsum : ∑ n ∈ Ico a d, ‖g (n + 1) - g n‖ ≤ |t| / a := by
    refine (sum_le_sum hgd).trans ?_
    rw [← mul_sum, telescope L a d had]
    obtain ⟨h1, h2, _⟩ := hLf a le_rfl
    obtain ⟨h1', _, _⟩ := hLf d had
    calc |t| * (L a - L d) ≤ |t| * (1 / a) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |t| / a := by ring
  calc 8 * Real.pi * a / |t| * (‖g d‖ + ∑ n ∈ Ico a d, ‖g (n + 1) - g n‖)
      ≤ 8 * Real.pi * a / |t| * (|t| / a + |t| / a) := by gcongr
    _ = 16 * Real.pi := by field_simp; ring

lemma shift_integrable (f : ℝ → ℂ) (n : ℝ) (hf : ContinuousOn f (Set.Icc n (n + 1))) :
    IntervalIntegrable (fun u => f (n + u)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  refine hf.comp (continuousOn_const.add continuousOn_id) ?_
  intro u hu
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

lemma unweighted (t : ℝ) (ht : 1 ≤ |t|) (a d : ℕ) (ha : 10 * |t| ≤ a) (had : a ≤ d)
    (hd : d ≤ 2 * a) :
    ‖∑ n ∈ Ico a d, zt t n - ∫ x in (a : ℝ)..d, zt t x‖ ≤ 16 * Real.pi := by
  have hapos : (0 : ℝ) < a := by linarith
  rw [integral_split (zt t) a d (continuousOn_zt t a d hapos) d had le_rfl]
  have hint : ∀ n ∈ Ico a d,
      IntervalIntegrable (fun u => zt t (n + u)) MeasureTheory.volume 0 1 := by
    intro n hn
    have hn' : (a : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    exact shift_integrable _ _ (continuousOn_zt t n (n + 1) (by linarith))
  have e : ∑ n ∈ Ico a d, zt t n - ∑ n ∈ Ico a d, ∫ u in (0 : ℝ)..1, zt t (n + u) =
      ∫ u in (0 : ℝ)..1, ∑ n ∈ Ico a d, (zt t n - zt t (n + u)) := by
    rw [intervalIntegral.integral_finsetSum
      (fun n hn => intervalIntegrable_const.sub (hint n hn)), ← sum_sub_distrib]
    refine sum_congr rfl (fun n hn => ?_)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint n hn),
      intervalIntegral.integral_const]
    simp
  rw [e]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 16 * Real.pi) ?_).trans
    (by simp)
  intro u hu
  rw [Set.uIoc_of_le zero_le_one] at hu
  exact unweighted_pt t ht a d ha had hd u hu.1.le hu.2

/-! ## The weighted estimate -/
lemma weighted (t : ℝ) (ht : 1 ≤ |t|) (a b : ℕ) (ha : 10 * |t| ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * a) (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Icc (a : ℝ) b))
    (hbd : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → |h x| ≤ 1)
    (hlip : ∀ x y : ℝ, (a : ℝ) ≤ x → x ≤ y → y ≤ b → y ≤ x + 1 → |h y - h x| ≤ 2 / a) :
    ‖∑ n ∈ Ico a b, (h n : ℂ) * zt t n - ∫ x in (a : ℝ)..b, (h x : ℂ) * zt t x‖ ≤
      48 * Real.pi + 2 := by
  have hapos : (0 : ℝ) < a := by linarith
  have hcF : ContinuousOn (fun x => (h x : ℂ) * zt t x) (Set.Icc (a : ℝ) b) :=
    (continuous_ofReal.comp_continuousOn hcont).mul (continuousOn_zt t a b hapos)
  rw [integral_split _ a b hcF b hab le_rfl]
  have hsub : ∀ n ∈ Ico a b, Set.Icc (n : ℝ) (n + 1) ⊆ Set.Icc (a : ℝ) b := by
    intro n hn
    have h1 : (a : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have h2 : (n : ℝ) + 1 ≤ b := by exact_mod_cast (mem_Ico.mp hn).2
    exact Set.Icc_subset_Icc h1 h2
  have hintZ : ∀ n ∈ Ico a b,
      IntervalIntegrable (fun u => zt t (n + u)) MeasureTheory.volume 0 1 :=
    fun n hn => shift_integrable _ _ ((continuousOn_zt t a b hapos).mono (hsub n hn))
  have hintF : ∀ n ∈ Ico a b, IntervalIntegrable (fun u => (h (n + u) : ℂ) * zt t (n + u))
      MeasureTheory.volume 0 1 :=
    fun n hn => shift_integrable (fun x => (h x : ℂ) * zt t x) _ (hcF.mono (hsub n hn))
  set J : ℕ → ℂ := fun n => ∫ u in (0 : ℝ)..1, zt t (n + u) with hJ
  set K : ℕ → ℂ := fun n => ∫ u in (0 : ℝ)..1, ((h n : ℂ) - h (n + u)) * zt t (n + u) with hK
  have hpiece : ∀ n ∈ Ico a b,
      ∫ u in (0 : ℝ)..1, (h (n + u) : ℂ) * zt t (n + u) = (h n : ℂ) * J n - K n := by
    intro n hn
    have e : ∫ u in (0 : ℝ)..1, ((h n : ℂ) - h (n + u)) * zt t (n + u) =
        ∫ u in (0 : ℝ)..1, ((h n : ℂ) * zt t (n + u) - (h (n + u) : ℂ) * zt t (n + u)) := by
      congr 1; ext u; ring
    simp only [hJ, hK]
    rw [e, intervalIntegral.integral_sub ((hintZ n hn).const_mul _) (hintF n hn),
      intervalIntegral.integral_const_mul]
    ring
  rw [sum_congr rfl hpiece]
  have e2 : ∑ n ∈ Ico a b, (h n : ℂ) * zt t n - ∑ n ∈ Ico a b, ((h n : ℂ) * J n - K n) =
      ∑ n ∈ Ico a b, (zt t n - J n) * (h n : ℂ) + ∑ n ∈ Ico a b, K n := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun n _ => ?_)
    ring
  rw [e2]
  have hcard : ((Ico a b).card : ℝ) * (2 / a) ≤ 2 := by
    have hbR : (b : ℝ) ≤ 2 * a := by exact_mod_cast hb
    rw [Nat.card_Ico, Nat.cast_sub hab, mul_div_assoc', div_le_iff₀ hapos]
    linarith
  have hA : ‖∑ n ∈ Ico a b, (zt t n - J n) * (h n : ℂ)‖ ≤ 16 * Real.pi * 3 := by
    have hP : ∀ d, a ≤ d → d ≤ b → ‖∑ n ∈ Ico a d, (zt t n - J n)‖ ≤ 16 * Real.pi := by
      intro d had hdb
      rw [sum_sub_distrib]
      simp only [hJ]
      rw [← integral_split (zt t) a d (continuousOn_zt t a d hapos) d had le_rfl]
      exact unweighted t ht a d ha had (by omega)
    refine (abel_le _ (fun n => (h n : ℂ)) a b hab _ hP).trans ?_
    have hb1 : ‖((h b : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hbd b (by exact_mod_cast hab) le_rfl
    have hvar : ∑ n ∈ Ico a b, ‖((h ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) - ((h n : ℝ) : ℂ)‖ ≤ 2 := by
      refine (sum_le_card_nsmul _ _ (2 / (a : ℝ)) ?_).trans ((nsmul_eq_mul _ _).trans_le hcard)
      intro n hn
      have h1 : (a : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      have h2 : (n : ℝ) + 1 ≤ b := by exact_mod_cast (mem_Ico.mp hn).2
      rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      push_cast
      exact hlip n (n + 1) h1 (by linarith) h2 le_rfl
    have hpi := Real.pi_pos
    calc 16 * Real.pi * (‖((h b : ℝ) : ℂ)‖ +
          ∑ n ∈ Ico a b, ‖((h ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) - ((h n : ℝ) : ℂ)‖)
        ≤ 16 * Real.pi * (1 + 2) := by gcongr
      _ = 16 * Real.pi * 3 := by ring
  have hB : ‖∑ n ∈ Ico a b, K n‖ ≤ 2 := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_card_nsmul _ _ (2 / (a : ℝ)) ?_).trans ((nsmul_eq_mul _ _).trans_le hcard)
    intro n hn
    have h1 : (a : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    have h2 : (n : ℝ) + 1 ≤ b := by exact_mod_cast (mem_Ico.mp hn).2
    simp only [hK]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 / a) ?_).trans
      (by simp)
    intro u hu
    rw [Set.uIoc_of_le zero_le_one] at hu
    rw [norm_mul, norm_zt, mul_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_sub_comm]
    exact hlip n (n + u) h1 (by linarith [hu.1]) (by linarith [hu.2]) (by linarith [hu.2])
  calc _ ≤ ‖∑ n ∈ Ico a b, (zt t n - J n) * (h n : ℂ)‖ + ‖∑ n ∈ Ico a b, K n‖ := norm_add_le _ _
    _ ≤ 16 * Real.pi * 3 + 2 := add_le_add hA hB
    _ = 48 * Real.pi + 2 := by ring

/-! ## The concrete weight -/
lemma rpow_diff_le (σ x y : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hx : 1 ≤ x) (hxy : x ≤ y) :
    x ^ (-σ) - y ^ (-σ) ≤ (y - x) / y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hyx : 1 ≤ y / x := by rw [le_div_iff₀ hx0]; linarith
  have e : y ^ (-σ) = x ^ (-σ) * (y / x) ^ (-σ) := by
    rw [← Real.mul_rpow hx0.le (by positivity)]
    congr 1
    field_simp
  have h1 : x / y ≤ (y / x) ^ (-σ) := by
    have := Real.rpow_le_rpow_of_exponent_le hyx (show (-1 : ℝ) ≤ -σ by linarith)
    rwa [Real.rpow_neg_one, inv_div] at this
  have h2 : x ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have h3 : 0 ≤ x ^ (-σ) := Real.rpow_nonneg hx0.le _
  have h4 : 0 ≤ 1 - x / y := by
    rw [sub_nonneg, div_le_one hy0]; exact hxy
  have h5 : (y - x) / y = 1 - x / y := by field_simp
  rw [e, h5]
  calc x ^ (-σ) - x ^ (-σ) * (y / x) ^ (-σ) = x ^ (-σ) * (1 - (y / x) ^ (-σ)) := by ring
    _ ≤ x ^ (-σ) * (1 - x / y) := mul_le_mul_of_nonneg_left (by linarith) h3
    _ ≤ 1 * (1 - x / y) := mul_le_mul_of_nonneg_right h2 h4
    _ = 1 - x / y := one_mul _

theorem block_sum_sub_integral_le : ∃ C : ℝ, 0 < C ∧ ∀ (t σ α β : ℝ) (a b : ℕ),
    1 ≤ |t| → 0 ≤ σ → σ ≤ 1 / 2 → 10 * |t| ≤ a → a ≤ b → (b : ℝ) ≤ 2 * a →
    (∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → |α + β * x| ≤ 1) → |β| ≤ 1 / a →
    ‖∑ n ∈ Finset.Ico a b, ((α + β * n : ℝ) : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + t * I)) -
      ∫ x in (a : ℝ)..b, ((α + β * x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤ C := by
  refine ⟨48 * Real.pi + 2, by positivity, ?_⟩
  intro t σ α β a b ht hσ0 hσ1 ha hab hb hw hβ
  have hapos : (0 : ℝ) < a := by linarith
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hb' : b ≤ 2 * a := by exact_mod_cast hb
  set h : ℝ → ℝ := fun x => (α + β * x) * x ^ (-σ) with hh
  have conv : ∀ x : ℝ, 0 < x → ((α + β * x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ : ℂ) + t * I)) =
      (h x : ℂ) * zt t x := by
    intro x hx
    rw [neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_eq_zt t x hx,
      show -(σ : ℂ) = ((-σ : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le]
    simp only [hh]
    push_cast
    ring
  have hsum : ∑ n ∈ Finset.Ico a b, ((α + β * n : ℝ) : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + t * I)) =
      ∑ n ∈ Ico a b, (h n : ℂ) * zt t n := by
    refine sum_congr rfl (fun n hn => ?_)
    have hn : (a : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
    rw [← Complex.ofReal_natCast]
    exact conv n (by linarith)
  have hint : ∫ x in (a : ℝ)..b, ((α + β * x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ : ℂ) + t * I)) =
      ∫ x in (a : ℝ)..b, (h x : ℂ) * zt t x := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le habR] at hx
    exact conv x (by linarith [hx.1])
  rw [hsum, hint]
  have hpow : ∀ x : ℝ, (a : ℝ) ≤ x → 0 ≤ x ^ (-σ) ∧ x ^ (-σ) ≤ 1 := fun x hx =>
    ⟨Real.rpow_nonneg (by linarith) _, Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      (by linarith)⟩
  apply weighted t ht a b ha hab hb' h
  · apply ContinuousOn.mul (by fun_prop)
    exact ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl
      (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)))
  · intro x hx1 hx2
    obtain ⟨p0, p1⟩ := hpow x hx1
    simp only [hh]
    rw [abs_mul, abs_of_nonneg p0]
    calc |α + β * x| * x ^ (-σ) ≤ 1 * 1 :=
          mul_le_mul (hw x hx1 hx2) p1 p0 zero_le_one
      _ = 1 := one_mul 1
  · intro x y hx hxy hy hy1
    obtain ⟨p0, p1⟩ := hpow y (by linarith)
    obtain ⟨q0, q1⟩ := hpow x hx
    have hd := rpow_diff_le σ x y hσ0 (by linarith) (by linarith) hxy
    have hmono : y ^ (-σ) ≤ x ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
    have hyx : (y - x) / y ≤ 1 / a := by
      rw [div_le_div_iff₀ (by linarith) hapos]; nlinarith
    have e : h y - h x = (β * (y - x)) * y ^ (-σ) + (α + β * x) * (y ^ (-σ) - x ^ (-σ)) := by
      simp only [hh]; ring
    rw [e]
    have t1 : |(β * (y - x)) * y ^ (-σ)| ≤ 1 / a := by
      rw [abs_mul, abs_mul, abs_of_nonneg p0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
      calc |β| * (y - x) * y ^ (-σ) ≤ (1 / a) * 1 * 1 := by
            apply mul_le_mul (mul_le_mul hβ (by linarith) (by linarith) (by positivity)) p1 p0
              (by positivity)
        _ = 1 / a := by ring
    have t2 : |(α + β * x) * (y ^ (-σ) - x ^ (-σ))| ≤ 1 / a := by
      rw [abs_mul, abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x ^ (-σ) - y ^ (-σ))]
      calc |α + β * x| * (x ^ (-σ) - y ^ (-σ)) ≤ 1 * (1 / a) :=
            mul_le_mul (hw x hx (by linarith)) (hd.trans hyx) (by linarith) zero_le_one
        _ = 1 / a := one_mul _
    calc _ ≤ |(β * (y - x)) * y ^ (-σ)| + |(α + β * x) * (y ^ (-σ) - x ^ (-σ))| :=
          abs_add_le _ _
      _ ≤ 1 / a + 1 / a := add_le_add t1 t2
      _ = 2 / a := by ring

end
end GuthMaynard.CitedLV.PartB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section
/-! ## Part B: sum versus integral on a block with slowly varying phase -/
alias block_sum_sub_integral_le := GuthMaynard.CitedLV.PartB.block_sum_sub_integral_le

end
end GuthMaynard.CitedLV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.PartK
noncomputable section
open GuthMaynard.CitedLV
/-!
# Part K: the kernel bound

`K(s) = ∑_{1 ≤ m ≤ 2N} w(m) m^{-s} ≪ N/t² + |t|^{1/2} log(|t|+2) + log(N+2)`.

Split at `X = ⌈10|t|⌉`:
* small `m < X`: Abel summation (`abel_bound`) with the nonincreasing weights `w(m) m^{-σ} ∈ [0,1]`
  and the van der Corput bound `partial_sum_cpow_le`;
* large `m ≥ X`: dyadic blocks (`dyadic`, `top_block`) via `block_sum_sub_integral_le`, and the
  explicit integral of the tent weight times `x^{-s}` (`integral_affine`, `int_bound1`, `int_bound2`).
-/
/-! ### The tent weight -/
lemma tentW_nonneg (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : 0 ≤ tentW N x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold tentW
  split_ifs with h1 h2
  · norm_num
  · rw [sub_nonneg, div_le_iff₀ hN']; linarith
  · exact le_refl _

lemma tentW_le_one (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : tentW N x ≤ 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold tentW
  split_ifs with h1 h2
  · exact le_refl _
  · have : 1 ≤ x / N := by rw [le_div_iff₀ hN']; linarith
    linarith
  · norm_num

lemma tentW_anti (N : ℕ) (hN : 1 ≤ N) {x y : ℝ} (hxy : x ≤ y) : tentW N y ≤ tentW N x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : x / N ≤ y / N := div_le_div_of_nonneg_right hxy hN'.le
  have a1 : (N : ℝ) < y → 1 ≤ y / N := fun h => by rw [le_div_iff₀ hN']; linarith
  have a2 : x ≤ 2 * N → x / N ≤ 2 := fun h => by rw [div_le_iff₀ hN']; linarith
  unfold tentW
  split_ifs <;> first
    | linarith
    | linarith [a1 (by linarith)]
    | linarith [a2 (by linarith)]

lemma tentW_eq_one (N : ℕ) {x : ℝ} (hx : x ≤ N) : tentW N x = 1 := by
  unfold tentW; rw [if_pos hx]

lemma tentW_eq_affine (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (h1 : (N : ℝ) ≤ x) (h2 : x ≤ 2 * N) :
    tentW N x = 2 + (-1 / N) * x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold tentW
  split_ifs with h3
  · have : x = N := le_antisymm h3 h1
    subst this; field_simp; ring
  · ring

/-! ### Splitting `m^{-s}` -/
lemma cpow_split (s : ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (m : ℂ) ^ (-s) = (((m : ℝ) ^ (-s.re) : ℝ) : ℂ) * (m : ℂ) ^ (-((s.im : ℂ) * I)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have h : -s = ((-s.re : ℝ) : ℂ) + (-((s.im : ℂ) * I)) := by
    apply Complex.ext <;> simp
  rw [h, cpow_add _ _ hm0, ofReal_cpow (by positivity), ofReal_natCast]

/-! ### Abel summation -/
lemma abel_identity (g : ℕ → ℝ) (e S : ℕ → ℂ) (hS : ∀ k, e k = S (k + 1) - S k) (h0 : S 0 = 0)
    (n : ℕ) :
    ∑ k ∈ range n, (g k : ℂ) * e k =
      (g n : ℂ) * S n + ∑ k ∈ range n, ((g k - g (k + 1) : ℝ) : ℂ) * S (k + 1) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih, hS n]
    push_cast; ring

lemma abel_bound (g : ℕ → ℝ) (e : ℕ → ℂ) (n : ℕ) (B : ℝ)
    (hg : ∀ k < n, g (k + 1) ≤ g k) (hgn : 0 ≤ g n)
    (hS : ∀ j ≤ n, ‖∑ k ∈ range j, e k‖ ≤ B) :
    ‖∑ k ∈ range n, (g k : ℂ) * e k‖ ≤ g 0 * B := by
  have hSe : ∀ k, e k = (fun j => ∑ i ∈ range j, e i) (k + 1) - (fun j => ∑ i ∈ range j, e i) k := by
    intro k; simp [sum_range_succ]
  rw [abel_identity g e (fun j => ∑ i ∈ range j, e i) hSe (by simp) n]
  calc _ ≤ ‖(g n : ℂ) * ∑ i ∈ range n, e i‖ +
        ‖∑ k ∈ range n, ((g k - g (k + 1) : ℝ) : ℂ) * ∑ i ∈ range (k + 1), e i‖ := norm_add_le _ _
    _ ≤ g n * B + ∑ k ∈ range n, (g k - g (k + 1)) * B := by
        gcongr ?_ + ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hgn]
          exact mul_le_mul_of_nonneg_left (hS n le_rfl) hgn
        · refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
          have hk' := mem_range.1 hk
          have h0 : 0 ≤ g k - g (k + 1) := sub_nonneg.2 (hg k hk')
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
          exact mul_le_mul_of_nonneg_left (hS (k + 1) hk') h0
    _ = g 0 * B := by rw [← sum_mul, sum_range_sub']; ring

lemma small_part (CV : ℝ) (hV : ∀ t : ℝ, 1 ≤ |t| → ∀ c : ℕ, (c : ℝ) ≤ 11 * |t| + 2 →
      ‖∑ m ∈ Finset.Icc 1 c, (m : ℂ) ^ (-((t : ℂ) * I))‖ ≤
        CV * (|t| ^ (1 / 2 : ℝ) * Real.log (|t| + 2)))
    (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (h0 : 0 ≤ s.re) (ht : 1 ≤ |s.im|) (M : ℕ)
    (hM : (M : ℝ) ≤ 10 * |s.im| + 2) :
    ‖∑ m ∈ Ico 1 M, ((tentW N m : ℝ) : ℂ) * (m : ℂ) ^ (-s)‖ ≤
      CV * (|s.im| ^ (1 / 2 : ℝ) * Real.log (|s.im| + 2)) := by
  rw [sum_Ico_eq_sum_range]
  have hfe : ∀ k : ℕ, ((tentW N ((1 + k : ℕ) : ℝ) : ℝ) : ℂ) * ((1 + k : ℕ) : ℂ) ^ (-s) =
      ((tentW N ((1 + k : ℕ) : ℝ) * ((1 + k : ℕ) : ℝ) ^ (-s.re) : ℝ) : ℂ) *
        ((1 + k : ℕ) : ℂ) ^ (-((s.im : ℂ) * I)) := by
    intro k; rw [cpow_split s (1 + k) (by omega)]; push_cast; ring
  rw [sum_congr rfl (fun k _ => hfe k)]
  set B := CV * (|s.im| ^ (1 / 2 : ℝ) * Real.log (|s.im| + 2))
  have hS : ∀ j ≤ M - 1, ‖∑ k ∈ range j, ((1 + k : ℕ) : ℂ) ^ (-((s.im : ℂ) * I))‖ ≤ B := by
    intro j hj
    have : ∑ k ∈ range j, ((1 + k : ℕ) : ℂ) ^ (-((s.im : ℂ) * I)) =
        ∑ m ∈ Icc 1 j, (m : ℂ) ^ (-((s.im : ℂ) * I)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]; simp
    rw [this]
    apply hV s.im ht j
    have : (j : ℝ) ≤ M := by exact_mod_cast (show j ≤ M by omega)
    linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hS 0 (Nat.zero_le _))
  refine (abel_bound _ _ (M - 1) B ?_ ?_ hS).trans ?_
  · intro k _
    have c1 : ((1 + k : ℕ) : ℝ) ≤ ((1 + (k + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have c0 : (0 : ℝ) < ((1 + k : ℕ) : ℝ) := by exact_mod_cast (by omega)
    exact mul_le_mul (tentW_anti N hN c1)
      (Real.rpow_le_rpow_of_nonpos c0 c1 (neg_nonpos.2 h0)) (by positivity) (tentW_nonneg N hN _)
  · exact mul_nonneg (tentW_nonneg N hN _) (by positivity)
  · have : tentW N ((1 + 0 : ℕ) : ℝ) * ((1 + 0 : ℕ) : ℝ) ^ (-s.re) ≤ 1 := by
      simp only [Nat.add_zero, Nat.cast_one, Real.one_rpow, mul_one]
      exact tentW_le_one N hN _
    nlinarith

/-! ### Continuity, integrals -/
lemma cont_cpow (s : ℂ) {x : ℝ} (hx : 0 < x) : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-s)) x :=
  (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hx)).comp continuous_ofReal.continuousAt

lemma pos_of_mem_uIcc {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : x ∈ Set.uIcc a b) : 0 < x := by
  rcases Set.mem_uIcc.1 hx with h | h <;> linarith [h.1]

lemma intInt (s : ℂ) (α β : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => ((α + β * x : ℝ) : ℂ) * (x : ℂ) ^ (-s))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  apply ContinuousAt.continuousWithinAt
  exact (continuous_ofReal.comp (continuous_const.add
    (continuous_const.mul continuous_id))).continuousAt.mul (cont_cpow s (pos_of_mem_uIcc ha hb hx))

lemma intInt0 (s : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  exact (cont_cpow s (pos_of_mem_uIcc ha hb hx)).continuousWithinAt

/-- Antiderivative of `(α + β x) x^{-s}`. -/
def G (s : ℂ) (α β : ℝ) (x : ℝ) : ℂ :=
  (α : ℂ) * (x : ℂ) ^ (-s + 1) / (-s + 1) + (β : ℂ) * (x : ℂ) ^ (-s + 1 + 1) / (-s + 1 + 1)

lemma cpow_succ_real {x : ℝ} (hx : 0 < x) (u : ℂ) : (x : ℂ) ^ (u + 1) = x * (x : ℂ) ^ u := by
  rw [cpow_add _ _ (ofReal_ne_zero.2 hx.ne'), cpow_one, mul_comm]

lemma integral_affine (s : ℂ) (hs1 : -s + 1 ≠ 0) (hs2 : -s + 1 + 1 ≠ 0) (α β : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, ((α + β * x : ℝ) : ℂ) * (x : ℂ) ^ (-s) = G s α β b - G s α β a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (intInt s α β ha hb)
  intro x hx
  have hx0 : 0 < x := pos_of_mem_uIcc ha hb hx
  have h1 := hasDerivAt_ofReal_cpow_const' (x := x) hx0.ne' (r := -s)
    (fun h => hs1 (by rw [h]; ring))
  have h2 := hasDerivAt_ofReal_cpow_const' (x := x) hx0.ne' (r := -s + 1)
    (fun h => hs2 (by rw [h]; ring))
  have h3 := (h1.const_mul (α : ℂ)).add (h2.const_mul (β : ℂ))
  convert h3 using 1
  · funext y; simp only [G, Pi.add_apply]; ring
  · rw [cpow_succ_real hx0]; push_cast; ring

/-! ### Blocks -/
/-- The statement of `block_sum_sub_integral_le` for a given constant. -/
def BlockProp (C : ℝ) : Prop := ∀ (t σ α β : ℝ) (a b : ℕ),
    1 ≤ |t| → 0 ≤ σ → σ ≤ 1 / 2 → 10 * |t| ≤ a → a ≤ b → (b : ℝ) ≤ 2 * a →
    (∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → |α + β * x| ≤ 1) → |β| ≤ 1 / a →
    ‖∑ n ∈ Finset.Ico a b, ((α + β * n : ℝ) : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + t * I)) -
      ∫ x in (a : ℝ)..b, ((α + β * x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ : ℂ) + t * I))‖ ≤ C

lemma block_s (CB : ℝ) (hB : BlockProp CB) (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2)
    (ht : 1 ≤ |s.im|) (α β : ℝ) (a b : ℕ) (ha : 10 * |s.im| ≤ a) (hab : a ≤ b)
    (hb : (b : ℝ) ≤ 2 * a) (hw : ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → |α + β * x| ≤ 1)
    (hβ : |β| ≤ 1 / a) :
    ‖∑ n ∈ Ico a b, ((α + β * n : ℝ) : ℂ) * (n : ℂ) ^ (-s) -
      ∫ x in (a : ℝ)..b, ((α + β * x : ℝ) : ℂ) * (x : ℂ) ^ (-s)‖ ≤ CB := by
  have := hB s.im s.re α β a b ht h0 h1 ha hab hb hw hβ
  rwa [Complex.re_add_im] at this

lemma dyadic (CB : ℝ) (hCB : 0 < CB) (hB : BlockProp CB) (s : ℂ) (h0 : 0 ≤ s.re)
    (h1 : s.re ≤ 1 / 2) (ht : 1 ≤ |s.im|) :
    ∀ k : ℕ, ∀ a b : ℕ, 10 * |s.im| ≤ a → a ≤ b → b ≤ 2 ^ k * a →
    ‖∑ n ∈ Ico a b, (n : ℂ) ^ (-s) - ∫ x in (a : ℝ)..b, (x : ℂ) ^ (-s)‖ ≤ CB * k := by
  intro k
  induction k with
  | zero =>
    intro a b _ hab hb
    have : b = a := by simp at hb; omega
    subst this; simp
  | succ k ih =>
    intro a b ha hab hb
    have ha0 : (0 : ℝ) < a := by linarith
    by_cases h2 : b ≤ 2 * a
    · have := block_s CB hB s h0 h1 ht 1 0 a b ha hab (by exact_mod_cast h2)
        (fun x _ _ => by simp) (by rw [abs_zero]; positivity)
      simp only [zero_mul, add_zero, ofReal_one, one_mul] at this
      push_cast; nlinarith
    · push Not at h2
      have h2a : (0 : ℝ) < ((2 * a : ℕ) : ℝ) := by push_cast; linarith
      have hb0 : (0 : ℝ) < (b : ℝ) := by
        have : (2 * a : ℕ) ≤ b := h2.le
        have : ((2 * a : ℕ) : ℝ) ≤ b := by exact_mod_cast this
        linarith
      rw [← sum_Ico_consecutive _ (show a ≤ 2 * a by omega) h2.le,
        ← intervalIntegral.integral_add_adjacent_intervals (intInt0 s ha0 h2a) (intInt0 s h2a hb0)]
      have hA := block_s CB hB s h0 h1 ht 1 0 a (2 * a) ha (by omega) (by push_cast; exact le_rfl)
        (fun x _ _ => by simp) (by rw [abs_zero]; positivity)
      simp only [zero_mul, add_zero, ofReal_one, one_mul] at hA
      have hC := ih (2 * a) b (by push_cast; linarith [abs_nonneg s.im]) h2.le
        (by calc b ≤ 2 ^ (k + 1) * a := hb
                _ = 2 ^ k * (2 * a) := by ring)
      set S1 := ∑ n ∈ Ico a (2 * a), (n : ℂ) ^ (-s)
      set S2 := ∑ n ∈ Ico (2 * a) b, (n : ℂ) ^ (-s)
      set I1 := ∫ x in (a : ℝ)..((2 * a : ℕ) : ℝ), (x : ℂ) ^ (-s)
      set I2 := ∫ x in ((2 * a : ℕ) : ℝ)..b, (x : ℂ) ^ (-s)
      have : S1 + S2 - (I1 + I2) = (S1 - I1) + (S2 - I2) := by ring
      rw [this]
      calc _ ≤ ‖S1 - I1‖ + ‖S2 - I2‖ := norm_add_le _ _
        _ ≤ CB + CB * k := add_le_add hA hC
        _ = CB * ((k + 1 : ℕ) : ℝ) := by push_cast; ring

lemma top_block (CB : ℝ) (hB : BlockProp CB) (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2)
    (ht : 1 ≤ |s.im|) (N : ℕ) (hN : 1 ≤ N) (a : ℕ) (ha : 10 * |s.im| ≤ a) (hNa : N ≤ a)
    (ha2 : a ≤ 2 * N) :
    ‖∑ n ∈ Ico a (2 * N), ((2 + (-1 / N) * n : ℝ) : ℂ) * (n : ℂ) ^ (-s) -
      ∫ x in (a : ℝ)..((2 * N : ℕ) : ℝ), ((2 + (-1 / N) * x : ℝ) : ℂ) * (x : ℂ) ^ (-s)‖ ≤
      2 * CB := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : (0 : ℝ) < a := by linarith
  have hNa' : (N : ℝ) ≤ a := by exact_mod_cast hNa
  have ha2' : (a : ℝ) ≤ 2 * N := by exact_mod_cast ha2
  have hB1 := block_s CB hB s h0 h1 ht 1 (-1 / (2 * N)) a (2 * N) ha ha2
    (by push_cast; linarith)
    (by
      intro x hx1 hx2
      push_cast at hx2
      have e : (1 : ℝ) + -1 / (2 * N) * x = 1 - x / (2 * N) := by ring
      rw [e, abs_le]
      have p1 : 0 ≤ x / (2 * N) := div_nonneg (by linarith) (by positivity)
      have p2 : x / (2 * N) ≤ 1 := by rw [div_le_one (by positivity)]; exact hx2
      constructor <;> linarith)
    (by
      rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
      exact one_div_le_one_div_of_le ha0 ha2')
  have e1 : ∀ x : ℝ, ((2 + (-1 / N) * x : ℝ) : ℂ) = 2 * ((1 + (-1 / (2 * N)) * x : ℝ) : ℂ) := by
    intro x; push_cast; field_simp
  have hs : ∑ n ∈ Ico a (2 * N), ((2 + (-1 / N) * n : ℝ) : ℂ) * (n : ℂ) ^ (-s) =
      2 * ∑ n ∈ Ico a (2 * N), ((1 + (-1 / (2 * N)) * n : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
    rw [mul_sum]; exact sum_congr rfl (fun n _ => by rw [e1, mul_assoc])
  have hi : ∫ x in (a : ℝ)..((2 * N : ℕ) : ℝ), ((2 + (-1 / N) * x : ℝ) : ℂ) * (x : ℂ) ^ (-s) =
      2 * ∫ x in (a : ℝ)..((2 * N : ℕ) : ℝ),
        ((1 + (-1 / (2 * N)) * x : ℝ) : ℂ) * (x : ℂ) ^ (-s) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; rw [e1, mul_assoc]
  rw [hs, hi, ← mul_sub, norm_mul, Complex.norm_two]
  linarith

/-! ### The integral bounds -/
lemma norm_u_ge (s : ℂ) : |s.im| ≤ ‖-s + 1‖ := by
  have := Complex.abs_im_le_norm (-s + 1); simpa using this

lemma norm_u1_ge (s : ℂ) : |s.im| ≤ ‖-s + 1 + 1‖ := by
  have := Complex.abs_im_le_norm (-s + 1 + 1); simpa using this

lemma norm_xu_le (s : ℂ) (h0 : 0 ≤ s.re) {x : ℝ} (hx : 1 ≤ x) : ‖(x : ℂ) ^ (-s + 1)‖ ≤ x := by
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
  calc x ^ (-s + 1).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by simp; linarith)
    _ = x := Real.rpow_one x

lemma nb1 (s : ℂ) (h0 : 0 ≤ s.re) (ht : 1 ≤ |s.im|) {x : ℝ} (hx : 1 ≤ x) :
    ‖(x : ℂ) ^ (-s + 1) / (-s + 1)‖ ≤ x / |s.im| := by
  rw [norm_div]
  exact div_le_div₀ (by linarith) (norm_xu_le s h0 hx) (by linarith) (norm_u_ge s)

lemma nb1' (s : ℂ) (h0 : 0 ≤ s.re) (ht : 1 ≤ |s.im|) {x : ℝ} (hx : 1 ≤ x) :
    ‖(x : ℂ) ^ (-s + 1) / (-s + 1 + 1)‖ ≤ x / |s.im| := by
  rw [norm_div]
  exact div_le_div₀ (by linarith) (norm_xu_le s h0 hx) (by linarith) (norm_u1_ge s)

lemma nb2 (s : ℂ) (h0 : 0 ≤ s.re) (ht : 1 ≤ |s.im|) {x : ℝ} (hx : 1 ≤ x) :
    ‖(x : ℂ) ^ (-s + 1) / ((-s + 1) * (-s + 1 + 1))‖ ≤ x / s.im ^ 2 := by
  rw [norm_div, norm_mul, ← sq_abs, sq]
  exact div_le_div₀ (by linarith) (norm_xu_le s h0 hx) (by nlinarith)
    (mul_le_mul (norm_u_ge s) (norm_u1_ge s) (abs_nonneg _) (norm_nonneg _))

lemma G_id1 (s : ℂ) (hu : -s + 1 ≠ 0) (hu1 : -s + 1 + 1 ≠ 0) {n x : ℝ} (hn : 0 < n) :
    G s 1 0 n - G s 1 0 x + (G s 2 (-1 / n) (2 * n) - G s 2 (-1 / n) n) =
      -((x : ℂ) ^ (-s + 1) / (-s + 1)) +
        2 * (((2 * n : ℝ) : ℂ) ^ (-s + 1) / ((-s + 1) * (-s + 1 + 1))) -
        (n : ℂ) ^ (-s + 1) / ((-s + 1) * (-s + 1 + 1)) := by
  unfold G
  have hn' : (n : ℂ) ≠ 0 := ofReal_ne_zero.2 hn.ne'
  generalize -s + 1 = u at *
  rw [cpow_succ_real (by positivity : (0 : ℝ) < 2 * n) u, cpow_succ_real hn u]
  push_cast
  field_simp
  ring

lemma G_id2 (s : ℂ) (hu : -s + 1 ≠ 0) (hu1 : -s + 1 + 1 ≠ 0) {n x : ℝ} (hn : 0 < n) (hx : 0 < x) :
    G s 2 (-1 / n) (2 * n) - G s 2 (-1 / n) x =
      2 * (((2 * n : ℝ) : ℂ) ^ (-s + 1) / ((-s + 1) * (-s + 1 + 1))) -
        2 * ((x : ℂ) ^ (-s + 1) / (-s + 1)) +
        ((x / n : ℝ) : ℂ) * ((x : ℂ) ^ (-s + 1) / (-s + 1 + 1)) := by
  unfold G
  have hn' : (n : ℂ) ≠ 0 := ofReal_ne_zero.2 hn.ne'
  generalize -s + 1 = u at *
  rw [cpow_succ_real (by positivity : (0 : ℝ) < 2 * n) u, cpow_succ_real hx u]
  push_cast
  field_simp
  ring

lemma u_ne (s : ℂ) (ht : 1 ≤ |s.im|) : -s + 1 ≠ 0 := by
  intro h; have := norm_u_ge s; rw [h, norm_zero] at this; linarith

lemma u1_ne (s : ℂ) (ht : 1 ≤ |s.im|) : -s + 1 + 1 ≠ 0 := by
  intro h; have := norm_u1_ge s; rw [h, norm_zero] at this; linarith

lemma int_bound1 (s : ℂ) (h0 : 0 ≤ s.re) (ht : 1 ≤ |s.im|) {n x : ℝ} (hn : 1 ≤ n) (hx : 1 ≤ x) :
    ‖G s 1 0 n - G s 1 0 x + (G s 2 (-1 / n) (2 * n) - G s 2 (-1 / n) n)‖ ≤
      x / |s.im| + 5 * (n / s.im ^ 2) := by
  rw [G_id1 s (u_ne s ht) (u1_ne s ht) (by linarith)]
  have a := nb1 s h0 ht hx
  have b := nb2 s h0 ht (by linarith : 1 ≤ 2 * n)
  have c := nb2 s h0 ht hn
  have q1 := norm_sub_le (-((x : ℂ) ^ (-s + 1) / (-s + 1)) +
    2 * (((2 * n : ℝ) : ℂ) ^ (-s + 1) / ((-s + 1) * (-s + 1 + 1))))
    ((n : ℂ) ^ (-s + 1) / ((-s + 1) * (-s + 1 + 1)))
  have q2 := norm_add_le (-((x : ℂ) ^ (-s + 1) / (-s + 1)))
    (2 * (((2 * n : ℝ) : ℂ) ^ (-s + 1) / ((-s + 1) * (-s + 1 + 1))))
  rw [norm_neg, norm_mul, Complex.norm_two] at q2
  have : 2 * n / s.im ^ 2 = 2 * (n / s.im ^ 2) := by ring
  linarith

lemma int_bound2 (s : ℂ) (h0 : 0 ≤ s.re) (ht : 1 ≤ |s.im|) {n x : ℝ} (hn : 1 ≤ n) (hx : 1 ≤ x)
    (hxn : x ≤ 2 * n) :
    ‖G s 2 (-1 / n) (2 * n) - G s 2 (-1 / n) x‖ ≤ 4 * (n / s.im ^ 2) + 4 * (x / |s.im|) := by
  rw [G_id2 s (u_ne s ht) (u1_ne s ht) (by linarith) (by linarith)]
  have b := nb2 s h0 ht (by linarith : 1 ≤ 2 * n)
  have a := nb1 s h0 ht hx
  have c := nb1' s h0 ht hx
  set A := ((2 * n : ℝ) : ℂ) ^ (-s + 1) / ((-s + 1) * (-s + 1 + 1))
  set B := (x : ℂ) ^ (-s + 1) / (-s + 1)
  set D := (x : ℂ) ^ (-s + 1) / (-s + 1 + 1)
  have hxn' : 0 ≤ x / n := by positivity
  have hxn2 : x / n ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have q1 := norm_add_le (2 * A - 2 * B) (((x / n : ℝ) : ℂ) * D)
  have q2 := norm_sub_le (2 * A) (2 * B)
  rw [norm_mul, norm_mul, Complex.norm_two] at q2
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hxn'] at q1
  have hD : x / n * ‖D‖ ≤ 2 * (x / |s.im|) :=
    mul_le_mul hxn2 c (norm_nonneg _) (by norm_num)
  have : 2 * n / s.im ^ 2 = 2 * (n / s.im ^ 2) := by ring
  have hxt : 0 ≤ x / |s.im| := by positivity
  linarith

/-! ### Assembly -/
lemma natlog_le (N : ℕ) (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (N + 2) := by
  have h1 : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h1
  have h3 : Real.log N ≤ Real.log (N + 2) := Real.log_le_log hN0 (by linarith)
  have h4 := Real.log_two_gt_d9
  have h5 : 0 ≤ (Nat.log 2 N : ℝ) := by positivity
  have h6 := mul_le_mul_of_nonneg_left h4.le h5
  have h7 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  nlinarith

lemma one_le_log (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Real.log (N + 2) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

lemma kernel_eq (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (M : ℕ) (h1 : 1 ≤ M) (h2 : M ≤ 2 * N) :
    kernel N s = ∑ m ∈ Ico 1 M, ((tentW N m : ℝ) : ℂ) * (m : ℂ) ^ (-s) +
      ∑ m ∈ Ico M (2 * N), ((tentW N m : ℝ) : ℂ) * (m : ℂ) ^ (-s) := by
  rw [sum_Ico_consecutive _ h1 h2, kernel, ← Finset.Ico_add_one_right_eq_Icc,
    sum_Ico_succ_top (by omega)]
  have : tentW N ((2 * N : ℕ) : ℝ) = 0 := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    unfold tentW; push_cast
    rw [if_neg (by linarith), if_pos le_rfl, mul_div_assoc, div_self hN0.ne']; ring
  rw [this]; simp

lemma large_part (CB : ℝ) (hCB : 0 < CB) (hB : BlockProp CB) (N : ℕ) (hN : 1 ≤ N) (s : ℂ)
    (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) (ht : 1 ≤ |s.im|) (X : ℕ) (hX1 : 10 * |s.im| ≤ X)
    (hX2 : (X : ℝ) ≤ 11 * |s.im|) (hX3 : X < 2 * N) :
    ‖∑ m ∈ Ico X (2 * N), ((tentW N m : ℝ) : ℂ) * (m : ℂ) ^ (-s)‖ ≤
      (5 * CB + 44) * Real.log (N + 2) + 5 * (N / s.im ^ 2) := by
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX0 : (1 : ℝ) ≤ X := by linarith
  have hl := one_le_log N hN
  have hxt : (X : ℝ) / |s.im| ≤ 11 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hNt : 0 ≤ (N : ℝ) / s.im ^ 2 := by positivity
  have hu := u_ne s ht
  have hu1 := u1_ne s ht
  have h2N : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have htop_sum : ∀ a : ℕ, N ≤ a →
      ∑ m ∈ Ico a (2 * N), ((tentW N m : ℝ) : ℂ) * (m : ℂ) ^ (-s) =
        ∑ m ∈ Ico a (2 * N), ((2 + (-1 / N) * m : ℝ) : ℂ) * (m : ℂ) ^ (-s) := by
    intro a ha
    refine sum_congr rfl (fun m hm => ?_)
    have hm' := mem_Ico.1 hm
    rw [tentW_eq_affine N hN (by exact_mod_cast (show N ≤ m by omega))
      (by exact_mod_cast (show m ≤ 2 * N by omega))]
  by_cases hXN : X ≤ N
  · -- bottom part `[X, N]` plus top block `[N, 2N]`
    rw [← sum_Ico_consecutive _ hXN (by omega), htop_sum N le_rfl]
    have hbot : ∑ m ∈ Ico X N, ((tentW N m : ℝ) : ℂ) * (m : ℂ) ^ (-s) =
        ∑ m ∈ Ico X N, (m : ℂ) ^ (-s) := by
      refine sum_congr rfl (fun m hm => ?_)
      have hm' := mem_Ico.1 hm
      rw [tentW_eq_one N (by exact_mod_cast hm'.2.le)]; simp
    rw [hbot]
    have hN10 : 10 * |s.im| ≤ (N : ℝ) := le_trans hX1 (by exact_mod_cast hXN)
    have hD := dyadic CB hCB hB s h0 h1 ht (Nat.log 2 N + 1) X N hX1 hXN (by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
      have hX' : 0 < X := by exact_mod_cast (by linarith : (0 : ℝ) < X)
      calc N ≤ 2 ^ (Nat.log 2 N + 1) := this.le
        _ ≤ 2 ^ (Nat.log 2 N + 1) * X := Nat.le_mul_of_pos_right _ hX')
    have hT := top_block CB hB s h0 h1 ht N hN N hN10 le_rfl (by omega)
    have hI1 := integral_affine s hu hu1 1 0 (by linarith : (0 : ℝ) < X)
      (by linarith : (0 : ℝ) < N)
    simp only [zero_mul, add_zero, ofReal_one, one_mul] at hI1
    have hI2 := integral_affine s hu hu1 2 (-1 / N) (by linarith : (0 : ℝ) < N)
      (by linarith : (0 : ℝ) < ((2 * N : ℕ) : ℝ))
    rw [hI1] at hD
    rw [hI2, h2N] at hT
    have hIB := int_bound1 s h0 ht hN0 hX0
    set S1 := ∑ m ∈ Ico X N, (m : ℂ) ^ (-s)
    set S2 := ∑ m ∈ Ico N (2 * N), ((2 + (-1 / N) * m : ℝ) : ℂ) * (m : ℂ) ^ (-s)
    have : S1 + S2 = (S1 - (G s 1 0 N - G s 1 0 X)) +
        (S2 - (G s 2 (-1 / N) (2 * N) - G s 2 (-1 / N) N)) +
        (G s 1 0 N - G s 1 0 X + (G s 2 (-1 / N) (2 * N) - G s 2 (-1 / N) N)) := by ring
    rw [this]
    have hL := natlog_le N hN
    refine norm_add₃_le.trans ?_
    push_cast at hD
    have k1 := mul_le_mul_of_nonneg_left hL hCB.le
    have k2 := mul_le_mul_of_nonneg_left hl hCB.le
    linarith
  · -- a single top block `[X, 2N]`
    push Not at hXN
    rw [htop_sum X hXN.le]
    have hT := top_block CB hB s h0 h1 ht N hN X hX1 hXN.le hX3.le
    have hI2 := integral_affine s hu hu1 2 (-1 / N) (by linarith : (0 : ℝ) < X)
      (by linarith : (0 : ℝ) < ((2 * N : ℕ) : ℝ))
    rw [hI2, h2N] at hT
    have hIB := int_bound2 s h0 ht hN0 hX0 (by
      have : (X : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hX3.le
      linarith)
    set S2 := ∑ m ∈ Ico X (2 * N), ((2 + (-1 / N) * m : ℝ) : ℂ) * (m : ℂ) ^ (-s)
    have : S2 = (S2 - (G s 2 (-1 / N) (2 * N) - G s 2 (-1 / N) X)) +
        (G s 2 (-1 / N) (2 * N) - G s 2 (-1 / N) X) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have k2 := mul_le_mul_of_nonneg_left hl hCB.le
    linarith

lemma main_bound (CV CB : ℝ) (hCB : 0 < CB)
    (hV : ∀ t : ℝ, 1 ≤ |t| → ∀ c : ℕ, (c : ℝ) ≤ 11 * |t| + 2 →
      ‖∑ m ∈ Finset.Icc 1 c, (m : ℂ) ^ (-((t : ℂ) * I))‖ ≤
        CV * (|t| ^ (1 / 2 : ℝ) * Real.log (|t| + 2)))
    (hB : BlockProp CB) (N : ℕ) (hN : 1 ≤ N) (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2)
    (ht : 1 ≤ |s.im|) :
    ‖kernel N s‖ ≤ CV * (|s.im| ^ (1 / 2 : ℝ) * Real.log (|s.im| + 2)) +
      ((5 * CB + 44) * Real.log (N + 2) + 5 * (N / s.im ^ 2)) := by
  set X := ⌈10 * |s.im|⌉₊ with hXdef
  have hX1 : 10 * |s.im| ≤ X := Nat.le_ceil _
  have hX2 : (X : ℝ) < 10 * |s.im| + 1 := Nat.ceil_lt_add_one (by positivity)
  have hX10 : 1 ≤ X := by
    have : (1 : ℝ) ≤ X := by linarith
    exact_mod_cast this
  have hl := one_le_log N hN
  have hNt : 0 ≤ (N : ℝ) / s.im ^ 2 := by positivity
  have hlpos : 0 ≤ (5 * CB + 44) * Real.log (N + 2) := by positivity
  rw [kernel_eq N hN s (min X (2 * N)) (by omega) (min_le_right _ _)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · apply small_part CV hV N hN s h0 ht
    have : ((min X (2 * N) : ℕ) : ℝ) ≤ X := by exact_mod_cast min_le_left _ _
    linarith
  · by_cases hX : X < 2 * N
    · rw [min_eq_left hX.le]
      exact large_part CB hCB hB N hN s h0 h1 ht X hX1 (by linarith) hX
    · push Not at hX
      rw [min_eq_right hX, Ico_self, sum_empty, norm_zero]
      linarith

theorem kernel_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 / 2 →
    1 ≤ |s.im| →
    ‖kernel N s‖ ≤ C * ((N : ℝ) / s.im ^ 2 + |s.im| ^ (1 / 2 : ℝ) * Real.log (|s.im| + 2) +
      Real.log (N + 2)) := by
  obtain ⟨CV, hCV, hV⟩ := GuthMaynard.CitedLV.partial_sum_cpow_le
  obtain ⟨CB, hCB, hB⟩ := GuthMaynard.CitedLV.block_sum_sub_integral_le
  refine ⟨CV + 5 * CB + 60, by positivity, ?_⟩
  intro N hN s h0 h1 ht
  have hM := main_bound CV CB hCB hV hB N hN s h0 h1 ht
  have hA : 0 ≤ |s.im| ^ (1 / 2 : ℝ) * Real.log (|s.im| + 2) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by linarith [abs_nonneg s.im]))
  have hl : 0 ≤ Real.log (N + 2) := by linarith [one_le_log N hN]
  have hNt : 0 ≤ (N : ℝ) / s.im ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show CV ≤ CV + 5 * CB + 60 by linarith) hA,
    mul_le_mul_of_nonneg_right (show 5 * CB + 44 ≤ CV + 5 * CB + 60 by linarith) hl,
    mul_le_mul_of_nonneg_right (show (5 : ℝ) ≤ CV + 5 * CB + 60 by linarith) hNt]

end
end GuthMaynard.CitedLV.PartK
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section
/-! ## Part K: the kernel bound -/
alias kernel_bound := GuthMaynard.CitedLV.PartK.kernel_bound

end
end GuthMaynard.CitedLV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.PartH
noncomputable section
/-! ## Helpers -/
lemma tentW_pos_N {N : ℕ} {x : ℝ} (h1 : ¬ x ≤ N) (h2 : x ≤ 2 * N) : (0 : ℝ) < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp at h1 h2; linarith
  · exact_mod_cast h

lemma tentW_nonneg (N : ℕ) (x : ℝ) : 0 ≤ tentW N x := by
  unfold tentW
  split_ifs with h1 h2
  · norm_num
  · have hN := tentW_pos_N h1 h2
    rw [sub_nonneg, div_le_iff₀ hN]; linarith
  · exact le_refl _

lemma tentW_le_one (N : ℕ) (x : ℝ) : tentW N x ≤ 1 := by
  unfold tentW
  split_ifs with h1 h2
  · exact le_refl _
  · have hN := tentW_pos_N h1 h2
    have : 1 ≤ x / N := by rw [le_div_iff₀ hN]; linarith
    linarith
  · norm_num

lemma tentW_eq_one (N : ℕ) (x : ℝ) (h : x ≤ N) : tentW N x = 1 := by simp [tentW, h]

lemma natCast_cpow_mul_conj (m : ℕ) (hm : 1 ≤ m) (z w : ℂ) :
    (m : ℂ) ^ (-z) * (starRingEnd ℂ) ((m : ℂ) ^ (-w)) =
      (m : ℂ) ^ (-(z + (starRingEnd ℂ) w)) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have harg : (m : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h1 : (starRingEnd ℂ) ((m : ℂ) ^ (-w)) = (m : ℂ) ^ (-(starRingEnd ℂ) w) := by
    rw [← map_neg, Complex.cpow_conj _ _ harg, Complex.conj_natCast]
  rw [h1, ← Complex.cpow_add _ _ hm0]; congr 1; ring

lemma norm_natCast_cpow_neg_le (m : ℕ) (hm : 1 ≤ m) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖(m : ℂ) ^ (-z)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm)
  simp; linarith

lemma norm_kernel_le (N : ℕ) (z : ℂ) (hz : 0 ≤ z.re) : ‖kernel N z‖ ≤ 2 * N := by
  unfold kernel
  calc _ ≤ ∑ m ∈ Icc 1 (2 * N), ‖((tentW N m : ℝ) : ℂ) * (m : ℂ) ^ (-z)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Icc 1 (2 * N), (1 : ℝ) := by
        apply sum_le_sum; intro m hm
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tentW_nonneg _ _)]
        have := norm_natCast_cpow_neg_le m (mem_Icc.1 hm).1 z hz
        have := tentW_le_one N m
        have := tentW_nonneg N m
        nlinarith [norm_nonneg ((m : ℂ) ^ (-z))]
    _ = 2 * N := by simp

/-! ## Targets -/
theorem halasz_ineq {ι : Type*} (N : ℕ) (a : ℕ → ℂ) (P : Finset ι) (s : ι → ℂ) (V : ℝ)
    (hV : 0 ≤ V) (hF : ∀ r ∈ P, V ≤ ‖dirPoly N a (s r)‖) :
    ((P.card : ℝ) * V) ^ 2 ≤ (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) *
      ∑ r ∈ P, ∑ q ∈ P, ‖kernel N (s r + (starRingEnd ℂ) (s q))‖ := by
  set F : ι → ℂ := fun r => dirPoly N a (s r) with hFdef
  set η : ι → ℂ := fun r => (starRingEnd ℂ) (F r) / (‖F r‖ : ℂ) with hη
  set B : ℕ → ℂ := fun m => ∑ r ∈ P, η r * (m : ℂ) ^ (-s r) with hB
  have hηF : ∀ r, η r * F r = (‖F r‖ : ℂ) := by
    intro r
    by_cases h : F r = 0
    · simp [hη, h]
    · have : (‖F r‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h)
      simp only [hη]; rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff this]; ring
  have hηn : ∀ r, ‖η r‖ ≤ 1 := by
    intro r
    simp only [hη]
    rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  have h1 : (P.card : ℝ) * V ≤ ∑ r ∈ P, ‖F r‖ := by
    have := sum_le_sum hF
    simpa [sum_const, nsmul_eq_mul] using this
  have h2 : ((∑ r ∈ P, ‖F r‖ : ℝ) : ℂ) = ∑ m ∈ Icc 1 N, a m * B m := by
    push_cast
    simp_rw [← hηF]
    simp only [hFdef, dirPoly, hB, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro r _; apply sum_congr rfl; intro m _; ring
  have h3 : ∑ r ∈ P, ‖F r‖ ≤ ∑ m ∈ Icc 1 N, ‖a m‖ * ‖B m‖ := by
    have hnn : 0 ≤ ∑ r ∈ P, ‖F r‖ := sum_nonneg (fun _ _ => norm_nonneg _)
    calc ∑ r ∈ P, ‖F r‖ = ‖((∑ r ∈ P, ‖F r‖ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      _ = ‖∑ m ∈ Icc 1 N, a m * B m‖ := by rw [h2]
      _ ≤ ∑ m ∈ Icc 1 N, ‖a m * B m‖ := norm_sum_le _ _
      _ = ∑ m ∈ Icc 1 N, ‖a m‖ * ‖B m‖ := by simp_rw [norm_mul]
  have h4 : (∑ m ∈ Icc 1 N, ‖a m‖ * ‖B m‖) ^ 2 ≤
      (∑ m ∈ Icc 1 N, ‖a m‖ ^ 2) * ∑ m ∈ Icc 1 N, ‖B m‖ ^ 2 :=
    sum_mul_sq_le_sq_mul_sq _ _ _
  set X : ℝ := ∑ m ∈ Icc 1 (2 * N), tentW N m * ‖B m‖ ^ 2 with hX
  have h5 : ∑ m ∈ Icc 1 N, ‖B m‖ ^ 2 ≤ X := by
    calc ∑ m ∈ Icc 1 N, ‖B m‖ ^ 2 = ∑ m ∈ Icc 1 N, tentW N m * ‖B m‖ ^ 2 := by
          apply sum_congr rfl; intro m hm
          rw [tentW_eq_one N m (by exact_mod_cast (mem_Icc.1 hm).2), one_mul]
      _ ≤ X := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro m hm; simp only [mem_Icc] at hm ⊢; omega
          · intro m _ _; exact mul_nonneg (tentW_nonneg _ _) (by positivity)
  have h6 : (X : ℂ) = ∑ r ∈ P, ∑ q ∈ P,
      η r * (starRingEnd ℂ) (η q) * kernel N (s r + (starRingEnd ℂ) (s q)) := by
    have e1 : (X : ℂ) = ∑ m ∈ Icc 1 (2 * N), ∑ r ∈ P, ∑ q ∈ P,
        η r * (starRingEnd ℂ) (η q) *
          (((tentW N m : ℝ) : ℂ) * ((m : ℂ) ^ (-s r) * (starRingEnd ℂ) ((m : ℂ) ^ (-s q)))) := by
      simp only [hX]
      push_cast
      apply sum_congr rfl; intro m _
      rw [← Complex.mul_conj']
      simp only [hB, map_sum, map_mul, sum_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl; intro r _; apply sum_congr rfl; intro q _; ring
    rw [e1, sum_comm]
    apply sum_congr rfl; intro r _
    rw [sum_comm]
    apply sum_congr rfl; intro q _
    unfold kernel
    rw [mul_sum]
    apply sum_congr rfl; intro m hm
    rw [natCast_cpow_mul_conj m (mem_Icc.1 hm).1]
  have h7 : X ≤ ∑ r ∈ P, ∑ q ∈ P, ‖kernel N (s r + (starRingEnd ℂ) (s q))‖ := by
    have hX0 : 0 ≤ X := sum_nonneg (fun m _ => mul_nonneg (tentW_nonneg _ _) (by positivity))
    calc X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
      _ ≤ _ := by
        rw [h6]
        refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun q _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have := hηn r
        have := hηn q
        have := norm_nonneg (η r)
        have := norm_nonneg (η q)
        have := norm_nonneg (kernel N (s r + (starRingEnd ℂ) (s q)))
        have : ‖η r‖ * ‖η q‖ ≤ 1 := by nlinarith
        nlinarith
  have hG0 : 0 ≤ ∑ m ∈ Icc 1 N, ‖a m‖ ^ 2 := sum_nonneg (fun _ _ => by positivity)
  have hPV : 0 ≤ (P.card : ℝ) * V := by positivity
  calc ((P.card : ℝ) * V) ^ 2 ≤ (∑ r ∈ P, ‖F r‖) ^ 2 := pow_le_pow_left₀ hPV h1 2
    _ ≤ (∑ m ∈ Icc 1 N, ‖a m‖ * ‖B m‖) ^ 2 :=
        pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) h3 2
    _ ≤ _ := h4
    _ ≤ _ := mul_le_mul_of_nonneg_left (h5.trans h7) hG0

end
end GuthMaynard.CitedLV.PartH
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section
/-! ## Part H: Halász–Montgomery and subdivision -/

end
end GuthMaynard.CitedLV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.PartH
noncomputable section
/-- Corrected form, with `r ∈ P`. -/
theorem sum_inv_sq_le_of_separated {ι : Type*} [DecidableEq ι] (P : Finset ι) (t : ι → ℝ)
    (ht : ∀ r ∈ P, ∀ q ∈ P, r ≠ q → 1 ≤ |t r - t q|) (r : ι) (hr : r ∈ P) :
    ∑ q ∈ P.erase r, 1 / (t r - t q) ^ 2 ≤ 4 := by
  set E := P.erase r with hE
  let k : ι → ℕ := fun q => ⌊|t r - t q|⌋₊
  let φ : ι → Bool × ℕ := fun q => (decide (t q < t r), k q)
  have hk1 : ∀ q ∈ E, 1 ≤ k q := fun q hq => by
    have := ht r hr q (mem_of_mem_erase hq) (ne_of_mem_erase hq).symm
    exact Nat.le_floor (by simpa using this)
  have hinj : Set.InjOn φ E := by
    intro q hq q' hq' h
    simp only [φ, Prod.mk.injEq, decide_eq_decide] at h
    obtain ⟨hs, hkk⟩ := h
    by_contra hne
    have hsep := ht q (mem_of_mem_erase hq) q' (mem_of_mem_erase hq') hne
    have h1 : (k q : ℝ) ≤ |t r - t q| := Nat.floor_le (abs_nonneg _)
    have h2 : |t r - t q| < k q + 1 := Nat.lt_floor_add_one _
    have h3 : (k q' : ℝ) ≤ |t r - t q'| := Nat.floor_le (abs_nonneg _)
    have h4 : |t r - t q'| < k q' + 1 := Nat.lt_floor_add_one _
    have e : (k q : ℝ) = k q' := by exact_mod_cast hkk
    have hlt : |t q - t q'| < 1 := by
      by_cases hq1 : t q < t r
      · have hq2 : t q' < t r := hs.1 hq1
        have ea := abs_of_pos (by linarith : 0 < t r - t q)
        have eb := abs_of_pos (by linarith : 0 < t r - t q')
        rw [abs_lt]; constructor <;> linarith
      · have hq2 : ¬ t q' < t r := fun h => hq1 (hs.2 h)
        rw [not_lt] at hq1 hq2
        have ea := abs_of_nonpos (by linarith : t r - t q ≤ 0)
        have eb := abs_of_nonpos (by linarith : t r - t q' ≤ 0)
        rw [abs_lt]; constructor <;> linarith
    linarith
  have hS : ∀ q ∈ E, 1 / (t r - t q) ^ 2 ≤ 1 / ((k q : ℝ)) ^ 2 := by
    intro q hq
    have hk := hk1 q hq
    have hpos : (0 : ℝ) < k q := by exact_mod_cast hk
    apply one_div_le_one_div_of_le (by positivity)
    have := Nat.floor_le (abs_nonneg (t r - t q))
    rw [← sq_abs (t r - t q)]
    exact pow_le_pow_left₀ hpos.le this 2
  set M := (E.image k).sup id + 1 with hM
  calc ∑ q ∈ E, 1 / (t r - t q) ^ 2 ≤ ∑ q ∈ E, 1 / ((k q : ℝ)) ^ 2 := sum_le_sum hS
    _ = ∑ x ∈ E.image φ, 1 / ((x.2 : ℝ)) ^ 2 := (sum_image (f := fun x : Bool × ℕ => 1 / ((x.2 : ℝ)) ^ 2) hinj).symm
    _ ≤ ∑ x ∈ (univ : Finset Bool) ×ˢ Ioo 0 M, 1 / ((x.2 : ℝ)) ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨q, hq, rfl⟩ := mem_image.1 hx
          simp only [mem_product, mem_univ, true_and, mem_Ioo, φ]
          refine ⟨hk1 q hq, ?_⟩
          have : k q ≤ (E.image k).sup id := Finset.le_sup (f := id) (mem_image_of_mem k hq)
          omega
        · intro _ _ _; positivity
    _ = 2 * ∑ i ∈ Ioo 0 M, ((i : ℝ) ^ 2)⁻¹ := by
        rw [sum_product]; simp [two_mul]
    _ ≤ 2 * 2 := by
        have := sum_Ioo_inv_sq_le (α := ℝ) 0 M
        norm_num at this
        linarith
    _ = 4 := by norm_num

end
end GuthMaynard.CitedLV.PartH
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section

end
end GuthMaynard.CitedLV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.PartH
noncomputable section
theorem card_le_of_separated {ι : Type*} (P : Finset ι) (t : ι → ℝ) (T : ℝ) (hT0 : 0 ≤ T)
    (ht : ∀ r ∈ P, ∀ q ∈ P, r ≠ q → 1 ≤ |t r - t q|)
    (hT : ∀ r ∈ P, ∀ q ∈ P, |t r - t q| ≤ T) :
    (P.card : ℝ) ≤ T + 1 := by
  classical
  rcases P.eq_empty_or_nonempty with h | hne
  · simp [h]; linarith
  obtain ⟨r0, hr0, hmin⟩ := P.exists_min_image t hne
  let k : ι → ℕ := fun q => ⌊t q - t r0⌋₊
  have hmaps : ∀ q ∈ P, k q ∈ range (⌊T⌋₊ + 1) := by
    intro q hq
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    exact le_trans (le_abs_self _) (hT q hq r0 hr0)
  have hinj : Set.InjOn k P := by
    intro q hq q' hq' h
    by_contra hne
    have hsep := ht q hq q' hq' hne
    have a1 := Nat.floor_le (sub_nonneg.2 (hmin q hq))
    have a2 := Nat.lt_floor_add_one (t q - t r0)
    have a3 := Nat.floor_le (sub_nonneg.2 (hmin q' hq'))
    have a4 := Nat.lt_floor_add_one (t q' - t r0)
    simp only [k] at h
    rw [h] at a1 a2
    have : |t q - t q'| < 1 := by rw [abs_lt]; constructor <;> linarith
    linarith
  have := card_le_card_of_injOn k (fun q hq => hmaps q hq) hinj
  simp only [card_range] at this
  calc (P.card : ℝ) ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
    _ ≤ T + 1 := by push_cast; linarith [Nat.floor_le hT0]

end
end GuthMaynard.CitedLV.PartH
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section

end
end GuthMaynard.CitedLV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.PartH
noncomputable section
theorem card_le_of_halasz : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, 1 ≤ N → ∀ T' : ℝ, 0 ≤ T' →
    ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V → ∀ {ι : Type} (P : Finset ι) (s : ι → ℂ),
    (∀ r ∈ P, 0 ≤ (s r).re ∧ (s r).re ≤ 1 / 4) →
    (∀ r ∈ P, ∀ q ∈ P, r ≠ q → 1 ≤ |(s r).im - (s q).im|) →
    (∀ r ∈ P, ∀ q ∈ P, |(s r).im - (s q).im| ≤ T') →
    (∀ r ∈ P, V ≤ ‖dirPoly N a (s r)‖) →
    C₁ * (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) *
      (T' ^ (1 / 2 : ℝ) * Real.log (T' + 2) + Real.log (N + 2)) ≤ V ^ 2 →
    (P.card : ℝ) ≤ C₂ * (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) * N / V ^ 2 := by
  obtain ⟨C, hC, hK⟩ := GuthMaynard.CitedLV.kernel_bound
  refine ⟨2 * C, 4 + 8 * C, by positivity, by positivity, ?_⟩
  intro N hN T' hT' a V hV ι P s hre hsep hdiam hF hcond
  classical
  set G := ∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2 with hG
  set L := T' ^ (1 / 2 : ℝ) * Real.log (T' + 2) + Real.log (N + 2) with hL
  have hG0 : 0 ≤ G := sum_nonneg (fun _ _ => by positivity)
  have hL0 : 0 ≤ L := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T' + 2)
    have := Real.log_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith : (1 : ℝ) ≤ (N : ℝ) + 2)
    positivity
  have hrow : ∀ r ∈ P, ∑ q ∈ P, ‖kernel N (s r + (starRingEnd ℂ) (s q))‖ ≤
      (2 + 4 * C) * N + C * P.card * L := by
    intro r hr
    rw [← add_sum_erase P _ hr]
    have hdiag : ‖kernel N (s r + (starRingEnd ℂ) (s r))‖ ≤ 2 * N :=
      norm_kernel_le N _ (by simp; linarith [(hre r hr).1])
    have hoff : ∀ q ∈ P.erase r, ‖kernel N (s r + (starRingEnd ℂ) (s q))‖ ≤
        C * (N * (1 / ((s r).im - (s q).im) ^ 2) + L) := by
      intro q hq
      have hqP := mem_of_mem_erase hq
      have hne : r ≠ q := (ne_of_mem_erase hq).symm
      have h1 := hsep r hr q hqP hne
      have h2 := hdiam r hr q hqP
      have hzre : (s r + (starRingEnd ℂ) (s q)).re = (s r).re + (s q).re := by simp
      have hzim : (s r + (starRingEnd ℂ) (s q)).im = (s r).im - (s q).im := by simp; ring
      have := hK N hN (s r + (starRingEnd ℂ) (s q))
        (by rw [hzre]; linarith [(hre r hr).1, (hre q hqP).1])
        (by rw [hzre]; linarith [(hre r hr).2, (hre q hqP).2]) (by rw [hzim]; exact h1)
      refine this.trans ?_
      rw [hzim]
      apply mul_le_mul_of_nonneg_left _ hC.le
      have hmono : |(s r).im - (s q).im| ^ (1 / 2 : ℝ) * Real.log (|(s r).im - (s q).im| + 2) ≤
          T' ^ (1 / 2 : ℝ) * Real.log (T' + 2) := by
        apply mul_le_mul
        · exact Real.rpow_le_rpow (abs_nonneg _) h2 (by norm_num)
        · exact Real.log_le_log (by positivity) (by linarith)
        · exact Real.log_nonneg (by linarith [abs_nonneg ((s r).im - (s q).im)])
        · positivity
      have : (N : ℝ) / ((s r).im - (s q).im) ^ 2 = N * (1 / ((s r).im - (s q).im) ^ 2) := by
        rw [mul_one_div]
      rw [this]
      linarith
    have hinv : ∑ q ∈ P.erase r, 1 / ((s r).im - (s q).im) ^ 2 ≤ 4 :=
      sum_inv_sq_le_of_separated P (fun r => (s r).im)
        (fun r hr q hq hne => hsep r hr q hq hne) r hr
    have hcardE : ((P.erase r).card : ℝ) ≤ P.card := by exact_mod_cast card_erase_le
    calc _ ≤ (2 : ℝ) * N + ∑ q ∈ P.erase r, C * (N * (1 / ((s r).im - (s q).im) ^ 2) + L) :=
          add_le_add hdiag (sum_le_sum hoff)
      _ = (2 : ℝ) * N + C * (N * ∑ q ∈ P.erase r, 1 / ((s r).im - (s q).im) ^ 2 +
            (P.erase r).card * L) := by
          rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) * N + C * (N * 4 + P.card * L) :=
by
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          have e1 := mul_le_mul_of_nonneg_left hinv hN0
          have e2 := mul_le_mul_of_nonneg_right hcardE hL0
          have e3 := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC.le
          linarith
      _ = _ := by ring
  have htot : ∑ r ∈ P, ∑ q ∈ P, ‖kernel N (s r + (starRingEnd ℂ) (s q))‖ ≤
      P.card * ((2 + 4 * C) * N + C * P.card * L) := by
    have := sum_le_sum hrow
    rwa [sum_const, nsmul_eq_mul] at this
  have hhal := halasz_ineq N a P s V hV.le hF
  set p : ℝ := (P.card : ℝ) with hp
  have hp0 : 0 ≤ p := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have key : (p * V) ^ 2 ≤ G * (p * ((2 + 4 * C) * N + C * p * L)) :=
    hhal.trans (mul_le_mul_of_nonneg_left htot hG0)
  have hcond' : 2 * C * G * L ≤ V ^ 2 := hcond
  rcases hp0.lt_or_eq with hpos | hzero
  · rw [le_div_iff₀ (by positivity)]
    have h2 : p * (p * V ^ 2) ≤ p * ((4 + 8 * C) * G * N) := by
      have : p * p * (C * G * L) ≤ p * p * (V ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have := le_of_mul_le_mul_left h2 hpos
    linarith
  · rw [← hzero]; positivity

end
end GuthMaynard.CitedLV.PartH
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section

end
end GuthMaynard.CitedLV
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.PartH
noncomputable section
lemma huxley_logs (N : ℕ) (hN : 1 ≤ N) (T : ℝ) (hT : 2 ≤ T) :
    0 ≤ Real.log (N + 2) ∧ Real.log (N + 2) ≤ 2 * N ∧
    Real.log (N + 2) ≤ 2 * Real.log (N * T) ∧ 0 < Real.log (T + 2) ∧
    Real.log (T + 2) ≤ 2 * Real.log (N * T) ∧ 0 ≤ Real.log (N * T) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNT : T ≤ N * T := by nlinarith
  refine ⟨Real.log_nonneg (by linarith), ?_, ?_, Real.log_pos (by linarith), ?_,
    Real.log_nonneg (by nlinarith)⟩
  · have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N + 2)
    linarith
  · rw [← Real.log_rpow (by nlinarith)]
    apply Real.log_le_log (by linarith)
    rw [Real.rpow_two]
    have h2N : (2 : ℝ) * N ≤ N * T := by nlinarith
    have := mul_le_mul h2N h2N (by positivity) (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 hN1) (by positivity : (0 : ℝ) ≤ N)]
  · rw [← Real.log_rpow (by nlinarith)]
    apply Real.log_le_log (by linarith)
    rw [Real.rpow_two]
    have := mul_le_mul hNT hNT (by positivity) (by positivity)
    nlinarith

/-- The published statement `GuthMaynard.card_le_of_large_values_huxley`, verbatim. -/
theorem card_le_of_large_values_huxley :
    ∃ C : ℝ, ∀ (N : ℕ), 1 ≤ N → ∀ T : ℝ, 2 ≤ T → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re ∧ (s r).re ≤ 1 / 4) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im| ∧ |(s r).im - (s q).im| ≤ T) →
      (∀ r, V ≤ ‖∑ m ∈ Finset.Icc 1 N, a m * (m : ℂ) ^ (-s r)‖) →
      (R : ℝ) ≤ C * ((∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) * N / V ^ 2 +
        (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) ^ 3 * N * T / V ^ 6 * Real.log (N * T) ^ 2) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hH⟩ := GuthMaynard.CitedLV.PartH.card_le_of_halasz
  refine ⟨C₂ + 16 * C₁ ^ 2 * C₂ + 128 * C₁ ^ 3, ?_⟩
  intro N hN T hT a V hV R s hre hsep hF
  obtain ⟨hl30, hl3N, hl3T, hℓ, hℓT, hlNT0⟩ := huxley_logs N hN T hT
  set G := ∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2 with hG
  set lNT := Real.log (N * T) with hlNT
  set l3 := Real.log (N + 2) with hl3
  set ℓ := Real.log (T + 2) with hℓdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hG0 : 0 ≤ G := sum_nonneg (fun _ _ => by positivity)
  set A := G * N / V ^ 2 with hA
  set W := G ^ 3 * N * T / V ^ 6 with hW
  have hA0 : 0 ≤ A := by positivity
  have hW0 : 0 ≤ W := by positivity
  have hB0 : 0 ≤ W * lNT ^ 2 := by positivity
  have hX0 : 0 ≤ C₂ * A := mul_nonneg hC₂.le hA0
  have hY0 : 0 ≤ 16 * C₁ ^ 2 * C₂ * (W * lNT ^ 2) := by positivity
  have hZ0 : 0 ≤ 128 * C₁ ^ 3 * (W * lNT ^ 2) := by positivity
  suffices h : (R : ℝ) ≤ C₂ * A + 16 * C₁ ^ 2 * C₂ * (W * lNT ^ 2) +
      128 * C₁ ^ 3 * (W * lNT ^ 2) by
    have e1 : 0 ≤ (16 * C₁ ^ 2 * C₂ + 128 * C₁ ^ 3) * A := by positivity
    have e2 : 0 ≤ C₂ * (W * lNT ^ 2) := by positivity
    linarith
  rcases Nat.eq_zero_or_pos R with hR | hR
  · have : (R : ℝ) = 0 := by simp [hR]
    rw [this]; linarith
  let i0 : Fin R := ⟨0, hR⟩
  have hGpos : 0 < G := by
    rcases hG0.lt_or_eq with h | h
    · exact h
    exfalso
    have hz : ∀ m ∈ Icc 1 N, a m = 0 := by
      intro m hm
      have := (sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h.symm m hm
      simpa using this
    have := hF i0
    rw [sum_eq_zero (fun m hm => by rw [hz m hm, zero_mul])] at this
    simp at this; linarith
  have hHP : ∀ (P : Finset (Fin R)) (T' : ℝ), 0 ≤ T' →
      (∀ r ∈ P, ∀ q ∈ P, |(s r).im - (s q).im| ≤ T') →
      C₁ * G * (T' ^ (1 / 2 : ℝ) * Real.log (T' + 2) + l3) ≤ V ^ 2 →
      (P.card : ℝ) ≤ C₂ * A := by
    intro P T' hT' hd hc
    have := hH N hN T' hT' a V hV P s (fun r _ => hre r) (fun r _ q _ h => (hsep r q h).1) hd
      (fun r _ => hF r) hc
    calc (P.card : ℝ) ≤ C₂ * G * N / V ^ 2 := this
      _ = C₂ * A := by rw [hA]; ring
  have hdiamU : ∀ r ∈ (univ : Finset (Fin R)), ∀ q ∈ (univ : Finset (Fin R)),
      |(s r).im - (s q).im| ≤ T := by
    intro r _ q _
    by_cases h : r = q
    · simp [h]; linarith
    · exact (hsep r q h).2
  by_cases hc : V ^ 2 < 2 * C₁ * G * l3
  · have hRT : (R : ℝ) ≤ T + 1 := by
      have := card_le_of_separated (univ : Finset (Fin R)) (fun r => (s r).im) T (by linarith)
        (fun r _ q _ h => (hsep r q h).1) hdiamU
      simpa using this
    have hV6 : V ^ 6 < 8 * C₁ ^ 3 * G ^ 3 * l3 ^ 3 := by
      have := pow_lt_pow_left₀ hc (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
      calc V ^ 6 = (V ^ 2) ^ 3 := by ring
        _ < (2 * C₁ * G * l3) ^ 3 := this
        _ = _ := by ring
    have hl3c : l3 ^ 3 ≤ 8 * N * lNT ^ 2 := by
      calc l3 ^ 3 = l3 * (l3 * l3) := by ring
        _ ≤ (2 * N) * ((2 * lNT) * (2 * lNT)) :=
            mul_le_mul hl3N (mul_le_mul hl3T hl3T hl30 (by positivity)) (by positivity)
              (by positivity)
        _ = _ := by ring
    have hWV : W * V ^ 6 = G ^ 3 * N * T := by
      simp only [hW]; field_simp
    have hC3 : 0 ≤ C₁ ^ 3 * G ^ 3 := by positivity
    have key : 2 * T * V ^ 6 ≤ 128 * C₁ ^ 3 * (W * lNT ^ 2) * V ^ 6 := by
      calc 2 * T * V ^ 6 ≤ 2 * T * (8 * C₁ ^ 3 * G ^ 3 * l3 ^ 3) :=
            mul_le_mul_of_nonneg_left hV6.le (by positivity)
        _ = 16 * T * (C₁ ^ 3 * G ^ 3) * l3 ^ 3 := by ring
        _ ≤ 16 * T * (C₁ ^ 3 * G ^ 3) * (8 * N * lNT ^ 2) :=
            mul_le_mul_of_nonneg_left hl3c (by positivity)
        _ = 128 * C₁ ^ 3 * lNT ^ 2 * (W * V ^ 6) := by rw [hWV]; ring
        _ = _ := by ring
    have := le_of_mul_le_mul_right key (by positivity)
    linarith
  rw [not_lt] at hc
  have hGne : G ≠ 0 := hGpos.ne'
  have hVne : V ≠ 0 := hV.ne'
  have hC₁ne : C₁ ≠ 0 := hC₁.ne'
  have hℓne : ℓ ≠ 0 := hℓ.ne'
  set u := V ^ 2 / (2 * C₁ * G * ℓ) with hu
  have hu0 : 0 < u := by positivity
  have hcondT : ∀ T' : ℝ, 0 ≤ T' → T' ≤ T → T' ^ (1 / 2 : ℝ) ≤ u →
      C₁ * G * (T' ^ (1 / 2 : ℝ) * Real.log (T' + 2) + l3) ≤ V ^ 2 := by
    intro T' h0 h1 h2
    have e1 : T' ^ (1 / 2 : ℝ) * Real.log (T' + 2) ≤ u * ℓ :=
      mul_le_mul h2 (Real.log_le_log (by linarith) (by linarith))
        (Real.log_nonneg (by linarith)) hu0.le
    have e2 : C₁ * G * (u * ℓ) = V ^ 2 / 2 := by
      simp only [hu]; field_simp
    have e3 := mul_le_mul_of_nonneg_left e1 (by positivity : 0 ≤ C₁ * G)
    linarith
  by_cases hTT : T ≤ u ^ 2
  · have hsq : T ^ (1 / 2 : ℝ) ≤ u := by
      calc T ^ (1 / 2 : ℝ) ≤ (u ^ 2) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) hTT (by norm_num)
        _ = u := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hu0.le]
    have := hHP univ T (by linarith) hdiamU (hcondT T (by linarith) le_rfl hsq)
    simp only [card_univ, Fintype.card_fin] at this
    linarith
  rw [not_le] at hTT
  set T₀ := u ^ 2 with hT₀
  have hT₀pos : 0 < T₀ := by positivity
  have hhalf : T₀ ^ (1 / 2 : ℝ) = u := by
    rw [hT₀, ← Real.sqrt_eq_rpow, Real.sqrt_sq hu0.le]
  have hc0 := hcondT T₀ hT₀pos.le hTT.le hhalf.le
  obtain ⟨r0, -, hmin⟩ := (univ : Finset (Fin R)).exists_min_image (fun r => (s r).im)
    ⟨i0, mem_univ _⟩
  let j : Fin R → ℕ := fun r => ⌊((s r).im - (s r0).im) / T₀⌋₊
  set M := ⌊T / T₀⌋₊ with hM
  have hmaps : ∀ r ∈ (univ : Finset (Fin R)), j r ∈ range (M + 1) := by
    intro r _
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hT₀pos.le
    exact (le_abs_self _).trans (hdiamU r (mem_univ _) r0 (mem_univ _))
  have hcard := card_eq_sum_card_fiberwise hmaps
  have hpiece : ∀ i ∈ range (M + 1),
      ((((univ : Finset (Fin R)).filter (fun r => j r = i)).card : ℕ) : ℝ) ≤ C₂ * A := by
    intro i _
    apply hHP _ T₀ hT₀pos.le _ hc0
    intro r hr q hq
    simp only [mem_filter, mem_univ, true_and, j] at hr hq
    have hxr := hmin r (mem_univ _)
    have hxq := hmin q (mem_univ _)
    set xr := ((s r).im - (s r0).im) / T₀ with hxr'
    set xq := ((s q).im - (s r0).im) / T₀ with hxq'
    have a1 : (⌊xr⌋₊ : ℝ) ≤ xr := Nat.floor_le (div_nonneg (sub_nonneg.2 hxr) hT₀pos.le)
    have a2 : xr < ⌊xr⌋₊ + 1 := Nat.lt_floor_add_one xr
    have a3 : (⌊xq⌋₊ : ℝ) ≤ xq := Nat.floor_le (div_nonneg (sub_nonneg.2 hxq) hT₀pos.le)
    have a4 : xq < ⌊xq⌋₊ + 1 := Nat.lt_floor_add_one xq
    have er : (⌊xr⌋₊ : ℝ) = i := by exact_mod_cast hr
    have eq' : (⌊xq⌋₊ : ℝ) = i := by exact_mod_cast hq
    have dr : xr * T₀ = (s r).im - (s r0).im := div_mul_cancel₀ _ hT₀pos.ne'
    have dq : xq * T₀ = (s q).im - (s r0).im := div_mul_cancel₀ _ hT₀pos.ne'
    have hlt1 : xr - xq ≤ 1 := by linarith
    have hgt1 : -1 ≤ xr - xq := by linarith
    have b1 := mul_le_mul_of_nonneg_right hlt1 hT₀pos.le
    have b2 := mul_le_mul_of_nonneg_right hgt1 hT₀pos.le
    rw [abs_le]; constructor <;> linarith
  have hsum : (R : ℝ) ≤ (M + 1) * (C₂ * A) := by
    have : (R : ℝ) = ∑ i ∈ range (M + 1),
        ((((univ : Finset (Fin R)).filter (fun r => j r = i)).card : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, ← hcard]; simp
    rw [this]
    calc _ ≤ ∑ i ∈ range (M + 1), C₂ * A := sum_le_sum hpiece
      _ = _ := by simp
  have hMle : (M : ℝ) ≤ T / T₀ := Nat.floor_le (by positivity)
  have hTA : T / T₀ * (C₂ * A) = 4 * C₁ ^ 2 * C₂ * (W * ℓ ^ 2) := by
    simp only [hT₀, hu, hA, hW]; field_simp; ring
  have hℓ2 : ℓ ^ 2 ≤ 4 * lNT ^ 2 := by
    have := pow_le_pow_left₀ hℓ.le hℓT 2
    linarith [show (2 * lNT) ^ 2 = 4 * lNT ^ 2 by ring]
  have f1 : (M + 1) * (C₂ * A) ≤ (T / T₀ + 1) * (C₂ * A) :=
    mul_le_mul_of_nonneg_right (by linarith) hX0
  have f2 : 4 * C₁ ^ 2 * C₂ * (W * ℓ ^ 2) ≤ 16 * C₁ ^ 2 * C₂ * (W * lNT ^ 2) := by
    have := mul_le_mul_of_nonneg_left hℓ2 (by positivity : 0 ≤ 4 * C₁ ^ 2 * C₂ * W)
    linarith
  linarith

end
end GuthMaynard.CitedLV.PartH
end

section
open Finset Complex
namespace GuthMaynard.CitedLV
noncomputable section
alias card_le_of_large_values_huxley := GuthMaynard.CitedLV.PartH.card_le_of_large_values_huxley

end
end GuthMaynard.CitedLV
end


theorem solution :
    ∃ C : ℝ, ∀ (N : ℕ), 1 ≤ N → ∀ T : ℝ, 2 ≤ T → ∀ (a : ℕ → ℂ) (V : ℝ), 0 < V →
      ∀ (R : ℕ) (s : Fin R → ℂ), (∀ r, 0 ≤ (s r).re ∧ (s r).re ≤ 1 / 4) →
      (∀ r q, r ≠ q → 1 ≤ |(s r).im - (s q).im| ∧ |(s r).im - (s q).im| ≤ T) →
      (∀ r, V ≤ ‖∑ m ∈ Finset.Icc 1 N, a m * (m : ℂ) ^ (-s r)‖) →
      (R : ℝ) ≤ C * ((∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) * N / V ^ 2 +
        (∑ m ∈ Finset.Icc 1 N, ‖a m‖ ^ 2) ^ 3 * N * T / V ^ 6 * Real.log (N * T) ^ 2) :=
  GuthMaynard.CitedLV.card_le_of_large_values_huxley
