-- Prove2me | solution 1 for GuthMaynard.norm_dyadic_sum_cpow_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:20:44.309194+00:00
-- url     : https://prove2.me/submissions/c4d26747-c177-48f2-a735-e523795ab455

import Mathlib
import Definitions.Def_GuthMaynard
section
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

open Finset Complex

namespace GuthMaynard.CitedLV

noncomputable section

/-! ## Part V: van der Corput partial sums -/

/-! ## Part B: sum versus integral on a block with slowly varying phase -/

/-! ## Part K: the kernel bound -/

/-! ## Part H: Halász–Montgomery and subdivision -/

end

end GuthMaynard.CitedLV
end

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

open Finset Complex

namespace GuthMaynard.CitedLV.PartV

open OAI.Problem337.ExponentialSum

noncomputable section

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
/-!
# Part B: sum versus integral on a block with slowly varying phase

* `partial_le`: Kusmin–Landau gives `|∑_{a ≤ n < d} n^{-it}| ≤ 8π a/|t|` for `10|t| ≤ a`, `d ≤ 2a`.
* `unweighted`: `|∑_{a ≤ n < d} n^{-it} - ∫_a^d x^{-it} dx| ≤ 16π`, via
  `∑ - ∫ = ∫_0^1 ∑_n (z(n) - z(n+u)) du` and Abel summation against `1 - ((n+u)/n)^{-it}`.
* `weighted`: for a real weight `h` with `|h| ≤ 1` and `|h(y) - h(x)| ≤ 2/a` for `|y - x| ≤ 1`,
  Abel summation against the unweighted errors gives `≤ 48π + 2`.
-/

open Finset Complex

namespace GuthMaynard.CitedLV.PartB

open OAI.Problem337.ExponentialSum

noncomputable section

/-- `x^{-it}` written through the real logarithm. -/
def zt (t x : ℝ) : ℂ := Complex.exp (((-(t * Real.log x) : ℝ) : ℂ) * I)

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

/-! ## Abel summation -/

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

/-! ## The unweighted estimate -/

/-! ## The weighted estimate -/

/-! ## The concrete weight -/

end

end GuthMaynard.CitedLV.PartB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-!
# Blueprint: Heath-Brown's large values estimate (Guth–Maynard Theorem 1.6)

Route: B. Kerr, arXiv:1909.12075, §§5–6 (Theorem 16 with `γ` the indicator of a well-spaced set), with
every double sum taken over *all* pairs (the set lies in an interval of length `T`), which makes the
majorant principle exact and removes the Fourier kernels.

`S A N = ∑_{x,y ∈ A} |∑_{N ≤ n ≤ 2N} n^{-1/2} n^{i(x-y)}|²`.

* `majorant`, `completion` (Kerr Lemmas 18, 19);
* `card_divisors_le`, `mono` (Kerr Lemma 20 / Corollary 21: `S(N) ≪ M^ε S(M)` for `M ≥ 64N`),
  `square` (Lemma 22);
* `dyadic_pointwise` (`|∑_{N≤n≤2N} n^{iu}| ≪ N/|u| + |u|^{1/2} log(|u|+2)`), `bprocess` (Kerr Lemma 26,
  van der Corput's B-process: the deep input), `mvt_bound`;
* `dual` (Kerr Lemma 24, 27, Corollary 28), `thm16`, `heath_brown_large_values`.
-/

/-! ## Part M -/

/-! ## Part C -/

/-! ## Part Q -/

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartP
noncomputable section
/-!
# Part P: `|∑_{N ≤ n ≤ 2N} n^{iu}| ≪ N/|u| + |u|^{1/2} log(|u|+2)`

From the Huxley parts: `PartV.partial_sum_cpow_le` (short partial sums, van der Corput) and
`PartB.partial_le` (Kusmin–Landau on a block `[a, d)` with `10|t| ≤ a`, `d ≤ 2a`).
-/
lemma cpow_flip (u : ℝ) (n : ℕ) :
    (n : ℂ) ^ ((u : ℂ) * I) = (n : ℂ) ^ (-(((-u : ℝ) : ℂ) * I)) := by
  congr 1; push_cast; ring

lemma one_le_V (u : ℝ) (hu : 1 ≤ |u|) : 1 ≤ |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2) := by
  have h1 : 1 ≤ |u| ^ (1 / 2 : ℝ) := Real.one_le_rpow hu (by norm_num)
  have h2 : 1 ≤ Real.log (|u| + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  nlinarith

lemma prefix_le : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 ≤ |u| → ∀ c : ℕ, (c : ℝ) ≤ 11 * |u| + 2 →
    ‖∑ n ∈ Finset.Icc 1 c, (n : ℂ) ^ ((u : ℂ) * I)‖ ≤
      C * (|u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)) := by
  obtain ⟨C, hC, h⟩ := GuthMaynard.CitedLV.PartV.partial_sum_cpow_le
  refine ⟨C, hC, fun u hu c hc => ?_⟩
  have hu' : 1 ≤ |-u| := by rwa [abs_neg]
  have := h (-u) hu' c (by rwa [abs_neg])
  rw [abs_neg] at this
  simpa only [cpow_flip u] using this

lemma block_le (u : ℝ) (hu : 1 ≤ |u|) (a d : ℕ) (ha : 10 * |u| ≤ a) (hd : d ≤ 2 * a) :
    ‖∑ n ∈ Finset.Ico a d, (n : ℂ) ^ ((u : ℂ) * I)‖ ≤ 8 * Real.pi * a / |u| := by
  have hu' : 1 ≤ |-u| := by rwa [abs_neg]
  have := GuthMaynard.CitedLV.PartB.partial_le (-u) hu' a d (by rwa [abs_neg]) hd
  rw [abs_neg] at this
  convert this using 2
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by
    have : a ≤ n := (Finset.mem_Ico.mp hn).1
    have : (a : ℝ) ≤ n := by exact_mod_cast this
    linarith
  rw [← GuthMaynard.CitedLV.PartB.cpow_eq_zt (-u) n hn0, cpow_flip u n]
  simp

lemma Icc_split (f : ℕ → ℂ) (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M + 1) :
    ∑ n ∈ Finset.Icc N M, f n = ∑ n ∈ Finset.Icc 1 M, f n - ∑ n ∈ Finset.Icc 1 (N - 1), f n := by
  have e1 : Finset.Icc 1 M = Finset.Ioc 0 M := by ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have e2 : Finset.Icc 1 (N - 1) = Finset.Ioc 0 (N - 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have e3 : Finset.Icc N M = Finset.Ioc (N - 1) M := by ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e1, e2, e3, ← Finset.sum_Ioc_consecutive f (Nat.zero_le (N - 1)) (by omega)]
  ring

theorem dyadic_pointwise : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ u : ℝ, 1 ≤ |u| →
    ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((u : ℂ) * I)‖ ≤
      C * (N / |u| + |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)) := by
  obtain ⟨C1, hC1, h1⟩ := prefix_le
  refine ⟨2 * C1 + 300, by positivity, fun N hN u hu => ?_⟩
  set V := |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2) with hV
  have hV1 : 1 ≤ V := one_le_V u hu
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hu0 : 0 < |u| := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNu : 0 ≤ (N : ℝ) / |u| := by positivity
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ ((u : ℂ) * I) with hf
  have hlast : ‖f (2 * N)‖ ≤ 1 := by
    simp only [hf]
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  -- difference of two prefixes, both short
  have short : ∀ M : ℕ, N ≤ M + 1 → (M : ℝ) ≤ 11 * |u| + 2 →
      ‖∑ n ∈ Finset.Icc N M, f n‖ ≤ 2 * C1 * V := by
    intro M hM hMu
    rw [Icc_split f N M hN hM]
    have hN1 : ((N - 1 : ℕ) : ℝ) ≤ 11 * |u| + 2 := by
      have : N - 1 ≤ M := by omega
      have : ((N - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast this
      linarith
    calc _ ≤ ‖∑ n ∈ Finset.Icc 1 M, f n‖ + ‖∑ n ∈ Finset.Icc 1 (N - 1), f n‖ := norm_sub_le _ _
      _ ≤ C1 * V + C1 * V := add_le_add (h1 u hu M hMu) (h1 u hu (N - 1) hN1)
      _ = 2 * C1 * V := by ring
  -- Icc N (2N) = Ico N (2N) ∪ {2N}
  have hsplit : ∀ b : ℕ, N ≤ b → b ≤ 2 * N →
      ∑ n ∈ Finset.Icc N (2 * N), f n =
        ∑ n ∈ Finset.Icc N (b - 1), f n + ∑ n ∈ Finset.Ico b (2 * N), f n + f (2 * N) := by
    intro b hb1 hb2
    have e : Finset.Icc N (2 * N) = Finset.Ico N (2 * N + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_succ_top (by omega), ← Finset.sum_Ico_consecutive f hb1 hb2]
    have e2 : Finset.Icc N (b - 1) = Finset.Ico N b := by
      ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e2]
  by_cases hA : (2 * N : ℝ) ≤ 11 * |u| + 2
  · have := short (2 * N) (by omega) (by push_cast; linarith)
    calc _ ≤ 2 * C1 * V := this
      _ ≤ (2 * C1 + 300) * (N / |u| + V) := by nlinarith
  rw [not_le] at hA
  by_cases hB : 10 * |u| ≤ N
  · rw [hsplit N le_rfl (by omega)]
    have e : Finset.Icc N (N - 1) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [e, Finset.sum_empty, zero_add]
    have hb := block_le u hu N (2 * N) hB le_rfl
    calc _ ≤ ‖∑ n ∈ Finset.Ico N (2 * N), f n‖ + ‖f (2 * N)‖ := norm_add_le _ _
      _ ≤ 8 * Real.pi * N / |u| + 1 := add_le_add hb hlast
      _ ≤ (2 * C1 + 300) * (N / |u| + V) := by
        rw [mul_div_assoc]; nlinarith
  rw [not_le] at hB
  -- split at b = ⌈10|u|⌉
  set b := ⌈10 * |u|⌉₊ with hbdef
  have hb1 : 10 * |u| ≤ b := Nat.le_ceil _
  have hb2 : (b : ℝ) < 10 * |u| + 1 := Nat.ceil_lt_add_one (by positivity)
  have hNb : N ≤ b := by
    have : (N : ℝ) ≤ b := by linarith
    exact_mod_cast this
  have hb2N : b ≤ 2 * N := by
    have : (b : ℝ) ≤ 2 * N := by linarith
    exact_mod_cast this
  rw [hsplit b hNb hb2N]
  have hs := short (b - 1) (by omega) (by
    have : ((b - 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b 1
    linarith)
  have hk := block_le u hu b (2 * N) hb1 (by omega)
  have hk' : 8 * Real.pi * b / |u| ≤ 88 * Real.pi := by
    rw [div_le_iff₀ hu0]; nlinarith
  calc _ ≤ ‖∑ n ∈ Finset.Icc N (b - 1), f n + ∑ n ∈ Finset.Ico b (2 * N), f n‖ + ‖f (2 * N)‖ :=
        norm_add_le _ _
    _ ≤ ‖∑ n ∈ Finset.Icc N (b - 1), f n‖ + ‖∑ n ∈ Finset.Ico b (2 * N), f n‖ + ‖f (2 * N)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ 2 * C1 * V + 88 * Real.pi + 1 := by gcongr; exact hk.trans hk'
    _ ≤ (2 * C1 + 300) * (N / |u| + V) := by nlinarith

end
end GuthMaynard.CitedLV.HB.PartP
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Part P -/
alias dyadic_pointwise := GuthMaynard.CitedLV.HB.PartP.dyadic_pointwise

/-! ## Part D -/

/-! ## Part T -/

end
end GuthMaynard.CitedLV.HB
end


open GuthMaynard in
theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ u : ℝ, 1 ≤ |u| →
    ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
      C * (N / |u| + |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)) :=
  GuthMaynard.CitedLV.HB.dyadic_pointwise
