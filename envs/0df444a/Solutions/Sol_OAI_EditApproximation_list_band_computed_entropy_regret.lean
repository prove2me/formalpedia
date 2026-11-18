-- Prove2me | solution 1 for OAI.EditApproximation.list_band_computed_entropy_regret
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:55.889919+00:00
-- url     : https://prove2.me/submissions/74bce254-ac29-45d1-af12-1570e3a1ff13

import Mathlib
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Regret
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Clipped Bellman regret for edit-distance refinement

The deterministic bound of Lemma `lem:generic-regret` in
Section 7 of *An Almost-Linear Approximation Scheme for Edit Distance*
(manuscript of September 24, 2026) applies to an arbitrary finite set of
children satisfying the Bellman inequality and exact-cost connection
inequality.
-/

namespace EditApproximation

open Finset

/-- Scalar exponential estimate used in Lemma `lem:entropy`, Equation
`eq:entropy-exponential`. -/
theorem entropy_exponential_bound (κ x : ℝ)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hx : 0 ≤ x) (hxκ : x ≤ κ) :
    Real.exp ((1 - 2 * κ) * x) ≤ 1 + (1 - κ) * x := by
  have h1κ : 0 ≤ 1 - κ := by linarith
  have h1κle : 1 - κ ≤ 1 := by linarith
  have h2κ : 0 ≤ 1 - 2 * κ := by linarith
  have h2κle : 1 - 2 * κ ≤ 1 := by linarith
  have hy : 0 ≤ (1 - κ) * x := mul_nonneg h1κ hx
  have hypos : 0 < 1 + (1 - κ) * x := by linarith
  apply (Real.le_log_iff_exp_le hypos).mp
  have hlog := Real.le_log_one_add_of_nonneg hy
  apply le_trans _ hlog
  apply (le_div_iff₀ (show 0 < (1 - κ) * x + 2 by linarith)).mpr
  have hproduct : (1 - 2 * κ) * (1 - κ) ≤ 1 :=
    (mul_le_mul_of_nonneg_right h2κle h1κ).trans (by simpa using h1κle)
  have hprodκ : (1 - 2 * κ) * (1 - κ) * x ≤ κ :=
    (mul_le_mul_of_nonneg_right hproduct hx).trans (by simpa using hxκ)
  have hfinal : 0 ≤ x * (κ - (1 - 2 * κ) * (1 - κ) * x) :=
    mul_nonneg hx (sub_nonneg.mpr hprodκ)
  have hkx : 0 ≤ κ * x := mul_nonneg hκ hx
  nlinarith

/-- The final telescoping step of Lemma `lem:entropy`. Here `played t`
is the inner product with the chosen distribution, `comparator t` is
the comparator inner product, and `decrement t` is its normalized
decrement. The potential-increment and variational bounds are explicit
internal proof obligations; this theorem does not assume a published
online-learning guarantee. -/
theorem entropy_potential_telescoping (S : ℕ) (η κ bound : ℝ)
    (potential played comparator decrement : ℕ → ℝ)
    (hη : 0 < η) (hκ : 0 ≤ κ)
    (hincrement : ∀ t < S,
      potential (t + 1) - potential t ≤ η * played t)
    (hstart : potential 0 ≤ bound)
    (hcomparator : η * ((∑ t ∈ range S, comparator t) -
        2 * κ * ∑ t ∈ range S, decrement t) ≤ potential S)
    (hdecrement : ∑ t ∈ range S, decrement t ≤ 1) :
    (∑ t ∈ range S, comparator t) - bound / η - 2 * κ ≤
      ∑ t ∈ range S, played t := by
  have htel : ∑ t ∈ range S, (potential (t + 1) - potential t) =
      potential S - potential 0 := by
    clear hincrement hcomparator hdecrement
    induction S with
    | zero => simp
    | succ S ih =>
      rw [sum_range_succ, ih]
      ring
  have hsum : potential S - potential 0 ≤ η * ∑ t ∈ range S, played t := by
    rw [← htel, mul_sum]
    exact sum_le_sum fun t ht => hincrement t (mem_range.mp ht)
  have hdecrement' : η * (2 * κ * ∑ t ∈ range S, decrement t) ≤ η * (2 * κ) := by
    calc
      _ ≤ η * (2 * κ * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdecrement (by positivity)) hη.le
      _ = _ := by ring
  have hcancel : η * (bound / η) = bound := mul_div_cancel₀ bound hη.ne'
  apply le_of_mul_le_mul_left (a := η) _ hη
  nlinarith

/-- Nonnegativity of relative entropy for a finite probability vector and
a strictly positive reference vector. Zero coordinates of the first
vector are allowed and contribute zero. -/
theorem finite_relative_entropy_nonnegative {ι : Type*} (coordinates : Finset ι)
    (p q : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hq : ∀ i ∈ coordinates, 0 < q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1) :
    0 ≤ ∑ i ∈ coordinates, p i * Real.log (p i / q i) := by
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      p i * Real.log (q i / p i) ≤ q i - p i := by
    by_cases hzero : p i = 0
    · simpa [hzero] using (hq i hi).le
    · have hp' : 0 < p i := lt_of_le_of_ne (hp i hi) (Ne.symm hzero)
      have hl := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos (hq i hi) hp')) hp'.le
      have hcancel : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      rwa [hcancel] at hl
  have hsum : ∑ i ∈ coordinates, p i * Real.log (q i / p i) ≤ 0 := by
    calc
      _ ≤ ∑ i ∈ coordinates, (q i - p i) := sum_le_sum hcoord
      _ = 0 := by rw [sum_sub_distrib, hqsum, hpsum]; ring
  have hneg (i : ι) (hi : i ∈ coordinates) :
      p i * Real.log (p i / q i) = -(p i * Real.log (q i / p i)) := by
    by_cases hzero : p i = 0
    · simp [hzero]
    · rw [Real.log_div hzero (hq i hi).ne', Real.log_div (hq i hi).ne' hzero]
      ring
  calc
    0 ≤ -(∑ i ∈ coordinates, p i * Real.log (q i / p i)) := neg_nonneg.mpr hsum
    _ = ∑ i ∈ coordinates, p i * Real.log (p i / q i) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun i hi => (hneg i hi).symm

/-- The finite Gibbs variational bound used when the innovation
supremum over the actual action hull is extended to the simplex.
This is a proved inequality, with no maximization-oracle assumption. -/
theorem finite_gibbs_variational_bound {ι : Type*} (coordinates : Finset ι)
    (p q gain : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hq : ∀ i ∈ coordinates, 0 < q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1) :
    (∑ i ∈ coordinates, p i * gain i) -
        (∑ i ∈ coordinates, p i * Real.log (p i / q i)) ≤
      Real.log (∑ i ∈ coordinates, q i * Real.exp (gain i)) := by
  let Z := ∑ i ∈ coordinates, q i * Real.exp (gain i)
  have hs : coordinates.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    simp [he] at hqsum
  have hZ : 0 < Z := sum_pos (fun i hi => mul_pos (hq i hi) (Real.exp_pos _)) hs
  let r : ι → ℝ := fun i => q i * Real.exp (gain i) / Z
  have hr (i : ι) (hi : i ∈ coordinates) : 0 < r i :=
    div_pos (mul_pos (hq i hi) (Real.exp_pos _)) hZ
  have hrsum : ∑ i ∈ coordinates, r i = 1 := by
    simp only [r]
    rw [← sum_div]
    change Z / Z = 1
    exact div_self hZ.ne'
  have hKL := finite_relative_entropy_nonnegative coordinates p r hp hr hpsum hrsum
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      p i * gain i - p i * Real.log (p i / q i) =
        p i * Real.log Z - p i * Real.log (p i / r i) := by
    by_cases hzero : p i = 0
    · simp [hzero]
    · have hlogr : Real.log (r i) = Real.log (q i) + gain i - Real.log Z := by
        change Real.log (q i * Real.exp (gain i) / Z) = _
        rw [Real.log_div (mul_pos (hq i hi) (Real.exp_pos _)).ne' hZ.ne',
          Real.log_mul (hq i hi).ne' (Real.exp_pos _).ne', Real.log_exp]
      rw [Real.log_div hzero (hq i hi).ne', Real.log_div hzero (hr i hi).ne', hlogr]
      ring
  have hidentity :
      (∑ i ∈ coordinates, p i * gain i) -
          (∑ i ∈ coordinates, p i * Real.log (p i / q i)) =
        Real.log Z - ∑ i ∈ coordinates, p i * Real.log (p i / r i) := by
    rw [← sum_sub_distrib]
    calc
      _ = ∑ i ∈ coordinates,
          (p i * Real.log Z - p i * Real.log (p i / r i)) := sum_congr rfl hcoord
      _ = _ := by rw [sum_sub_distrib, ← sum_mul, hpsum, one_mul]
  change _ ≤ Real.log Z
  rw [hidentity]
  exact sub_le_self _ hKL

/-- The small-decrement logarithmic moment bound in the entropy
innovation argument. The bound on `η * innovation i` is the only
smallness requirement needed here. -/
theorem entropy_small_increment_logsum {ι : Type*} (coordinates : Finset ι)
    (p innovation : ι → ℝ) (η κ : ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hinnovation : ∀ i ∈ coordinates, 0 ≤ η * innovation i)
    (hsmall : ∀ i ∈ coordinates, η * innovation i ≤ κ) :
    Real.log (∑ i ∈ coordinates,
        p i * Real.exp (η * (1 - 2 * κ) * innovation i)) ≤
      η * (1 - κ) * ∑ i ∈ coordinates, p i * innovation i := by
  let Z := ∑ i ∈ coordinates, p i * Real.exp (η * (1 - 2 * κ) * innovation i)
  have hs : coordinates.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    simp [he] at hpsum
  have hZ : 0 < Z := sum_pos (fun i hi => mul_pos (hp i hi) (Real.exp_pos _)) hs
  have hbound : Z ≤ 1 + η * (1 - κ) * ∑ i ∈ coordinates, p i * innovation i := by
    calc
      _ ≤ ∑ i ∈ coordinates, p i * (1 + (1 - κ) * (η * innovation i)) := by
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (hp i hi).le
        rw [show η * (1 - 2 * κ) * innovation i =
          (1 - 2 * κ) * (η * innovation i) by ring]
        exact entropy_exponential_bound κ (η * innovation i) hκ hκhalf
          (hinnovation i hi) (hsmall i hi)
      _ = _ := by
        simp_rw [mul_add, mul_one]
        rw [sum_add_distrib, hpsum]
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        ring
  exact (Real.log_le_sub_one_of_pos hZ).trans (by linarith)

/-- Equal probability mass in every child block makes every blockwise
constant vector have the same inner product with the two distributions. -/
theorem fixed_block_mass_inner_product {ι β : Type*} [Fintype β] [DecidableEq β]
    (coordinates : Finset ι) (block : ι → β) (p q : ι → ℝ) (baseline : β → ℝ)
    (hblock : ∀ b, (∑ i ∈ coordinates with block i = b, p i) =
      ∑ i ∈ coordinates with block i = b, q i) :
    (∑ i ∈ coordinates, p i * baseline (block i)) =
      ∑ i ∈ coordinates, q i * baseline (block i) := by
  classical
  have hdecompose (r : ι → ℝ) :
      (∑ b : β, baseline b * ∑ i ∈ coordinates with block i = b, r i) =
        ∑ i ∈ coordinates, r i * baseline (block i) := by
    simp only [mul_sum, sum_filter, mul_ite, mul_zero]
    rw [sum_comm]
    simp [mul_comm]
  rw [← hdecompose p, ← hdecompose q]
  exact sum_congr rfl fun b _ => congrArg (baseline b * ·) (hblock b)

/-- The innovation variational inequality for the actual action hull.
Its fixed block masses are used exactly through `hfixedMass`: the
blockwise minimum vector `baseline` has the same inner product with
every feasible vector. The residual `innovation` has small range.

Combined with the entropy penalty at a positive maximizer, this bounds
the potential increment without replacing the action hull by a simplex
in the algorithm. -/
theorem entropy_innovation_variational_bound {ι : Type*} (coordinates : Finset ι)
    (p q decrement baseline innovation : ι → ℝ) (η κ : ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hq : ∀ i ∈ coordinates, 0 ≤ q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1)
    (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hbaseline : ∀ i ∈ coordinates, 0 ≤ baseline i)
    (hdecomposition : ∀ i ∈ coordinates, decrement i = baseline i + innovation i)
    (hfixedMass : (∑ i ∈ coordinates, q i * baseline i) =
      ∑ i ∈ coordinates, p i * baseline i)
    (hinnovation : ∀ i ∈ coordinates, 0 ≤ η * innovation i)
    (hsmall : ∀ i ∈ coordinates, η * innovation i ≤ κ) :
    η * (1 - 2 * κ) * (∑ i ∈ coordinates, q i * decrement i) -
        (∑ i ∈ coordinates, q i * Real.log (q i / p i)) ≤
      η * (1 - κ) * ∑ i ∈ coordinates, p i * decrement i := by
  have hgibbs := finite_gibbs_variational_bound coordinates q p
    (fun i => η * (1 - 2 * κ) * innovation i) hq hp hqsum hpsum
  have hlog := entropy_small_increment_logsum coordinates p innovation η κ
    hp hpsum hκ hκhalf hinnovation hsmall
  have hgain : (∑ i ∈ coordinates, q i * (η * (1 - 2 * κ) * innovation i)) =
      η * (1 - 2 * κ) * ∑ i ∈ coordinates, q i * innovation i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hgain] at hgibbs
  have hresidual := hgibbs.trans hlog
  have hpsumDecrement : (∑ i ∈ coordinates, p i * decrement i) =
      (∑ i ∈ coordinates, p i * baseline i) +
        ∑ i ∈ coordinates, p i * innovation i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [hdecomposition i hi, mul_add]
  have hqsumDecrement : (∑ i ∈ coordinates, q i * decrement i) =
      (∑ i ∈ coordinates, p i * baseline i) +
        ∑ i ∈ coordinates, q i * innovation i := by
    rw [← hfixedMass, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [hdecomposition i hi, mul_add]
  have hmass : 0 ≤ ∑ i ∈ coordinates, p i * baseline i :=
    sum_nonneg fun i hi => mul_nonneg (hp i hi).le (hbaseline i hi)
  have hcorrection : 0 ≤ η * κ * ∑ i ∈ coordinates, p i * baseline i :=
    mul_nonneg (mul_nonneg hη hκ) hmass
  rw [hpsumDecrement, hqsumDecrement]
  nlinarith

/-- First-order optimality of entropy plus a linear objective along a
feasible segment. The segment-maximization hypothesis is exactly what
an entropy maximizer on a convex action hull supplies. -/
theorem entropy_first_order_on_segment {ι : Type*} (coordinates : Finset ι)
    (p q objective : ι → ℝ) (η : ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hmax : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∑ i ∈ coordinates,
        (Real.negMulLog (p i + t * (q i - p i)) +
          η * objective i * (p i + t * (q i - p i)))) ≤
      ∑ i ∈ coordinates, (Real.negMulLog (p i) + η * objective i * p i)) :
    ∑ i ∈ coordinates,
      (-Real.log (p i) - 1 + η * objective i) * (q i - p i) ≤ 0 := by
  let f : ℝ → ℝ := fun t => ∑ i ∈ coordinates,
    (Real.negMulLog (p i + t * (q i - p i)) +
      η * objective i * (p i + t * (q i - p i)))
  have hd : HasDerivAt f (∑ i ∈ coordinates,
      (-Real.log (p i) - 1 + η * objective i) * (q i - p i)) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hline : HasDerivAt (fun t : ℝ => p i + t * (q i - p i)) (q i - p i) 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) (p i)).fun_add
        ((hasDerivAt_id (0 : ℝ)).mul_const (q i - p i))
    have hneg : HasDerivAt Real.negMulLog (-Real.log (p i) - 1)
        (p i + 0 * (q i - p i)) := by
      simpa using Real.hasDerivAt_negMulLog (hp i hi).ne'
    have hent := hneg.comp 0 hline
    have hent' : HasDerivAt (fun t : ℝ => Real.negMulLog (p i + t * (q i - p i)))
        ((-Real.log (p i) - 1) * (q i - p i)) 0 := by
      convert! hent using 1
      all_goals try with_reducible_and_instances rfl
    convert hent'.add (hline.const_mul (η * objective i)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hmaxOn : IsMaxOn f (Set.Icc (0 : ℝ) 1) 0 := by
    intro t ht
    simpa [f] using hmax t ht.1 ht.2
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    have hsegment : segment ℝ (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [segment_eq_Icc (by norm_num)]
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hnonpos := hmaxOn.localize.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  simpa using hnonpos

/-- The exact relative-entropy penalty at a positive first-order
maximizer. This proves manuscript Equation `eq:entropy-penalty` once
the first-order condition is supplied by
`entropy_first_order_on_segment`. -/
theorem entropy_penalty_of_first_order {ι : Type*} (coordinates : Finset ι)
    (p q objective : ι → ℝ) (η : ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1)
    (hfirst : ∑ i ∈ coordinates,
      (-Real.log (p i) - 1 + η * objective i) * (q i - p i) ≤ 0) :
    (∑ i ∈ coordinates, Real.negMulLog (q i)) +
        η * (∑ i ∈ coordinates, objective i * q i) ≤
      (∑ i ∈ coordinates, Real.negMulLog (p i)) +
        η * (∑ i ∈ coordinates, objective i * p i) -
        (∑ i ∈ coordinates, q i * Real.log (q i / p i)) := by
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      Real.negMulLog (q i) - Real.negMulLog (p i) +
          η * objective i * (q i - p i) + q i * Real.log (q i / p i) =
        (-Real.log (p i) - 1 + η * objective i) * (q i - p i) + (q i - p i) := by
    by_cases hqzero : q i = 0
    · simp only [hqzero, Real.negMulLog, zero_mul, zero_div]
      ring
    · rw [Real.log_div hqzero (hp i hi).ne']
      simp only [Real.negMulLog]
      ring
  have hidentity :
      (∑ i ∈ coordinates,
        (Real.negMulLog (q i) - Real.negMulLog (p i) +
          η * objective i * (q i - p i) + q i * Real.log (q i / p i))) =
        ∑ i ∈ coordinates,
          (-Real.log (p i) - 1 + η * objective i) * (q i - p i) := by
    calc
      _ = ∑ i ∈ coordinates,
          ((-Real.log (p i) - 1 + η * objective i) * (q i - p i) + (q i - p i)) :=
        sum_congr rfl hcoord
      _ = _ := by rw [sum_add_distrib, sum_sub_distrib, hqsum, hpsum]; ring
  have hbound := hidentity.trans_le hfirst
  simp only [sum_add_distrib, sum_sub_distrib, mul_sub] at hbound
  have hlinear : (∑ i ∈ coordinates, η * objective i * q i) =
      η * ∑ i ∈ coordinates, objective i * q i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  have hlinear' : (∑ i ∈ coordinates, η * objective i * p i) =
      η * ∑ i ∈ coordinates, objective i * p i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hlinear, hlinear'] at hbound
  linarith

/-- An entropy maximizer cannot have a zero coordinate when a strictly
positive feasible vector is available. Only maximization on the
segments to that vector is needed, so this applies to the actual finite
action hull in the manuscript. -/
theorem entropy_maximizer_positive {ι : Type*} (coordinates : Finset ι)
    (p witness objective : ι → ℝ) (η : ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hw : ∀ i ∈ coordinates, 0 < witness i)
    (hmax : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∑ i ∈ coordinates,
        (Real.negMulLog ((1 - t) * p i + t * witness i) +
          η * objective i * ((1 - t) * p i + t * witness i))) ≤
      ∑ i ∈ coordinates, (Real.negMulLog (p i) + η * objective i * p i)) :
    ∀ i ∈ coordinates, 0 < p i := by
  classical
  intro k hk
  by_contra hnot
  have hpk : p k = 0 := le_antisymm (le_of_not_gt hnot) (hp k hk)
  let value : ι → ℝ → ℝ := fun i x => Real.negMulLog x + η * objective i * x
  let A := (∑ i ∈ coordinates, value i (witness i)) -
    ∑ i ∈ coordinates, value i (p i)
  let t := Real.exp (-(|A| / witness k + 1))
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hratio : 0 ≤ |A| / witness k := div_nonneg (abs_nonneg _) (hw k hk).le
    linarith
  have htlog : Real.log t = -(|A| / witness k + 1) := Real.log_exp _
  have hpositive : 0 < t * A + witness k * Real.negMulLog t := by
    have hbracket : 0 < A + |A| + witness k := by
      have := neg_le_abs A
      linarith [hw k hk]
    calc
      _ = t * (A + |A| + witness k) := by
        rw [Real.negMulLog, htlog]
        field_simp [(hw k hk).ne']
        ring
      _ > 0 := mul_pos ht hbracket
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      (1 - t) * value i (p i) + t * value i (witness i) ≤
        value i ((1 - t) * p i + t * witness i) := by
    have hconcave := Real.concaveOn_negMulLog.2 (hp i hi) (hw i hi).le
      (show 0 ≤ 1 - t by linarith) ht.le (show (1 - t) + t = 1 by ring)
    simp only [smul_eq_mul] at hconcave
    dsimp only [value]
    nlinarith
  have hkexact :
      (1 - t) * value k (p k) + t * value k (witness k) +
          witness k * Real.negMulLog t =
        value k ((1 - t) * p k + t * witness k) := by
    simp only [hpk, value, mul_zero, Real.negMulLog_zero, zero_add, add_zero]
    rw [Real.negMulLog_mul]
    ring
  let lower : ι → ℝ := fun i => (1 - t) * value i (p i) + t * value i (witness i)
  let upper : ι → ℝ := fun i => value i ((1 - t) * p i + t * witness i)
  have hothers : ∑ i ∈ coordinates.erase k, lower i ≤
      ∑ i ∈ coordinates.erase k, upper i :=
    sum_le_sum fun i hi => hcoord i (mem_of_mem_erase hi)
  have hwhole : (∑ i ∈ coordinates.erase k, lower i) + lower k +
      witness k * Real.negMulLog t ≤ (∑ i ∈ coordinates.erase k, upper i) + upper k := by
    change lower k + witness k * Real.negMulLog t = upper k at hkexact
    linarith
  rw [sum_erase_add coordinates lower hk, sum_erase_add coordinates upper hk] at hwhole
  have hlower : (∑ i ∈ coordinates, lower i) =
      (1 - t) * (∑ i ∈ coordinates, value i (p i)) +
        t * ∑ i ∈ coordinates, value i (witness i) := by
    simp only [lower, sum_add_distrib, ← mul_sum]
  rw [hlower] at hwhole
  have hupper : ∑ i ∈ coordinates, upper i ≤ ∑ i ∈ coordinates, value i (p i) :=
    hmax t ht.le ht1
  have hfinal := hwhole.trans hupper
  dsimp only [A] at hpositive
  nlinarith

/-- Entropy is nonnegative on a finite probability vector. -/
theorem finite_entropy_nonnegative {ι : Type*} (coordinates : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1) :
    0 ≤ ∑ i ∈ coordinates, Real.negMulLog (p i) := by
  apply sum_nonneg
  intro i hi
  apply Real.negMulLog_nonneg (hp i hi)
  exact (single_le_sum hp hi).trans hpsum.le

/-- The entropy of a finite probability vector is at most the logarithm
of the number of listed coordinates. -/
theorem finite_entropy_le_log_card {ι : Type*} (coordinates : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1) :
    (∑ i ∈ coordinates, Real.negMulLog (p i)) ≤ Real.log coordinates.card := by
  have hs : coordinates.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    simp [he] at hpsum
  have hn : 0 < (coordinates.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
  let uniform : ι → ℝ := fun _ => 1 / coordinates.card
  have hu : ∀ i ∈ coordinates, 0 < uniform i := fun _ _ => div_pos zero_lt_one hn
  have husum : ∑ i ∈ coordinates, uniform i = 1 := by
    simp only [uniform, sum_const, nsmul_eq_mul]
    field_simp
  have hKL := finite_relative_entropy_nonnegative coordinates p uniform hp hu hpsum husum
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      p i * Real.log (p i / uniform i) =
        -Real.negMulLog (p i) + p i * Real.log coordinates.card := by
    by_cases hzero : p i = 0
    · simp [hzero]
    · rw [Real.log_div hzero (hu i hi).ne']
      simp only [uniform, one_div, Real.log_inv, Real.negMulLog]
      ring
  have hid : (∑ i ∈ coordinates, p i * Real.log (p i / uniform i)) =
      -(∑ i ∈ coordinates, Real.negMulLog (p i)) + Real.log coordinates.card := by
    calc
      _ = ∑ i ∈ coordinates, (-Real.negMulLog (p i) + p i * Real.log coordinates.card) :=
        sum_congr rfl hcoord
      _ = _ := by rw [sum_add_distrib, sum_neg_distrib, ← sum_mul, hpsum, one_mul]
  rw [hid] at hKL
  linarith

theorem entropyValue_eq {ι : Type*} (coordinates : Finset ι)
    (η : ℝ) (objective p : ι → ℝ) :
    entropyValue coordinates η objective p =
      (∑ i ∈ coordinates, Real.negMulLog (p i)) +
        η * ∑ i ∈ coordinates, objective i * p i := by
  unfold entropyValue
  rw [sum_add_distrib, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  ring

/-- The entropy potential is attained on every nonempty compact action
hull, since the zero-coordinate convention gives continuous entropy. -/
theorem exists_entropy_maximizer {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η : ℝ) (objective : ι → ℝ)
    (hcompact : IsCompact Q) (hne : Q.Nonempty) :
    ∃ p ∈ Q, IsMaxOn (entropyValue coordinates η objective) Q p := by
  apply hcompact.exists_isMaxOn hne
  unfold entropyValue
  fun_prop

/-- Positivity of the entropy maximizer on a convex feasible hull with
a positive feasible witness. -/
theorem entropy_hull_maximizer_positive {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η : ℝ) (objective p witness : ι → ℝ)
    (hconvex : Convex ℝ Q) (hpQ : p ∈ Q) (hwQ : witness ∈ Q)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hw : ∀ i ∈ coordinates, 0 < witness i)
    (hmax : IsMaxOn (entropyValue coordinates η objective) Q p) :
    ∀ i ∈ coordinates, 0 < p i := by
  apply entropy_maximizer_positive coordinates p witness objective η hp hw
  intro t ht ht1
  have hmem := hconvex hpQ hwQ (show 0 ≤ 1 - t by linarith) ht
    (show (1 - t) + t = 1 by ring)
  simpa [entropyValue, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hmax hmem

/-- The exact KL penalty holds for every competitor in the action hull,
including competitors with zero coordinates. -/
theorem entropy_hull_penalty {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η : ℝ) (objective p q : ι → ℝ)
    (hconvex : Convex ℝ Q) (hpQ : p ∈ Q) (hqQ : q ∈ Q)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1)
    (hmax : IsMaxOn (entropyValue coordinates η objective) Q p) :
    entropyValue coordinates η objective q ≤ entropyValue coordinates η objective p -
      ∑ i ∈ coordinates, q i * Real.log (q i / p i) := by
  have hfirst := entropy_first_order_on_segment coordinates p q objective η hp
    (by
      intro t ht ht1
      have hmem := hconvex hpQ hqQ (show 0 ≤ 1 - t by linarith) ht
        (show (1 - t) + t = 1 by ring)
      have heq : (1 - t) • p + t • q = fun i => p i + t * (q i - p i) := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [heq] at hmem
      exact hmax hmem)
  rw [entropyValue_eq, entropyValue_eq]
  exact entropy_penalty_of_first_order coordinates p q objective η hp hpsum hqsum hfirst

theorem entropyValue_add_scaled {ι : Type*} (coordinates : Finset ι)
    (η scale : ℝ) (objective increment p : ι → ℝ) :
    entropyValue coordinates η (fun i => objective i + scale * increment i) p =
      entropyValue coordinates η objective p +
        η * scale * ∑ i ∈ coordinates, increment i * p i := by
  rw [entropyValue_eq, entropyValue_eq]
  simp_rw [add_mul]
  rw [sum_add_distrib]
  have hsum : (∑ i ∈ coordinates, scale * increment i * p i) =
      scale * ∑ i ∈ coordinates, increment i * p i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

/-- One complete optimistic entropy-potential step on the actual hull.
The old objective and its predicted increment are arbitrary and may
have negative coordinates. Only the residual decrement is small. -/
theorem entropy_hull_potential_step {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η κ : ℝ)
    (old gain decrement baseline innovation oldLeader predicted newLeader : ι → ℝ)
    (hconvex : Convex ℝ Q)
    (hpredQ : predicted ∈ Q) (hnewQ : newLeader ∈ Q)
    (hpred : ∀ i ∈ coordinates, 0 < predicted i)
    (hnew : ∀ i ∈ coordinates, 0 ≤ newLeader i)
    (hpredsum : ∑ i ∈ coordinates, predicted i = 1)
    (hnewsum : ∑ i ∈ coordinates, newLeader i = 1)
    (holdMax : IsMaxOn (entropyValue coordinates η old) Q oldLeader)
    (hpredMax : IsMaxOn
      (entropyValue coordinates η (fun i => old i + gain i)) Q predicted)
    (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hbaseline : ∀ i ∈ coordinates, 0 ≤ baseline i)
    (hdecomposition : ∀ i ∈ coordinates, decrement i = baseline i + innovation i)
    (hfixedMass : (∑ i ∈ coordinates, newLeader i * baseline i) =
      ∑ i ∈ coordinates, predicted i * baseline i)
    (hinnovation : ∀ i ∈ coordinates, 0 ≤ η * innovation i)
    (hsmall : ∀ i ∈ coordinates, η * innovation i ≤ κ) :
    entropyValue coordinates η
        (fun i => old i + gain i + (1 - 2 * κ) * decrement i) newLeader -
        entropyValue coordinates η old oldLeader ≤
      η * ∑ i ∈ coordinates, (gain i + (1 - κ) * decrement i) * predicted i := by
  have hpenalty := entropy_hull_penalty coordinates Q η (fun i => old i + gain i)
    predicted newLeader hconvex hpredQ hnewQ hpred hpredsum hnewsum hpredMax
  have hinnovationBound := entropy_innovation_variational_bound coordinates predicted
    newLeader decrement baseline innovation η κ hpred hnew hpredsum hnewsum
    hη hκ hκhalf hbaseline hdecomposition hfixedMass hinnovation hsmall
  have hpredComm : (∑ i ∈ coordinates, predicted i * decrement i) =
      ∑ i ∈ coordinates, decrement i * predicted i :=
    sum_congr rfl fun i _ => mul_comm _ _
  have hnewComm : (∑ i ∈ coordinates, newLeader i * decrement i) =
      ∑ i ∈ coordinates, decrement i * newLeader i :=
    sum_congr rfl fun i _ => mul_comm _ _
  rw [hpredComm, hnewComm] at hinnovationBound
  have hnewValue := entropyValue_add_scaled coordinates η (1 - 2 * κ)
    (fun i => old i + gain i) decrement newLeader
  have hpredValue := entropyValue_add_scaled coordinates η 1 old gain predicted
  simp only [one_mul, mul_one] at hpredValue
  have holdBound := holdMax hpredQ
  change entropyValue coordinates η old predicted ≤
    entropyValue coordinates η old oldLeader at holdBound
  have hsum : (∑ i ∈ coordinates, (gain i + (1 - κ) * decrement i) * predicted i) =
      (∑ i ∈ coordinates, gain i * predicted i) +
        (1 - κ) * ∑ i ∈ coordinates, decrement i * predicted i := by
    simp_rw [add_mul]
    rw [sum_add_distrib]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  nlinarith

theorem optimisticHistory_succ {ι : Type*} (κ : ℝ)
    (gain decrement : ℕ → ι → ℝ) (t : ℕ) :
    optimisticHistory κ gain decrement (t + 1) =
      fun i => optimisticHistory κ gain decrement t i + gain t i +
        (1 - 2 * κ) * decrement t i := by
  ext i
  simp only [optimisticHistory, sum_range_succ]
  ring

theorem optimisticHistory_inner_product {ι : Type*} (coordinates : Finset ι)
    (κ : ℝ) (gain decrement : ℕ → ι → ℝ) (S : ℕ) (p : ι → ℝ) :
    (∑ i ∈ coordinates, optimisticHistory κ gain decrement S i * p i) =
      (∑ t ∈ range S, ∑ i ∈ coordinates, (gain t i + decrement t i) * p i) -
        2 * κ * ∑ t ∈ range S, ∑ i ∈ coordinates, decrement t i * p i := by
  simp only [optimisticHistory, sum_mul]
  rw [sum_comm, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t ht
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  ring

/-- Lemma `lem:entropy` for a finite compact convex action hull. The
fixed child-block masses enter through the equality of the baseline
inner products; `fixed_block_mass_inner_product` supplies that equality
from the individual block masses. The potential argument uses positivity and the relative-entropy penalty. -/
theorem finite_hull_entropy_regret {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (S : ℕ) (η κ : ℝ)
    (gain decrement baseline innovation predicted : ℕ → ι → ℝ)
    (witness comparator : ι → ℝ)
    (hcompact : IsCompact Q) (hconvex : Convex ℝ Q)
    (hwQ : witness ∈ Q) (hcQ : comparator ∈ Q)
    (hw : ∀ i ∈ coordinates, 0 < witness i)
    (hprob : ∀ p ∈ Q,
      (∀ i ∈ coordinates, 0 ≤ p i) ∧ (∑ i ∈ coordinates, p i = 1))
    (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hpredQ : ∀ t < S, predicted t ∈ Q)
    (hpredMax : ∀ t < S, IsMaxOn
      (entropyValue coordinates η
        (fun i => optimisticHistory κ gain decrement t i + gain t i)) Q (predicted t))
    (hbaseline : ∀ t < S, ∀ i ∈ coordinates, 0 ≤ baseline t i)
    (hdecomposition : ∀ t < S, ∀ i ∈ coordinates,
      decrement t i = baseline t i + innovation t i)
    (hfixedMass : ∀ t < S, ∀ p ∈ Q, ∀ q ∈ Q,
      (∑ i ∈ coordinates, p i * baseline t i) =
        ∑ i ∈ coordinates, q i * baseline t i)
    (hinnovation : ∀ t < S, ∀ i ∈ coordinates, 0 ≤ η * innovation t i)
    (hsmall : ∀ t < S, ∀ i ∈ coordinates, η * innovation t i ≤ κ)
    (hdecrement : ∀ i ∈ coordinates, ∑ t ∈ range S, decrement t i ≤ 1) :
    (∑ t ∈ range S, ∑ i ∈ coordinates, (gain t i + decrement t i) * comparator i) -
        Real.log coordinates.card / η - 2 * κ ≤
      ∑ t ∈ range S, ∑ i ∈ coordinates,
        (gain t i + (1 - κ) * decrement t i) * predicted t i := by
  classical
  have hex : ∀ t : ℕ, ∃ p ∈ Q,
      IsMaxOn (entropyValue coordinates η (optimisticHistory κ gain decrement t)) Q p :=
    fun t => exists_entropy_maximizer coordinates Q η
      (optimisticHistory κ gain decrement t) hcompact ⟨witness, hwQ⟩
  choose leader hleaderQ hleaderMax using hex
  let potential : ℕ → ℝ := fun t => entropyValue coordinates η
    (optimisticHistory κ gain decrement t) (leader t)
  have hpredPositive (t : ℕ) (ht : t < S) : ∀ i ∈ coordinates, 0 < predicted t i :=
    entropy_hull_maximizer_positive coordinates Q η
      (fun i => optimisticHistory κ gain decrement t i + gain t i)
      (predicted t) witness hconvex (hpredQ t ht) hwQ
      (hprob (predicted t) (hpredQ t ht)).1 hw (hpredMax t ht)
  have hincrement (t : ℕ) (ht : t < S) :
      potential (t + 1) - potential t ≤
        η * ∑ i ∈ coordinates, (gain t i + (1 - κ) * decrement t i) * predicted t i := by
    have hstep := entropy_hull_potential_step coordinates Q η κ
      (optimisticHistory κ gain decrement t) (gain t) (decrement t) (baseline t)
      (innovation t) (leader t) (predicted t) (leader (t + 1)) hconvex
      (hpredQ t ht) (hleaderQ (t + 1)) (hpredPositive t ht)
      (hprob (leader (t + 1)) (hleaderQ (t + 1))).1
      (hprob (predicted t) (hpredQ t ht)).2
      (hprob (leader (t + 1)) (hleaderQ (t + 1))).2
      (hleaderMax t) (hpredMax t ht) hη.le hκ hκhalf (hbaseline t ht)
      (hdecomposition t ht)
      (hfixedMass t ht (leader (t + 1)) (hleaderQ (t + 1)) (predicted t) (hpredQ t ht))
      (hinnovation t ht) (hsmall t ht)
    simpa only [potential, optimisticHistory_succ] using hstep
  have hstart : potential 0 ≤ Real.log coordinates.card := by
    have hbound := finite_entropy_le_log_card coordinates (leader 0)
      (hprob (leader 0) (hleaderQ 0)).1 (hprob (leader 0) (hleaderQ 0)).2
    simpa [potential, entropyValue, optimisticHistory] using hbound
  have hcomparator : η *
      ((∑ t ∈ range S, ∑ i ∈ coordinates, (gain t i + decrement t i) * comparator i) -
        2 * κ * ∑ t ∈ range S, ∑ i ∈ coordinates, decrement t i * comparator i) ≤
        potential S := by
    have hmax := hleaderMax S hcQ
    change entropyValue coordinates η (optimisticHistory κ gain decrement S) comparator ≤
      potential S at hmax
    rw [entropyValue_eq, optimisticHistory_inner_product] at hmax
    have hentropy := finite_entropy_nonnegative coordinates comparator
      (hprob comparator hcQ).1 (hprob comparator hcQ).2
    linarith
  have hdecrementSum : (∑ t ∈ range S, ∑ i ∈ coordinates, decrement t i * comparator i) ≤ 1 := by
    calc
      _ = ∑ i ∈ coordinates, (∑ t ∈ range S, decrement t i) * comparator i := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i hi
        rw [sum_mul]
      _ ≤ ∑ i ∈ coordinates, comparator i := sum_le_sum fun i hi => by
        simpa using mul_le_mul_of_nonneg_right (hdecrement i hi) ((hprob comparator hcQ).1 i hi)
      _ = 1 := (hprob comparator hcQ).2
  exact entropy_potential_telescoping S η κ (Real.log coordinates.card) potential
    (fun t => ∑ i ∈ coordinates, (gain t i + (1 - κ) * decrement t i) * predicted t i)
    (fun t => ∑ i ∈ coordinates, (gain t i + decrement t i) * comparator i)
    (fun t => ∑ i ∈ coordinates, decrement t i * comparator i)
    hη hκ hincrement hstart hcomparator hdecrementSum

/-- Replacing a probability vector by an approximation in `ℓ₁` loses
at most that error against any coordinate gain in `[-1, 0]`. -/
theorem bounded_gain_l1_approximation {ι : Type*} (coordinates : Finset ι)
    (gain exactVector approximateVector : ι → ℝ) (error : ℝ)
    (hgain : ∀ i ∈ coordinates, -1 ≤ gain i ∧ gain i ≤ 0)
    (hl1 : ∑ i ∈ coordinates, |approximateVector i - exactVector i| ≤ error) :
    (∑ i ∈ coordinates, gain i * exactVector i) - error ≤
      ∑ i ∈ coordinates, gain i * approximateVector i := by
  have hterm (i : ι) (hi : i ∈ coordinates) :
      gain i * (exactVector i - approximateVector i) ≤
        |approximateVector i - exactVector i| := by
    have habs : |gain i| ≤ 1 := abs_le.mpr ⟨(hgain i hi).1, (hgain i hi).2.trans zero_le_one⟩
    calc
      _ ≤ |gain i * (exactVector i - approximateVector i)| := le_abs_self _
      _ = |gain i| * |exactVector i - approximateVector i| := abs_mul _ _
      _ ≤ 1 * |exactVector i - approximateVector i| :=
        mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = _ := by rw [one_mul, abs_sub_comm]
  have hsum := (sum_le_sum hterm).trans hl1
  simp only [mul_sub, sum_sub_distrib] at hsum
  linarith

/-- The entropy-regret lemma in its fixed-child-block form. Baseline
decrements are constructed as the actual minimum within each child
block; the range hypothesis supplies the small residual required by
the potential proof. -/
theorem finite_block_entropy_regret {ι β : Type*} [Fintype β] [DecidableEq β]
    (coordinates : Finset ι) (block : ι → β)
    (Q : Set (ι → ℝ)) (S : ℕ) (η κ rangeBound : ℝ)
    (gain decrement predicted : ℕ → ι → ℝ) (witness comparator : ι → ℝ)
    (hcompact : IsCompact Q) (hconvex : Convex ℝ Q)
    (hwQ : witness ∈ Q) (hcQ : comparator ∈ Q)
    (hw : ∀ i ∈ coordinates, 0 < witness i)
    (hprob : ∀ p ∈ Q,
      (∀ i ∈ coordinates, 0 ≤ p i) ∧ (∑ i ∈ coordinates, p i = 1))
    (hblocks : ∀ b, (coordinates.filter (fun i => block i = b)).Nonempty)
    (hblockMass : ∀ p ∈ Q, ∀ q ∈ Q, ∀ b,
      (∑ i ∈ coordinates with block i = b, p i) =
        ∑ i ∈ coordinates with block i = b, q i)
    (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : η * rangeBound ≤ κ)
    (hpredQ : ∀ t < S, predicted t ∈ Q)
    (hpredMax : ∀ t < S, IsMaxOn
      (entropyValue coordinates η
        (fun i => optimisticHistory κ gain decrement t i + gain t i)) Q (predicted t))
    (hdecrementNonneg : ∀ t < S, ∀ i ∈ coordinates, 0 ≤ decrement t i)
    (hrange : ∀ t < S, ∀ i ∈ coordinates, ∀ j ∈ coordinates,
      block i = block j → |decrement t i - decrement t j| ≤ rangeBound)
    (hdecrement : ∀ i ∈ coordinates, ∑ t ∈ range S, decrement t i ≤ 1) :
    (∑ t ∈ range S, ∑ i ∈ coordinates, (gain t i + decrement t i) * comparator i) -
        Real.log coordinates.card / η - 2 * κ ≤
      ∑ t ∈ range S, ∑ i ∈ coordinates,
        (gain t i + (1 - κ) * decrement t i) * predicted t i := by
  classical
  let blockMinimum : ℕ → β → ℝ := fun t b =>
    (coordinates.filter (fun i => block i = b)).inf' (hblocks b) (decrement t)
  let baseline : ℕ → ι → ℝ := fun t i => blockMinimum t (block i)
  let innovation : ℕ → ι → ℝ := fun t i => decrement t i - baseline t i
  have hbaseline (t : ℕ) (ht : t < S) (i : ι) (hi : i ∈ coordinates) :
      0 ≤ baseline t i := by
    apply Finset.le_inf'
    intro j hj
    exact hdecrementNonneg t ht j (mem_filter.mp hj).1
  have hminor (t : ℕ) (i : ι) (hi : i ∈ coordinates) :
      baseline t i ≤ decrement t i := by
    have hiBlock : i ∈ coordinates.filter (fun j => block j = block i) :=
      mem_filter.mpr ⟨hi, rfl⟩
    exact Finset.inf'_le (decrement t) hiBlock
  have hresidual (t : ℕ) (ht : t < S) (i : ι) (hi : i ∈ coordinates) :
      innovation t i ≤ rangeBound := by
    have hlower : decrement t i - rangeBound ≤ baseline t i := by
      apply Finset.le_inf'
      intro j hj
      have hdiff := hrange t ht i hi j (mem_filter.mp hj).1 (mem_filter.mp hj).2.symm
      have := (abs_le.mp hdiff).2
      linarith
    dsimp only [innovation]
    linarith
  apply finite_hull_entropy_regret coordinates Q S η κ gain decrement baseline innovation
    predicted witness comparator hcompact hconvex hwQ hcQ hw hprob hη hκ hκhalf
    hpredQ hpredMax hbaseline
  · intro t ht i hi
    dsimp only [innovation]
    ring
  · intro t ht p hp q hq
    exact fixed_block_mass_inner_product coordinates block p q (blockMinimum t)
      (hblockMass p hp q hq)
  · intro t ht i hi
    exact mul_nonneg hη.le (sub_nonneg.mpr (hminor t i hi))
  · intro t ht i hi
    exact (mul_le_mul_of_nonneg_left (hresidual t ht i hi) hη.le).trans hηrange
  · exact hdecrement

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_Numerics
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite numerical optimizer for edit-distance refinement

These are the explicit fixed-step recurrence and rational mixture
calculations from Section 9 of *An Almost-Linear Approximation Scheme
for Edit Distance* (September 24, 2026). The recurrence is an internal
analytic obligation of the manuscript, not an assumed published theorem.
-/

namespace EditApproximation

open Finset

theorem frankWolfeStep_nonnegative (j : ℕ) : 0 ≤ frankWolfeStep j := by
  unfold frankWolfeStep
  positivity

theorem frankWolfeStep_le_one (j : ℕ) : frankWolfeStep j ≤ 1 := by
  unfold frankWolfeStep
  apply (div_le_one₀ (by positivity)).mpr
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

/-- The scalar induction step giving the optimizer's `8/(σ(j+1))`
error term. -/
theorem frank_wolfe_scalar_step (σ error x : ℝ) (hσ : 0 < σ) (hx : 0 ≤ x) :
    (1 - 2 / (x + 3)) * (2 * error + 8 / (σ * (x + 2))) +
        2 * error * (2 / (x + 3)) + 2 * (2 / (x + 3)) ^ 2 / σ ≤
      2 * error + 8 / (σ * (x + 3)) := by
  have h2 : 0 < x + 2 := by linarith
  have h3 : 0 < x + 3 := by linarith
  have hid :
      (2 * error + 8 / (σ * (x + 3))) -
        ((1 - 2 / (x + 3)) * (2 * error + 8 / (σ * (x + 2))) +
          2 * error * (2 / (x + 3)) + 2 * (2 / (x + 3)) ^ 2 / σ) =
        8 / (σ * (x + 2) * (x + 3) ^ 2) := by
    field_simp [hσ.ne', h2.ne', h3.ne']
    ring
  have hnonneg : 0 ≤ 8 / (σ * (x + 2) * (x + 3) ^ 2) := by positivity
  linarith

/-- The first update removes dependence on the initial objective gap.
The conclusion corresponds to manuscript indices `j ≥ 1`. -/
theorem frank_wolfe_gap_bound (σ error : ℝ) (gap : ℕ → ℝ)
    (hσ : 0 < σ)
    (hrecurrence : ∀ j,
      gap (j + 1) ≤ (1 - frankWolfeStep j) * gap j +
        2 * error * frankWolfeStep j + 2 * (frankWolfeStep j) ^ 2 / σ) :
    ∀ j : ℕ, gap (j + 1) ≤ 2 * error + 8 / (σ * ((j : ℝ) + 2)) := by
  intro j
  induction j with
  | zero =>
    have hfirst : gap 1 ≤ 2 * error + 2 / σ := by
      simpa [frankWolfeStep] using hrecurrence 0
    have hratio : 8 / (σ * (0 + 2)) = 4 / σ := by ring
    rw [Nat.cast_zero, hratio]
    have hnonneg : 0 ≤ 2 / σ := by positivity
    have hratio' : 4 / σ = 2 * (2 / σ) := by ring
    rw [hratio']
    norm_num only [Nat.zero_add]
    linarith
  | succ j ih =>
    have hstep : frankWolfeStep (j + 1) = 2 / ((j : ℝ) + 3) := by
      norm_num [frankWolfeStep, Nat.cast_add, add_assoc]
    have hcoef : 0 ≤ 1 - frankWolfeStep (j + 1) :=
      sub_nonneg.mpr (frankWolfeStep_le_one _)
    have hmono := mul_le_mul_of_nonneg_left ih hcoef
    have hrec := hrecurrence (j + 1)
    rw [hstep] at hmono hrec
    have hscalar := frank_wolfe_scalar_step σ error (j : ℝ) hσ (Nat.cast_nonneg _)
    have hbound : gap (j + 1 + 1) ≤ 2 * error + 8 / (σ * ((j : ℝ) + 3)) := by
      linarith
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [Nat.cast_add, add_assoc]

/-- The increase of `-x log x` after adding a positive smoothing
parameter is bounded by that parameter's own entropy. -/
theorem entropy_smoothing_upper (x σ : ℝ) (hx : 0 ≤ x) (hσ : 0 < σ) :
    Real.negMulLog (x + σ) - Real.negMulLog x ≤ Real.negMulLog σ := by
  by_cases hxzero : x = 0
  · simp [hxzero]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hlogσ : 0 ≤ Real.log (x + σ) - Real.log σ :=
      sub_nonneg.mpr (Real.log_le_log hσ (by linarith))
    have hlogx : 0 ≤ Real.log (x + σ) - Real.log x :=
      sub_nonneg.mpr (Real.log_le_log hxpos (by linarith))
    have hprodσ := mul_nonneg hσ.le hlogσ
    have hprodx := mul_nonneg hx hlogx
    simp only [Real.negMulLog]
    nlinarith

/-- The negative change in the smoothed entropy coordinate is linear
in the smoothing parameter on the relevant interval `[0,2]`. -/
theorem entropy_smoothing_lower (x σ : ℝ) (hx : 0 ≤ x) (hσ : 0 < σ)
    (hupper : x + σ ≤ 2) :
    Real.negMulLog x - Real.negMulLog (x + σ) ≤ 2 * σ := by
  have hxs : 0 < x + σ := by linarith
  have hlog : Real.log (x + σ) ≤ 1 := by
    exact (Real.log_le_log hxs hupper).trans (by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith)
  have hσlog := mul_le_mul_of_nonneg_left hlog hσ.le
  by_cases hxzero : x = 0
  · rw [hxzero, zero_add] at hσlog
    simp only [hxzero, Real.negMulLog, zero_add, neg_zero, zero_mul, zero_sub]
    nlinarith
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hratio := Real.log_le_sub_one_of_pos (div_pos hxs hxpos)
    rw [Real.log_div hxs.ne' hxpos.ne'] at hratio
    have hratio' := mul_le_mul_of_nonneg_left hratio hx
    have hcancel : x * ((x + σ) / x - 1) = σ := by
      field_simp
      ring
    rw [hcancel] at hratio'
    simp only [Real.negMulLog]
    nlinarith

theorem negMulLog_le_two_sqrt (σ : ℝ) (hσ : 0 < σ) :
    Real.negMulLog σ ≤ 2 * Real.sqrt σ := by
  have hroot : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hsq : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt hσ.le
  have hdiv : σ / Real.sqrt σ = Real.sqrt σ := by
    apply (div_eq_iff hroot.ne').mpr
    nlinarith
  have hmul : σ * (Real.sqrt σ)⁻¹ = Real.sqrt σ := by
    simpa only [div_eq_mul_inv] using hdiv
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hroot)
  rw [Real.log_inv, Real.log_sqrt hσ.le] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * σ by positivity)
  simp only [Real.negMulLog]
  nlinarith

/-- A uniform coordinate modulus for entropy smoothing, valid including
zero coordinates. -/
theorem entropy_smoothing_coordinate (x σ : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    |Real.negMulLog (x + σ) - Real.negMulLog x| ≤ 2 * Real.sqrt σ := by
  have hupper := (entropy_smoothing_upper x σ hx hσ).trans (negMulLog_le_two_sqrt σ hσ)
  have hlower := entropy_smoothing_lower x σ hx hσ (by linarith)
  have hσroot : σ ≤ Real.sqrt σ := by
    have hsq : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt hσ.le
    have hroot := Real.sqrt_nonneg σ
    have hσsq : σ ^ 2 ≤ σ := by nlinarith
    nlinarith
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- Manuscript Equation `eq:entropy-smoothing`, with a slightly stronger
constant from the coordinate estimate. The linear coefficient vector
cancels, so the bound is independent of its magnitude. -/
theorem finite_entropy_smoothing_bound {ι : Type*} (coordinates : Finset ι)
    (p objective : ι → ℝ) (σ η : ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    |((∑ i ∈ coordinates, Real.negMulLog (p i + σ)) +
        η * ∑ i ∈ coordinates, objective i * p i) -
      entropyValue coordinates η objective p| ≤ 4 * coordinates.card * Real.sqrt σ := by
  rw [entropyValue_eq]
  have hcancel :
      ((∑ i ∈ coordinates, Real.negMulLog (p i + σ)) +
        η * ∑ i ∈ coordinates, objective i * p i) -
        ((∑ i ∈ coordinates, Real.negMulLog (p i)) +
          η * ∑ i ∈ coordinates, objective i * p i) =
        ∑ i ∈ coordinates, (Real.negMulLog (p i + σ) - Real.negMulLog (p i)) := by
    rw [sum_sub_distrib]
    ring
  rw [hcancel]
  calc
    _ ≤ ∑ i ∈ coordinates, |Real.negMulLog (p i + σ) - Real.negMulLog (p i)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ coordinates, 2 * Real.sqrt σ := sum_le_sum fun i hi =>
      entropy_smoothing_coordinate (p i) σ (hp i hi)
        ((single_le_sum hp hi).trans hpsum.le) hσ hσ1
    _ ≤ 4 * coordinates.card * Real.sqrt σ := by
      simp only [sum_const, nsmul_eq_mul]
      have hc : 0 ≤ (coordinates.card : ℝ) := Nat.cast_nonneg _
      have hroot := Real.sqrt_nonneg σ
      nlinarith

private theorem entropy_quadratic_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => z * Real.log z - z ^ 2 / 2)
      (Real.log x + 1 - x) x := by
  convert! (Real.hasDerivAt_mul_log hx.ne').sub
    (((hasDerivAt_id x).pow 2).div_const 2) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq]
  ring

/-- Negative entropy minus half the square is convex on the probability
coordinate interval. This is the exact curvature bound used for the
objective-gap estimate in the finite optimizer. -/
theorem entropy_quadratic_convex :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun z : ℝ => z * Real.log z - z ^ 2 / 2) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc (0 : ℝ) 1)
  · exact (Real.continuous_mul_log.sub (by fun_prop)).continuousOn
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    exact (entropy_quadratic_hasDerivAt x hx.1).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    simp only [interior_Icc, Set.mem_Ioo] at hx hy
    rw [(entropy_quadratic_hasDerivAt x hx.1).deriv,
      (entropy_quadratic_hasDerivAt y hy.1).deriv]
    have hratio := Real.one_sub_inv_le_log_of_pos (div_pos hy.1 hx.1)
    have hinv : (y / x)⁻¹ = x / y := by field_simp
    rw [hinv, Real.log_div hy.1.ne' hx.1.ne'] at hratio
    have hscaled := mul_le_mul_of_nonneg_left hratio hy.1.le
    have hcancel : y * (1 - x / y) = y - x := by field_simp [hy.1.ne']
    rw [hcancel] at hscaled
    have hlog : 0 ≤ Real.log y - Real.log x :=
      sub_nonneg.mpr (Real.log_le_log hx.1 hxy)
    have hcorrection := mul_nonneg (show 0 ≤ 1 - y by linarith) hlog
    nlinarith

/-- The entropy coordinate gap is at least half the squared coordinate
distance, including the competitor value zero by continuity. -/
theorem entropy_coordinate_strong_gap (x y : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1) :
    (x - y) ^ 2 / 2 ≤
      x * Real.log x - y * Real.log y - (Real.log y + 1) * (x - y) := by
  have hderiv := entropy_quadratic_hasDerivAt y hy
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hslope := entropy_quadratic_convex.slope_le_of_hasDerivAt
      ⟨hx, hx1⟩ ⟨hy.le, hy1⟩ hxy hderiv
    rw [slope_def_field] at hslope
    have hmul := (div_le_iff₀ (sub_pos.mpr hxy)).mp hslope
    nlinarith
  · simp
  · have hslope := entropy_quadratic_convex.le_slope_of_hasDerivAt
      ⟨hy.le, hy1⟩ ⟨hx, hx1⟩ hyx hderiv
    rw [slope_def_field] at hslope
    have hmul := (le_div_iff₀ (sub_pos.mpr hyx)).mp hslope
    nlinarith

/-- Relative entropy dominates half the squared Euclidean distance on
the finite probability simplex. -/
theorem finite_relative_entropy_sq_gap {ι : Type*} (coordinates : Finset ι)
    (p q : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hq : ∀ i ∈ coordinates, 0 ≤ q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1) :
    (∑ i ∈ coordinates, (q i - p i) ^ 2) / 2 ≤
      ∑ i ∈ coordinates, q i * Real.log (q i / p i) := by
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      (q i - p i) ^ 2 / 2 ≤ q i * Real.log (q i / p i) - q i + p i := by
    have hstrong := entropy_coordinate_strong_gap (q i) (p i) (hq i hi)
      ((single_le_sum hq hi).trans hqsum.le) (hp i hi)
      ((single_le_sum (fun j hj => (hp j hj).le) hi).trans hpsum.le)
    by_cases hqzero : q i = 0
    · simp only [hqzero, zero_mul, sub_zero, zero_sub] at hstrong ⊢
      nlinarith
    · rw [Real.log_div hqzero (hp i hi).ne']
      nlinarith
  have hsum := sum_le_sum hcoord
  rw [← sum_div, sum_add_distrib, sum_sub_distrib, hqsum, hpsum] at hsum
  linarith

/-- A true entropy-objective gap controls the `ℓ₁` error of a feasible
mixture, with the manuscript's exact factor `sqrt (2d gap)`. -/
theorem entropy_gap_to_l1 {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η : ℝ) (objective maximizer mixture : ι → ℝ)
    (hconvex : Convex ℝ Q) (hmaxQ : maximizer ∈ Q) (hmixQ : mixture ∈ Q)
    (hmax : ∀ i ∈ coordinates, 0 < maximizer i)
    (hmix : ∀ i ∈ coordinates, 0 ≤ mixture i)
    (hmaxsum : ∑ i ∈ coordinates, maximizer i = 1)
    (hmixsum : ∑ i ∈ coordinates, mixture i = 1)
    (hmaximize : IsMaxOn (entropyValue coordinates η objective) Q maximizer) :
    (∑ i ∈ coordinates, |mixture i - maximizer i|) ≤
      Real.sqrt (2 * coordinates.card *
        (entropyValue coordinates η objective maximizer -
          entropyValue coordinates η objective mixture)) := by
  have hpenalty := entropy_hull_penalty coordinates Q η objective maximizer mixture
    hconvex hmaxQ hmixQ hmax hmaxsum hmixsum hmaximize
  have hsq := finite_relative_entropy_sq_gap coordinates maximizer mixture hmax hmix hmaxsum hmixsum
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul coordinates
    (fun _ _ => (show (0 : ℝ) ≤ 1 by norm_num))
    (fun i _ => sq_nonneg (mixture i - maximizer i))
    (fun i _ => (show |mixture i - maximizer i| ^ 2 ≤ 1 * (mixture i - maximizer i) ^ 2 by
      rw [one_mul, sq_abs]))
  simp only [sum_const, nsmul_eq_mul, mul_one] at hcs
  apply Real.le_sqrt_of_sq_le
  have hc : 0 ≤ (coordinates.card : ℝ) := Nat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left (show
      (∑ i ∈ coordinates, (mixture i - maximizer i) ^ 2) ≤
        2 * (entropyValue coordinates η objective maximizer -
          entropyValue coordinates η objective mixture) by linarith) hc
  nlinarith

theorem optimizer_work_budget_gap (G : ℝ) (hG : 0 < G) :
    8 / ((1 / G ^ 50) * (G ^ 80 + 1)) ≤ 8 / G ^ 30 := by
  have hpow : G ^ 80 = G ^ 50 * G ^ 30 := by rw [← pow_add]
  have hcancel : (1 / G ^ 50) * G ^ 80 = G ^ 30 := by
    rw [hpow]
    field_simp
  have hdenom : G ^ 30 ≤ (1 / G ^ 50) * (G ^ 80 + 1) := by
    rw [← hcancel]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hG _) hdenom

theorem optimizer_smoothing_root (G : ℝ) (hG : 0 < G) :
    Real.sqrt (1 / G ^ 50) = 1 / G ^ 25 := by
  have hpow : G ^ 50 = (G ^ 25) ^ 2 := by rw [← pow_mul]
  rw [hpow, Real.sqrt_div (by positivity), Real.sqrt_one, Real.sqrt_sq_eq_abs,
    abs_of_pos (pow_pos hG _)]

/-- The explicit total objective-gap bound after the prescribed
number of fixed-step updates. -/
theorem optimizer_explicit_gap_budget (G d : ℝ) (hG : 4 ≤ G) (hd : d ≤ G) :
    2 / G ^ 20 + 8 / G ^ 30 + 8 * d / G ^ 25 ≤ 12 / G ^ 20 := by
  have hGpos : 0 < G := by linarith
  have hG1 : 1 ≤ G := by linarith
  have hG10 : 4 ≤ G ^ 10 := hG.trans (by
    simpa using pow_le_pow_right₀ hG1 (by norm_num : 1 ≤ 10))
  have hG5 : d ≤ G ^ 5 := hd.trans (by
    simpa using pow_le_pow_right₀ hG1 (by norm_num : 1 ≤ 5))
  have hsmall : 8 / G ^ 30 ≤ 2 / G ^ 20 := by
    apply (div_le_div_iff₀ (pow_pos hGpos _) (pow_pos hGpos _)).mpr
    have hscale := mul_le_mul_of_nonneg_left hG10 (show 0 ≤ 2 * G ^ 20 by positivity)
    have hpow : G ^ 30 = G ^ 20 * G ^ 10 := by rw [← pow_add]
    rw [hpow]
    nlinarith
  have hsmooth : 8 * d / G ^ 25 ≤ 8 / G ^ 20 := by
    apply (div_le_div_iff₀ (pow_pos hGpos _) (pow_pos hGpos _)).mpr
    have hscale := mul_le_mul_of_nonneg_left hG5 (show 0 ≤ 8 * G ^ 20 by positivity)
    have hpow : G ^ 25 = G ^ 20 * G ^ 5 := by rw [← pow_add]
    rw [hpow]
    nlinarith
  have hsum : 2 / G ^ 20 + 2 / G ^ 20 + 8 / G ^ 20 = 12 / G ^ 20 := by ring
  linarith

/-- The quantitative final `H^(-3)` precision calculation. The squared
distance premise is supplied by the proved entropy/KL curvature bound. -/
theorem optimizer_final_l1_precision (H G d distance gap : ℝ)
    (hH : 4 ≤ H) (hHG : H ≤ G) (hd : 0 ≤ d) (hdG : d ≤ G)
    (hsquared : distance ^ 2 ≤ 2 * d * gap) (hgap : gap ≤ 12 / G ^ 20) :
    distance ≤ 1 / H ^ 3 := by
  have hHpos : 0 < H := by linarith
  have hGpos : 0 < G := lt_of_lt_of_le hHpos hHG
  have hG4 : 4 ≤ G := hH.trans hHG
  have hG1 : 1 ≤ G := by linarith
  have hG3 : 64 ≤ G ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hG4 3
    norm_num at h
    exact h
  have hG13 : 24 ≤ G ^ 13 := by
    have hmono := pow_le_pow_right₀ hG1 (by norm_num : 3 ≤ 13)
    linarith
  have hratio : 24 / G ^ 19 ≤ 1 / G ^ 6 := by
    apply (div_le_div_iff₀ (pow_pos hGpos _) (pow_pos hGpos _)).mpr
    have hscale := mul_le_mul_of_nonneg_right hG13 (pow_nonneg hGpos.le 6)
    have hpow : G ^ 19 = G ^ 13 * G ^ 6 := by rw [← pow_add]
    rw [hpow]
    nlinarith
  have hHratio : 1 / G ^ 6 ≤ 1 / H ^ 6 :=
    div_le_div_of_nonneg_left zero_le_one (pow_pos hHpos _)
      (pow_le_pow_left₀ hHpos.le hHG 6)
  have hscale := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * d by positivity)
  have hdimension := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdG (by norm_num : (0 : ℝ) ≤ 24))
    (pow_nonneg hGpos.le 20)
  have hcancel : 24 * G / G ^ 20 = 24 / G ^ 19 := by
    have hpow : G ^ 20 = G ^ 19 * G := by rw [← pow_succ]
    rw [hpow]
    field_simp
  have hsquare : distance ^ 2 ≤ 1 / H ^ 6 := by
    rw [hcancel] at hdimension
    have hcombined := hdimension.trans (hratio.trans hHratio)
    have hscaledGap : 2 * d * (12 / G ^ 20) = 24 * d / G ^ 20 := by ring
    rw [hscaledGap] at hscale
    exact hsquared.trans (hscale.trans hcombined)
  have htarget : (1 / H ^ 3) ^ 2 = 1 / H ^ 6 := by
    rw [div_pow, one_pow, ← pow_mul]
  have hpositive : 0 < 1 / H ^ 3 := by positivity
  rw [← htarget] at hsquare
  nlinarith

/-- Rational truncated logarithm used for the entropy-gradient
calculation. Its evaluation uses only rational arithmetic. -/


theorem rationalLogApproximation_cast (r : ℚ) (K : ℕ) :
    (rationalLogApproximation r K : ℝ) =
      2 * ∑ k ∈ range K,
        ((((r : ℝ) - 1) / ((r : ℝ) + 1)) ^ (2 * k + 1) / (2 * k + 1)) := by
  unfold rationalLogApproximation
  push_cast
  rfl

theorem logarithm_symmetric_parameter_bound (r σ : ℝ)
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hr : σ ≤ r) (hrupper : r ≤ 1 + σ) :
    |(r - 1) / (r + 1)| ≤ 1 - σ := by
  have hrpos : 0 < r := hσ.trans_le hr
  have hrden : 0 < r + 1 := by linarith
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hrden).mpr
    have hprod := mul_nonneg hrpos.le (show 0 ≤ 1 - σ by linarith)
    nlinarith
  · apply (div_le_iff₀ hrden).mpr
    have hmul := mul_le_mul_of_nonneg_left hrupper hσ.le
    have hσsquare : σ ^ 2 ≤ σ / 2 := by
      have h := mul_le_mul_of_nonneg_left hσhalf hσ.le
      nlinarith
    nlinarith

/-- Explicit logarithm-series remainder for the rational gradient
routine. Mathlib's logarithm remainder is specialized to the bounded
smoothed-coordinate interval. Its bound suffices for the prescribed
polynomial truncation length. -/
theorem logarithm_series_error (r σ : ℝ) (K : ℕ)
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hr : σ ≤ r) (hrupper : r ≤ 1 + σ) :
    |Real.log r - 2 * ∑ k ∈ range K,
        (((r - 1) / (r + 1)) ^ (2 * k + 1) / (2 * k + 1))| ≤
      2 * Real.exp (-2 * K * σ) / σ := by
  let b := (r - 1) / (r + 1)
  have hrpos : 0 < r := hσ.trans_le hr
  have hrden : 0 < r + 1 := by linarith
  have hb : |b| ≤ 1 - σ := logarithm_symmetric_parameter_bound r σ hσ hσhalf hr hrupper
  have hb1 : |b| < 1 := by linarith
  have htransform : (1 + b) / (1 - b) = r := by
    dsimp only [b]
    field_simp
    ring
  have hseries := Real.sum_range_sub_log_div_le hb1 K
  rw [htransform] at hseries
  have htwice := mul_le_mul_of_nonneg_left hseries (show (0 : ℝ) ≤ 2 by norm_num)
  have hleft :
      |Real.log r - 2 * ∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1)| =
        2 * |1 / 2 * Real.log r - ∑ k ∈ range K, b ^ (2 * k + 1) / (2 * k + 1)| := by
    rw [← abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), ← abs_mul]
    congr 1
    ring
  rw [← hleft, ← mul_div_assoc] at htwice
  have hdenom : σ ≤ 1 - b ^ 2 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg b) hb 2
    rw [sq_abs] at hsq
    have hσsq : σ ^ 2 ≤ σ := by nlinarith
    nlinarith
  have hnum : |b| ^ (2 * K + 1) ≤ Real.exp (-2 * K * σ) := by
    calc
      _ ≤ (1 - σ) ^ (2 * K + 1) := pow_le_pow_left₀ (abs_nonneg b) hb _
      _ ≤ Real.exp (-σ) ^ (2 * K + 1) := pow_le_pow_left₀
        (show 0 ≤ 1 - σ by linarith) (Real.one_sub_le_exp_neg σ) _
      _ = Real.exp ((2 * K + 1 : ℕ) * (-σ)) := (Real.exp_nat_mul (-σ) _).symm
      _ ≤ Real.exp (-2 * K * σ) := Real.exp_le_exp.mpr (by push_cast <;> nlinarith)
  calc
    _ ≤ 2 * |b| ^ (2 * K + 1) / (1 - b ^ 2) := htwice
    _ ≤ 2 * Real.exp (-2 * K * σ) / (1 - b ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num))
        (hσ.le.trans hdenom)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hσ hdenom

theorem rationalLogApproximation_error (r : ℚ) (σ : ℝ) (K : ℕ)
    (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hr : σ ≤ (r : ℝ)) (hrupper : (r : ℝ) ≤ 1 + σ) :
    |Real.log (r : ℝ) - (rationalLogApproximation r K : ℝ)| ≤
      2 * Real.exp (-2 * K * σ) / σ := by
  rw [rationalLogApproximation_cast]
  exact logarithm_series_error (r : ℝ) σ K hσ hσhalf hr hrupper

theorem logarithm_truncation_exponential_budget (G : ℝ) (hG : 4 ≤ G) :
    2 * Real.exp (-2 * G ^ 10) / (1 / G ^ 50) ≤ 1 / G ^ 20 := by
  have hGpos : 0 < G := by linarith
  have hG1 : 1 ≤ G := by linarith
  have hG5 : 1024 ≤ G ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hG 5
    norm_num at h
    exact h
  have hG10 : 315 ≤ G ^ 10 := by
    have hmono := pow_le_pow_right₀ hG1 (by norm_num : 5 ≤ 10)
    linarith
  have hpoly : 2 * G ^ 70 ≤ (2 * G ^ 10) ^ 8 / (8 : ℕ).factorial := by
    norm_num
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 40320)).mpr
    rw [mul_pow, ← pow_mul]
    have hpow : G ^ 80 = G ^ 70 * G ^ 10 := by rw [← pow_add]
    norm_num
    rw [hpow]
    have hscale := mul_le_mul_of_nonneg_left hG10 (show 0 ≤ 256 * G ^ 70 by positivity)
    nlinarith
  have hexp : 2 * G ^ 70 ≤ Real.exp (2 * G ^ 10) :=
    hpoly.trans (Real.pow_div_factorial_le_exp (x := 2 * G ^ 10) (n := 8) (by positivity))
  have heq : 2 * Real.exp (-2 * G ^ 10) / (1 / G ^ 50) =
      2 * G ^ 50 / Real.exp (2 * G ^ 10) := by
    rw [show -2 * G ^ 10 = -(2 * G ^ 10) by ring, Real.exp_neg]
    field_simp [hGpos.ne']
  rw [heq]
  apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos hGpos _)).mpr
  have hpow : G ^ 50 * G ^ 20 = G ^ 70 := by rw [← pow_add]
  nlinarith

/-- The prescribed rational logarithm computation has the required
absolute gradient precision `G^(-20)` after `G^60` rational terms. -/
theorem rationalLogApproximation_prescribed_precision (r : ℚ) (G : ℕ)
    (hG : 4 ≤ G)
    (hr : 1 / (G : ℝ) ^ 50 ≤ (r : ℝ))
    (hrupper : (r : ℝ) ≤ 1 + 1 / (G : ℝ) ^ 50) :
    |Real.log (r : ℝ) - (rationalLogApproximation r (G ^ 60) : ℝ)| ≤
      1 / (G : ℝ) ^ 20 := by
  have hG4 : (4 : ℝ) ≤ G := by exact_mod_cast hG
  have hGpos : (0 : ℝ) < G := by linarith
  have hG1 : (1 : ℝ) ≤ G := by linarith
  have hG50 : (2 : ℝ) ≤ (G : ℝ) ^ 50 := by
    have hmono := pow_le_pow_right₀ hG1 (by norm_num : 1 ≤ 50)
    norm_num only [pow_one] at hmono
    linarith
  have hσpos : 0 < 1 / (G : ℝ) ^ 50 := by positivity
  have hσhalf : 1 / (G : ℝ) ^ 50 ≤ 1 / 2 := by
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hG50
  have herror := rationalLogApproximation_error r (1 / (G : ℝ) ^ 50) (G ^ 60)
    hσpos hσhalf hr hrupper
  have hprod : ((G ^ 60 : ℕ) : ℝ) * (1 / (G : ℝ) ^ 50) = (G : ℝ) ^ 10 := by
    push_cast
    have hpow : (G : ℝ) ^ 60 = (G : ℝ) ^ 10 * (G : ℝ) ^ 50 := by rw [← pow_add]
    rw [hpow]
    field_simp
  have hexponent : -2 * ((G ^ 60 : ℕ) : ℝ) * (1 / (G : ℝ) ^ 50) =
      -2 * (G : ℝ) ^ 10 := by nlinarith [hprod]
  rw [hexponent] at herror
  exact herror.trans (logarithm_truncation_exponential_budget (G : ℝ) hG4)

theorem finite_gradient_error {ι : Type*} (coordinates : Finset ι)
    (gradient approximateGradient p : ι → ℝ) (error : ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (herror : ∀ i ∈ coordinates, |approximateGradient i - gradient i| ≤ error) :
    |∑ i ∈ coordinates, (approximateGradient i - gradient i) * p i| ≤ error := by
  calc
    _ ≤ ∑ i ∈ coordinates, |(approximateGradient i - gradient i) * p i| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ coordinates, error * p i := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hp i hi)]
      exact mul_le_mul_of_nonneg_right (herror i hi) (hp i hi)
    _ = error := by rw [← mul_sum, hpsum, mul_one]

/-- Enumerating the vertices with an approximate gradient loses at
most `2e₀` in the true linearization, even against an arbitrary feasible
mixture. -/
theorem approximate_gradient_linearization_loss {ι : Type*} (coordinates : Finset ι)
    (gradient approximateGradient selected competitor : ι → ℝ) (error : ℝ)
    (hselected : ∀ i ∈ coordinates, 0 ≤ selected i)
    (hcompetitor : ∀ i ∈ coordinates, 0 ≤ competitor i)
    (hselectedSum : ∑ i ∈ coordinates, selected i = 1)
    (hcompetitorSum : ∑ i ∈ coordinates, competitor i = 1)
    (herror : ∀ i ∈ coordinates, |approximateGradient i - gradient i| ≤ error)
    (hchoose : (∑ i ∈ coordinates, approximateGradient i * competitor i) ≤
      ∑ i ∈ coordinates, approximateGradient i * selected i) :
    (∑ i ∈ coordinates, gradient i * competitor i) -
        (∑ i ∈ coordinates, gradient i * selected i) ≤ 2 * error := by
  have hsel := finite_gradient_error coordinates gradient approximateGradient selected
    error hselected hselectedSum herror
  have hcomp := finite_gradient_error coordinates gradient approximateGradient competitor
    error hcompetitor hcompetitorSum herror
  simp only [sub_mul, sum_sub_distrib] at hsel hcomp
  have hselBounds := abs_le.mp hsel
  have hcompBounds := abs_le.mp hcomp
  linarith

/-- Tangent upper bound for a single smoothed entropy coordinate. -/
theorem smoothed_entropy_coordinate_upper (x y σ linear : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hσ : 0 < σ) :
    (Real.negMulLog (y + σ) + linear * y) -
        (Real.negMulLog (x + σ) + linear * x) ≤
      (-Real.log (x + σ) - 1 + linear) * (y - x) := by
  have hxs : 0 < x + σ := by linarith
  have hys : 0 < y + σ := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hxs hys)
  rw [Real.log_div hxs.ne' hys.ne'] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hys.le
  have hcancel : (y + σ) * ((x + σ) / (y + σ) - 1) = x - y := by
    field_simp
    ring
  rw [hcancel] at hscaled
  simp only [Real.negMulLog]
  nlinarith

/-- A scalar smoothness bound obtained directly from `log u ≤ u-1`.
The coefficient `1/σ` combines with the sharper simplex diameter below
to give the manuscript's exact `2 ξ²/σ` remainder. -/
theorem smoothed_entropy_coordinate_lower (x y σ linear : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hσ : 0 < σ) :
    (-Real.log (x + σ) - 1 + linear) * (y - x) - (y - x) ^ 2 / σ ≤
      (Real.negMulLog (y + σ) + linear * y) -
        (Real.negMulLog (x + σ) + linear * x) := by
  have hxs : 0 < x + σ := by linarith
  have hys : 0 < y + σ := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hys hxs)
  rw [Real.log_div hys.ne' hxs.ne'] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hys.le
  have hcancel : (y + σ) * ((y + σ) / (x + σ) - 1) - y + x =
      (y - x) ^ 2 / (x + σ) := by
    field_simp
    ring
  have hratio : (y - x) ^ 2 / (x + σ) ≤ (y - x) ^ 2 / σ :=
    div_le_div_of_nonneg_left (sq_nonneg _) hσ (by linarith)
  have hbound : (y + σ) * (Real.log (y + σ) - Real.log (x + σ)) - y + x ≤
      (y - x) ^ 2 / (x + σ) := by linarith
  have hbound' := hbound.trans hratio
  simp only [Real.negMulLog]
  nlinarith

theorem probability_vectors_sq_distance_le_two {ι : Type*} (coordinates : Finset ι)
    (p q : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hq : ∀ i ∈ coordinates, 0 ≤ q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1) :
    ∑ i ∈ coordinates, (q i - p i) ^ 2 ≤ 2 := by
  have hcoord (i : ι) (hi : i ∈ coordinates) : (q i - p i) ^ 2 ≤ q i + p i := by
    have hp1 := (single_le_sum hp hi).trans hpsum.le
    have hq1 := (single_le_sum hq hi).trans hqsum.le
    have hpprod := mul_nonneg (hp i hi) (sub_nonneg.mpr hp1)
    have hqprod := mul_nonneg (hq i hi) (sub_nonneg.mpr hq1)
    have hpq := mul_nonneg (hp i hi) (hq i hi)
    nlinarith
  calc
    _ ≤ ∑ i ∈ coordinates, (q i + p i) := sum_le_sum hcoord
    _ = 2 := by rw [sum_add_distrib, hqsum, hpsum]; norm_num

theorem smoothed_entropy_tangent_upper {ι : Type*} (coordinates : Finset ι)
    (σ : ℝ) (linear p q : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hq : ∀ i ∈ coordinates, 0 ≤ q i) (hσ : 0 < σ) :
    smoothedEntropyValue coordinates σ linear q - smoothedEntropyValue coordinates σ linear p ≤
      ∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * (q i - p i) := by
  rw [smoothedEntropyValue, smoothedEntropyValue, ← sum_sub_distrib]
  exact sum_le_sum fun i hi => smoothed_entropy_coordinate_upper (p i) (q i) σ
    (linear i) (hp i hi) (hq i hi) hσ

theorem smoothed_entropy_mixture_lower {ι : Type*} (coordinates : Finset ι)
    (σ ξ : ℝ) (linear p selected : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hselected : ∀ i ∈ coordinates, 0 ≤ selected i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hselectedSum : ∑ i ∈ coordinates, selected i = 1)
    (hσ : 0 < σ) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    ξ * (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * (selected i - p i)) -
        2 * ξ ^ 2 / σ ≤
      smoothedEntropyValue coordinates σ linear
          (fun i => (1 - ξ) * p i + ξ * selected i) - smoothedEntropyValue coordinates σ linear p := by
  let updated : ι → ℝ := fun i => (1 - ξ) * p i + ξ * selected i
  have hupdated (i : ι) (hi : i ∈ coordinates) : 0 ≤ updated i :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hξ1) (hp i hi))
      (mul_nonneg hξ (hselected i hi))
  have hcoordinate (i : ι) (hi : i ∈ coordinates) :=
    smoothed_entropy_coordinate_lower (p i) (updated i) σ (linear i) (hp i hi) (hupdated i hi) hσ
  have hsum := sum_le_sum hcoordinate
  have hterm (i : ι) : updated i - p i = ξ * (selected i - p i) := by
    dsimp only [updated]
    ring
  simp only [smoothedEntropyGradient] at hsum ⊢
  simp_rw [hterm, mul_pow, div_eq_mul_inv] at hsum
  rw [sum_sub_distrib] at hsum
  have hlinear :
      (∑ i ∈ coordinates, (-Real.log (p i + σ) - 1 + linear i) * (ξ * (selected i - p i))) =
        ξ * ∑ i ∈ coordinates, (-Real.log (p i + σ) - 1 + linear i) * (selected i - p i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  have hquadratic : (∑ i ∈ coordinates, ξ ^ 2 * (selected i - p i) ^ 2 * σ⁻¹) =
      (ξ ^ 2 / σ) * ∑ i ∈ coordinates, (selected i - p i) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hlinear, hquadratic, sum_sub_distrib] at hsum
  have hdiameter := probability_vectors_sq_distance_le_two coordinates p selected hp hselected hpsum hselectedSum
  have hscale := mul_le_mul_of_nonneg_left hdiameter (show 0 ≤ ξ ^ 2 / σ by positivity)
  change _ ≤ smoothedEntropyValue coordinates σ linear updated -
    smoothedEntropyValue coordinates σ linear p at hsum
  change _ ≤ smoothedEntropyValue coordinates σ linear updated -
    smoothedEntropyValue coordinates σ linear p
  have htwo : ξ ^ 2 / σ * 2 = 2 * ξ ^ 2 / σ := by ring
  rw [htwo] at hscale
  linarith

/-- The manuscript's fixed-step optimizer recurrence follows from the
actual smoothed entropy objective and approximate gradient selection. -/
theorem smoothed_frank_wolfe_recurrence {ι : Type*} (coordinates : Finset ι)
    (σ ξ error : ℝ) (linear p selected best approximateGradient : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hselected : ∀ i ∈ coordinates, 0 ≤ selected i)
    (hbest : ∀ i ∈ coordinates, 0 ≤ best i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hselectedSum : ∑ i ∈ coordinates, selected i = 1)
    (hbestSum : ∑ i ∈ coordinates, best i = 1)
    (hσ : 0 < σ) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hgradient : ∀ i ∈ coordinates,
      |approximateGradient i - smoothedEntropyGradient σ linear p i| ≤ error)
    (hchoose : (∑ i ∈ coordinates, approximateGradient i * best i) ≤
      ∑ i ∈ coordinates, approximateGradient i * selected i) :
    smoothedEntropyValue coordinates σ linear best -
        smoothedEntropyValue coordinates σ linear (fun i => (1 - ξ) * p i + ξ * selected i) ≤
      (1 - ξ) * (smoothedEntropyValue coordinates σ linear best - smoothedEntropyValue coordinates σ linear p) +
        2 * error * ξ + 2 * ξ ^ 2 / σ := by
  have htangent := smoothed_entropy_tangent_upper coordinates σ linear p best hp hbest hσ
  have hlinear := approximate_gradient_linearization_loss coordinates
    (smoothedEntropyGradient σ linear p) approximateGradient selected best error
    hselected hbest hselectedSum hbestSum hgradient hchoose
  have hlower := smoothed_entropy_mixture_lower coordinates σ ξ linear p selected
    hp hselected hpsum hselectedSum hσ hξ hξ1
  have hsumBest : (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * (best i - p i)) =
      (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * best i) -
        ∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * p i := by
    simp only [mul_sub, sum_sub_distrib]
  have hsumSelected : (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * (selected i - p i)) =
      (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * selected i) -
        ∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * p i := by
    simp only [mul_sub, sum_sub_distrib]
  rw [hsumBest] at htangent
  rw [hsumSelected] at hlower
  have hgain : smoothedEntropyValue coordinates σ linear best - smoothedEntropyValue coordinates σ linear p -
      2 * error ≤ (∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * selected i) -
        ∑ i ∈ coordinates, smoothedEntropyGradient σ linear p i * p i := by linarith
  have hscale := mul_le_mul_of_nonneg_left hgain hξ
  nlinarith

/-- Casting the exact rational update gives precisely the analytic step. -/
theorem rationalOptimizerIterate_cast_step {ι : Type*}
    (initial : ι → ℚ) (selected : ℕ → ι → ℚ) (j : ℕ) :
    (fun i => (rationalOptimizerIterate initial selected (j + 1) i : ℝ)) =
      (fun i => (1 - frankWolfeStep j) * (rationalOptimizerIterate initial selected j i : ℝ) +
        frankWolfeStep j * (selected j i : ℝ)) := by
  funext i
  simp [rationalOptimizerIterate, frankWolfeStep]

/-- All exact rational iterates are probability vectors. -/
theorem rationalOptimizerIterate_probability {ι : Type*} (coordinates : Finset ι)
    (initial : ι → ℚ) (selected : ℕ → ι → ℚ)
    (hinitial : ∀ i ∈ coordinates, (0 : ℝ) ≤ initial i)
    (hinitialSum : ∑ i ∈ coordinates, (initial i : ℝ) = 1)
    (hselected : ∀ j i, i ∈ coordinates → (0 : ℝ) ≤ selected j i)
    (hselectedSum : ∀ j, ∑ i ∈ coordinates, (selected j i : ℝ) = 1) :
    ∀ j, (∀ i ∈ coordinates, (0 : ℝ) ≤ rationalOptimizerIterate initial selected j i) ∧
      (∑ i ∈ coordinates, (rationalOptimizerIterate initial selected j i : ℝ)) = 1 := by
  intro j
  induction j with
  | zero => exact ⟨hinitial, hinitialSum⟩
  | succ j ih =>
    have hstep := congr_fun (rationalOptimizerIterate_cast_step initial selected j)
    constructor
    · intro i hi
      rw [hstep i]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr (frankWolfeStep_le_one j)) (ih.1 i hi))
        (mul_nonneg (frankWolfeStep_nonnegative j) (hselected j i hi))
    · simp_rw [hstep]
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, ih.2, hselectedSum]
      ring

/-- Convex feasibility is preserved by the actual rational iterates. -/
theorem rationalOptimizerIterate_mem {ι : Type*}
    (Q : Set (ι → ℝ)) (initial : ι → ℚ) (selected : ℕ → ι → ℚ)
    (hconvex : Convex ℝ Q) (hinitial : (fun i => (initial i : ℝ)) ∈ Q)
    (hselected : ∀ j, (fun i => (selected j i : ℝ)) ∈ Q) :
    ∀ j, (fun i => (rationalOptimizerIterate initial selected j i : ℝ)) ∈ Q := by
  intro j
  induction j with
  | zero => exact hinitial
  | succ j ih =>
    rw [rationalOptimizerIterate_cast_step]
    exact hconvex ih (hselected j) (sub_nonneg.mpr (frankWolfeStep_le_one j))
      (frankWolfeStep_nonnegative j) (by ring)

/-- Objective convergence of the exact rational implementation follows
from the proved smoothness and rational approximate-gradient choices. -/
theorem rational_optimizer_smoothed_gap_bound {ι : Type*} (coordinates : Finset ι)
    (σ error : ℝ) (linear best : ι → ℝ) (initial : ι → ℚ)
    (selected : ℕ → ι → ℚ) (approximateGradient : ℕ → ι → ℝ)
    (hinitial : ∀ i ∈ coordinates, (0 : ℝ) ≤ initial i)
    (hinitialSum : ∑ i ∈ coordinates, (initial i : ℝ) = 1)
    (hselected : ∀ j i, i ∈ coordinates → (0 : ℝ) ≤ selected j i)
    (hselectedSum : ∀ j, ∑ i ∈ coordinates, (selected j i : ℝ) = 1)
    (hbest : ∀ i ∈ coordinates, 0 ≤ best i)
    (hbestSum : ∑ i ∈ coordinates, best i = 1) (hσ : 0 < σ)
    (hgradient : ∀ j i, i ∈ coordinates →
      |approximateGradient j i - smoothedEntropyGradient σ linear
        (fun i => (rationalOptimizerIterate initial selected j i : ℝ)) i| ≤ error)
    (hchoose : ∀ j, (∑ i ∈ coordinates, approximateGradient j i * best i) ≤
      ∑ i ∈ coordinates, approximateGradient j i * (selected j i : ℝ)) :
    ∀ j, smoothedEntropyValue coordinates σ linear best - smoothedEntropyValue coordinates σ linear
      (fun i => (rationalOptimizerIterate initial selected (j + 1) i : ℝ)) ≤
        2 * error + 8 / (σ * ((j : ℝ) + 2)) := by
  have hprobability := rationalOptimizerIterate_probability coordinates initial selected
    hinitial hinitialSum hselected hselectedSum
  apply frank_wolfe_gap_bound σ error
    (fun j => smoothedEntropyValue coordinates σ linear best - smoothedEntropyValue coordinates σ linear
      (fun i => (rationalOptimizerIterate initial selected j i : ℝ))) hσ
  intro j
  rw [rationalOptimizerIterate_cast_step]
  exact smoothed_frank_wolfe_recurrence coordinates σ (frankWolfeStep j) error linear
    (fun i => (rationalOptimizerIterate initial selected j i : ℝ))
    (fun i => (selected j i : ℝ)) best (approximateGradient j)
    (hprobability j).1 (hselected j) hbest (hprobability j).2 (hselectedSum j) hbestSum hσ
    (frankWolfeStep_nonnegative j) (frankWolfeStep_le_one j) (hgradient j) (hchoose j)

/-- The actual rational gradient routine, including exact linear terms. -/


theorem rationalSmoothedGradient_precision {ι : Type*} (coordinates : Finset ι)
    (G : ℕ) (linear p : ι → ℚ) (hG : 4 ≤ G)
    (hp : ∀ i ∈ coordinates, (0 : ℝ) ≤ p i)
    (hpsum : ∑ i ∈ coordinates, (p i : ℝ) = 1) :
    ∀ i ∈ coordinates,
      |(rationalSmoothedGradient G linear p i : ℝ) -
        smoothedEntropyGradient (1 / (G : ℝ) ^ 50)
          (fun i => (linear i : ℝ)) (fun i => (p i : ℝ)) i| ≤ 1 / (G : ℝ) ^ 20 := by
  intro i hi
  have hinput : (1 / (G : ℝ) ^ 50) ≤ (p i + 1 / (G : ℚ) ^ 50 : ℚ) := by
    push_cast
    linarith [hp i hi]
  have hupper : ((p i + 1 / (G : ℚ) ^ 50 : ℚ) : ℝ) ≤ 1 + 1 / (G : ℝ) ^ 50 := by
    push_cast
    linarith [(single_le_sum hp hi).trans hpsum.le]
  have hlog := rationalLogApproximation_prescribed_precision
    (p i + 1 / (G : ℚ) ^ 50) G hG hinput hupper
  convert hlog using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [rationalSmoothedGradient, smoothedEntropyGradient]
  push_cast
  ring

/-- The prescribed number of exact rational updates reaches the true
entropy-objective precision, with no assumed analytic recurrence. -/
theorem rational_optimizer_true_gap_precision {ι : Type*} (coordinates : Finset ι)
    (G : ℕ) (linear initial : ι → ℚ) (selected : ℕ → ι → ℚ) (best : ι → ℝ)
    (hG : 4 ≤ G) (hdG : coordinates.card ≤ G)
    (hinitial : ∀ i ∈ coordinates, (0 : ℝ) ≤ initial i)
    (hinitialSum : ∑ i ∈ coordinates, (initial i : ℝ) = 1)
    (hselected : ∀ j i, i ∈ coordinates → (0 : ℝ) ≤ selected j i)
    (hselectedSum : ∀ j, ∑ i ∈ coordinates, (selected j i : ℝ) = 1)
    (hbest : ∀ i ∈ coordinates, 0 ≤ best i)
    (hbestSum : ∑ i ∈ coordinates, best i = 1)
    (hchoose : ∀ j,
      (∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (rationalOptimizerIterate initial selected j) i : ℝ) * best i) ≤
      ∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (rationalOptimizerIterate initial selected j) i : ℝ) * (selected j i : ℝ)) :
    entropyValue coordinates 1 (fun i => (linear i : ℝ)) best -
      entropyValue coordinates 1 (fun i => (linear i : ℝ))
        (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) ≤
          12 / (G : ℝ) ^ 20 := by
  let σ : ℝ := 1 / (G : ℝ) ^ 50
  have hG4 : (4 : ℝ) ≤ G := by exact_mod_cast hG
  have hGpos : (0 : ℝ) < G := by linarith
  have hσ : 0 < σ := by dsimp [σ] <;> positivity
  have hσ1 : σ ≤ 1 := by
    dsimp [σ]
    apply (div_le_one₀ (pow_pos hGpos _)).mpr
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ G)
  have hprobability := rationalOptimizerIterate_probability coordinates initial selected
    hinitial hinitialSum hselected hselectedSum
  have hgradient j := rationalSmoothedGradient_precision coordinates G linear
    (rationalOptimizerIterate initial selected j) hG (hprobability j).1 (hprobability j).2
  have hgap := rational_optimizer_smoothed_gap_bound coordinates σ (1 / (G : ℝ) ^ 20)
    (fun i => (linear i : ℝ)) best initial selected
    (fun j i => (rationalSmoothedGradient G linear (rationalOptimizerIterate initial selected j) i : ℝ))
    hinitial hinitialSum hselected hselectedSum hbest hbestSum hσ hgradient hchoose (G ^ 80 - 1)
  have hK : 1 ≤ G ^ 80 := by
    have hGnat : 0 < G := by omega
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 80 (Nat.ne_of_gt hGnat))
  rw [Nat.sub_add_cancel hK] at hgap
  have hindex : ((G ^ 80 - 1 : ℕ) : ℝ) + 2 = (G : ℝ) ^ 80 + 1 := by
    rw [Nat.cast_sub hK, Nat.cast_one, Nat.cast_pow]
    ring
  rw [hindex] at hgap
  have hbudget := optimizer_work_budget_gap (G : ℝ) hGpos
  have hsmoothed : smoothedEntropyValue coordinates σ (fun i => (linear i : ℝ)) best -
      smoothedEntropyValue coordinates σ (fun i => (linear i : ℝ))
        (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) ≤
          2 / (G : ℝ) ^ 20 + 8 / (G : ℝ) ^ 30 := by
    dsimp only [σ] at hgap ⊢
    have htwo : (2 : ℝ) * (1 / (G : ℝ) ^ 20) = 2 / (G : ℝ) ^ 20 := by ring
    rw [htwo] at hgap
    linarith
  have hbestSmoothing := finite_entropy_smoothing_bound coordinates best
    (fun i => (linear i : ℝ)) σ 1 hbest hbestSum hσ hσ1
  have hvalueSmoothing := finite_entropy_smoothing_bound coordinates
    (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ))
    (fun i => (linear i : ℝ)) σ 1 (hprobability _).1 (hprobability _).2 hσ hσ1
  have hbestSmooth : |smoothedEntropyValue coordinates σ (fun i => (linear i : ℝ)) best -
      entropyValue coordinates 1 (fun i => (linear i : ℝ)) best| ≤
      4 * coordinates.card * Real.sqrt σ := by
    simpa [smoothedEntropyValue, sum_add_distrib] using hbestSmoothing
  have hvalueSmooth : |smoothedEntropyValue coordinates σ (fun i => (linear i : ℝ))
      (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) -
        entropyValue coordinates 1 (fun i => (linear i : ℝ))
          (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ))| ≤
      4 * coordinates.card * Real.sqrt σ := by
    simpa [smoothedEntropyValue, sum_add_distrib] using hvalueSmoothing
  have htrue : entropyValue coordinates 1 (fun i => (linear i : ℝ)) best -
      entropyValue coordinates 1 (fun i => (linear i : ℝ))
        (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) ≤
      2 / (G : ℝ) ^ 20 + 8 / (G : ℝ) ^ 30 + 8 * coordinates.card * Real.sqrt σ := by
    have hb := abs_le.mp hbestSmooth
    have hv := abs_le.mp hvalueSmooth
    linarith
  have hroot : Real.sqrt σ = 1 / (G : ℝ) ^ 25 := optimizer_smoothing_root _ hGpos
  rw [hroot] at htrue
  have hdimension : (coordinates.card : ℝ) ≤ G := by exact_mod_cast hdG
  have hfinal := optimizer_explicit_gap_budget (G : ℝ) coordinates.card hG4 hdimension
  have hnorm : (8 : ℝ) * coordinates.card * (1 / (G : ℝ) ^ 25) =
      8 * coordinates.card / (G : ℝ) ^ 25 := by ring
  rw [hnorm] at htrue
  exact htrue.trans hfinal

/-- The final distance guarantee for the prescribed rational updates.
Only their concrete finite linearization choices remain as input. -/
theorem rational_optimizer_l1_precision {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (H G : ℕ) (linear initial : ι → ℚ)
    (selected : ℕ → ι → ℚ) (maximizer : ι → ℝ)
    (hH : 4 ≤ H) (hHG : H ≤ G) (hdG : coordinates.card ≤ G)
    (hconvex : Convex ℝ Q) (hinitialQ : (fun i => (initial i : ℝ)) ∈ Q)
    (hselectedQ : ∀ j, (fun i => (selected j i : ℝ)) ∈ Q)
    (hmaxQ : maximizer ∈ Q)
    (hinitial : ∀ i ∈ coordinates, (0 : ℝ) ≤ initial i)
    (hinitialSum : ∑ i ∈ coordinates, (initial i : ℝ) = 1)
    (hselected : ∀ j i, i ∈ coordinates → (0 : ℝ) ≤ selected j i)
    (hselectedSum : ∀ j, ∑ i ∈ coordinates, (selected j i : ℝ) = 1)
    (hmax : ∀ i ∈ coordinates, 0 < maximizer i)
    (hmaxSum : ∑ i ∈ coordinates, maximizer i = 1)
    (hmaximize : IsMaxOn (entropyValue coordinates 1 (fun i => (linear i : ℝ))) Q maximizer)
    (hchoose : ∀ j,
      (∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (rationalOptimizerIterate initial selected j) i : ℝ) * maximizer i) ≤
      ∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (rationalOptimizerIterate initial selected j) i : ℝ) * (selected j i : ℝ)) :
    (∑ i ∈ coordinates,
      |(rationalOptimizerIterate initial selected (G ^ 80) i : ℝ) - maximizer i|) ≤
        1 / (H : ℝ) ^ 3 := by
  have hG : 4 ≤ G := hH.trans hHG
  have hprobability := rationalOptimizerIterate_probability coordinates initial selected
    hinitial hinitialSum hselected hselectedSum (G ^ 80)
  have hmixture := rationalOptimizerIterate_mem Q initial selected
    hconvex hinitialQ hselectedQ (G ^ 80)
  have hgap := rational_optimizer_true_gap_precision coordinates G linear initial selected maximizer
    hG hdG hinitial hinitialSum hselected hselectedSum (fun i hi => (hmax i hi).le) hmaxSum hchoose
  have hdistance := entropy_gap_to_l1 coordinates Q 1 (fun i => (linear i : ℝ)) maximizer
    (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) hconvex
    hmaxQ hmixture hmax hprobability.1 hmaxSum hprobability.2 hmaximize
  have hmaxbound := hmaximize hmixture
  change entropyValue coordinates 1 (fun i => (linear i : ℝ))
      (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ)) ≤
    entropyValue coordinates 1 (fun i => (linear i : ℝ)) maximizer at hmaxbound
  have hnonnegative : 0 ≤ 2 * (coordinates.card : ℝ) *
      (entropyValue coordinates 1 (fun i => (linear i : ℝ)) maximizer -
        entropyValue coordinates 1 (fun i => (linear i : ℝ))
          (fun i => (rationalOptimizerIterate initial selected (G ^ 80) i : ℝ))) := by positivity
  have hsquared := pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _)) hdistance 2
  rw [Real.sq_sqrt hnonnegative] at hsquared
  apply optimizer_final_l1_precision (H : ℝ) G coordinates.card _ _
    (by exact_mod_cast hH) (by exact_mod_cast hHG) (Nat.cast_nonneg _)
    (by exact_mod_cast hdG) hsquared hgap

/-- Maximizing a finite list's linearization also maximizes it on the
real convex hull. -/
theorem finite_linearization_maximizes_convexHull {ι : Type*} (coordinates : Finset ι)
    (vertices : Set (ι → ℝ)) (gradient selected : ι → ℝ)
    (hchoose : ∀ p ∈ vertices,
      (∑ i ∈ coordinates, gradient i * p i) ≤ ∑ i ∈ coordinates, gradient i * selected i) :
    ∀ p ∈ convexHull ℝ vertices,
      (∑ i ∈ coordinates, gradient i * p i) ≤ ∑ i ∈ coordinates, gradient i * selected i := by
  let bound := ∑ i ∈ coordinates, gradient i * selected i
  have hconvex : Convex ℝ {p : ι → ℝ | (∑ i ∈ coordinates, gradient i * p i) ≤ bound} := by
    intro p hp q hq a b ha hb hab
    change (∑ i ∈ coordinates, gradient i * (a * p i + b * q i)) ≤ bound
    have hlinear : (∑ i ∈ coordinates, gradient i * (a * p i + b * q i)) =
        a * (∑ i ∈ coordinates, gradient i * p i) +
        b * (∑ i ∈ coordinates, gradient i * q i) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hlinear]
    have hp' := mul_le_mul_of_nonneg_left hp ha
    have hq' := mul_le_mul_of_nonneg_left hq hb
    have hbound : a * bound + b * bound = bound := by rw [← add_mul, hab, one_mul]
    linarith
  exact convexHull_min hchoose hconvex

/-- Executable finite rational comparisons, with the first listed
maximizer selected in a tie. The fallback only applies to an empty list. -/


theorem rationalLinearizationMaximizer_spec {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (gradient : ι → ℚ) (hvertices : vertices ≠ []) :
    rationalLinearizationMaximizer coordinates vertices gradient ∈ vertices ∧
      ∀ p ∈ vertices, (∑ i ∈ coordinates, gradient i * p i) ≤
        ∑ i ∈ coordinates, gradient i * rationalLinearizationMaximizer coordinates vertices gradient i := by
  unfold rationalLinearizationMaximizer
  cases harg : vertices.argmax (fun p => ∑ i ∈ coordinates, gradient i * p i) with
  | none => exact False.elim (hvertices (List.argmax_eq_none.mp harg))
  | some selected =>
    simp only [Option.getD_some]
    have hmem : selected ∈ vertices.argmax (fun p => ∑ i ∈ coordinates, gradient i * p i) := by
      rw [harg]
      simp
    exact ⟨List.argmax_mem hmem, fun p hp => List.le_of_mem_argmax
      (f := fun p : ι → ℚ => ∑ i ∈ coordinates, gradient i * p i) hp hmem⟩

theorem finiteRationalOptimizer_eq_iterate {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) :
    finiteRationalOptimizer coordinates vertices linear G j =
      rationalOptimizerIterate (vertices.headD (fun _ => 0))
        (finiteOptimizerSelection coordinates vertices linear G) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext i
    simp only [finiteRationalOptimizer, rationalOptimizerIterate]
    change (1 - 2 / ((j : ℚ) + 2)) * finiteRationalOptimizer coordinates vertices linear G j i +
        2 / ((j : ℚ) + 2) * finiteOptimizerSelection coordinates vertices linear G j i = _
    rw [ih]

/-- Every vector in the listed real convex hull is a probability vector. -/
theorem rationalVertexHull_probability {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ))
    (hvertices : ∀ p ∈ vertices,
      (∀ i ∈ coordinates, (0 : ℝ) ≤ p i) ∧ (∑ i ∈ coordinates, (p i : ℝ)) = 1) :
    ∀ p ∈ convexHull ℝ (rationalVertexSet vertices),
      (∀ i ∈ coordinates, 0 ≤ p i) ∧ (∑ i ∈ coordinates, p i) = 1 := by
  have hconvex : Convex ℝ {p : ι → ℝ |
      (∀ i ∈ coordinates, 0 ≤ p i) ∧ (∑ i ∈ coordinates, p i) = 1} := by
    intro p hp q hq a b ha hb hab
    constructor
    · intro i hi
      exact add_nonneg (mul_nonneg ha (hp.1 i hi)) (mul_nonneg hb (hq.1 i hi))
    · change (∑ i ∈ coordinates, (a * p i + b * q i)) = 1
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hp.2, hq.2, mul_one, mul_one]
      exact hab
  apply convexHull_min _ hconvex
  rintro _ ⟨p, hp, rfl⟩
  exact hvertices p hp

/-- Concrete finite vertex selection satisfies the required
linearization inequality against every real feasible mixture. -/
theorem finiteOptimizerSelection_maximizes {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ)
    (hvertices : vertices ≠ []) :
    ∀ best ∈ convexHull ℝ (rationalVertexSet vertices),
      (∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (finiteRationalOptimizer coordinates vertices linear G j) i : ℝ) * best i) ≤
      ∑ i ∈ coordinates, (rationalSmoothedGradient G linear
        (finiteRationalOptimizer coordinates vertices linear G j) i : ℝ) *
        (finiteOptimizerSelection coordinates vertices linear G j i : ℝ) := by
  apply finite_linearization_maximizes_convexHull
  rintro _ ⟨p, hp, rfl⟩
  have hspec := (rationalLinearizationMaximizer_spec coordinates vertices
    (rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j))
    hvertices).2 p hp
  dsimp only [finiteOptimizerSelection]
  exact_mod_cast hspec

/-- Accuracy of the executable rational optimizer at every positive
entropy maximizer of its listed action hull. -/
theorem finiteRationalOptimizer_l1_precision {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (H : ℕ) (maximizer : ι → ℝ)
    (hvertices : vertices ≠ []) (hH : 4 ≤ H)
    (hprobability : ∀ p ∈ vertices,
      (∀ i ∈ coordinates, (0 : ℝ) ≤ p i) ∧ (∑ i ∈ coordinates, (p i : ℝ)) = 1)
    (hmaxQ : maximizer ∈ convexHull ℝ (rationalVertexSet vertices))
    (hmax : ∀ i ∈ coordinates, 0 < maximizer i)
    (hmaximize : IsMaxOn (entropyValue coordinates 1 (fun i => (linear i : ℝ)))
      (convexHull ℝ (rationalVertexSet vertices)) maximizer) :
    (∑ i ∈ coordinates, |(finiteRationalOptimizer coordinates vertices linear
      (H + coordinates.card + 2) ((H + coordinates.card + 2) ^ 80) i : ℝ) - maximizer i|) ≤
        1 / (H : ℝ) ^ 3 := by
  let G := H + coordinates.card + 2
  let initial : ι → ℚ := vertices.headD (fun _ => 0)
  let selected := finiteOptimizerSelection coordinates vertices linear G
  have hinitialMem : initial ∈ vertices := by
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons p tail => exact List.mem_cons_self
  have hselectedMem j : selected j ∈ vertices :=
    (rationalLinearizationMaximizer_spec coordinates vertices
      (rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j))
      hvertices).1
  have hinitialQ : (fun i => (initial i : ℝ)) ∈ convexHull ℝ (rationalVertexSet vertices) :=
    subset_convexHull ℝ _ ⟨initial, hinitialMem, rfl⟩
  have hselectedQ j : (fun i => (selected j i : ℝ)) ∈ convexHull ℝ (rationalVertexSet vertices) :=
    subset_convexHull ℝ _ ⟨selected j, hselectedMem j, rfl⟩
  have hmaxProbability := rationalVertexHull_probability coordinates vertices hprobability maximizer hmaxQ
  have hchoose j := finiteOptimizerSelection_maximizes coordinates vertices linear G j
    hvertices maximizer hmaxQ
  simp_rw [finiteRationalOptimizer_eq_iterate] at hchoose ⊢
  exact rational_optimizer_l1_precision coordinates (convexHull ℝ (rationalVertexSet vertices)) H G
    linear initial selected maximizer hH (by dsimp [G]; omega) (by dsimp [G]; omega)
    (convex_convexHull ℝ _) hinitialQ hselectedQ hmaxQ
    (hprobability initial hinitialMem).1 (hprobability initial hinitialMem).2
    (fun j => (hprobability (selected j) (hselectedMem j)).1)
    (fun j => (hprobability (selected j) (hselectedMem j)).2)
    hmax hmaxProbability.2 hmaximize hchoose

/-- Averaging the finite action list gives a feasible vector positive
at every covered coordinate, including lists with repeated actions. -/
theorem rationalVertexHull_positive_witness {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (hvertices : vertices ≠ [])
    (hnonnegative : ∀ p ∈ vertices, ∀ i ∈ coordinates, (0 : ℝ) ≤ p i)
    (hcovered : ∀ i ∈ coordinates, ∃ p ∈ vertices, (0 : ℝ) < p i) :
    ∃ witness ∈ convexHull ℝ (rationalVertexSet vertices),
      ∀ i ∈ coordinates, 0 < witness i := by
  classical
  let listed := vertices.toFinset
  have hlisted : listed.Nonempty := (List.toFinset_nonempty_iff vertices).mpr hvertices
  have hcard : 0 < (listed.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hlisted)
  let weight : ℝ := 1 / listed.card
  have hweight : 0 < weight := by dsimp [weight] <;> positivity
  have hweightSum : (∑ _ ∈ listed, weight) = 1 := by
    simp only [sum_const, nsmul_eq_mul]
    dsimp only [weight]
    field_simp
  let witness : ι → ℝ := ∑ p ∈ listed, weight • (fun i => (p i : ℝ))
  refine ⟨witness, ?_, ?_⟩
  · exact (convex_convexHull ℝ (rationalVertexSet vertices)).sum_mem
      (fun _ _ => hweight.le) hweightSum (fun p hp =>
        subset_convexHull ℝ _ ⟨p, List.mem_toFinset.mp hp, rfl⟩)
  · intro i hi
    dsimp only [witness]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨p, hp, hpi⟩ := hcovered i hi
    exact sum_pos' (fun q hq => mul_nonneg hweight.le
      (hnonnegative q (List.mem_toFinset.mp hq) i hi))
      ⟨p, List.mem_toFinset.mpr hp, mul_pos hweight hpi⟩

/-- The finite optimizer accuracy theorem with exactly the manuscript's
probability and coordinate-coverage assumptions. The returned point is
the executable rational construction defined above. -/
theorem finite_entropy_optimizer {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (H : ℕ)
    (hvertices : vertices ≠ []) (hH : 4 ≤ H)
    (hprobability : ∀ p ∈ vertices,
      (∀ i ∈ coordinates, (0 : ℝ) ≤ p i) ∧ (∑ i ∈ coordinates, (p i : ℝ)) = 1)
    (hcovered : ∀ i ∈ coordinates, ∃ p ∈ vertices, (0 : ℝ) < p i) :
    ∃ maximizer ∈ convexHull ℝ (rationalVertexSet vertices),
      IsMaxOn (entropyValue coordinates 1 (fun i => (linear i : ℝ)))
        (convexHull ℝ (rationalVertexSet vertices)) maximizer ∧
      (∑ i ∈ coordinates, |(finiteRationalOptimizer coordinates vertices linear
        (H + coordinates.card + 2) ((H + coordinates.card + 2) ^ 80) i : ℝ) - maximizer i|) ≤
          1 / (H : ℝ) ^ 3 := by
  classical
  have hfinite : ({p : ι → ℚ | p ∈ vertices} : Set (ι → ℚ)).Finite := by
    simp
  have hcompact := (hfinite.image (fun p : ι → ℚ => fun i => (p i : ℝ))).isCompact_convexHull ℝ
  obtain ⟨witness, hwitnessQ, hwitness⟩ := rationalVertexHull_positive_witness coordinates vertices
    hvertices (fun p hp => (hprobability p hp).1) hcovered
  obtain ⟨maximizer, hmaxQ, hmaximize⟩ := exists_entropy_maximizer coordinates
    (convexHull ℝ (rationalVertexSet vertices)) 1 (fun i => (linear i : ℝ)) hcompact ⟨witness, hwitnessQ⟩
  have hmaxProbability := rationalVertexHull_probability coordinates vertices hprobability maximizer hmaxQ
  have hmax := entropy_hull_maximizer_positive coordinates (convexHull ℝ (rationalVertexSet vertices))
    1 (fun i => (linear i : ℝ)) maximizer witness (convex_convexHull ℝ _) hmaxQ hwitnessQ
    hmaxProbability.1 hwitness hmaximize
  exact ⟨maximizer, hmaxQ, hmaximize, finiteRationalOptimizer_l1_precision coordinates vertices linear H
    maximizer hvertices hH hprobability hmaxQ hmax hmaximize⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActionVectors
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual fixed-block action hull

Coordinates are precisely the child/state pairs occurring in a finite band.
Each action assigns its fixed rational child mass to one state per child.
This verifies the probability, coverage and block-mass hypotheses used by
the numerical optimizer and optimistic entropy regret.
-/

namespace EditApproximation

open Finset





theorem action_coordinate_mem {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) {action : β → σ} (haction : action ∈ band) (child : β) :
    (child, action child) ∈ bandCoordinates band := by
  apply mem_biUnion.mpr
  exact ⟨action, haction, mem_image.mpr ⟨child, mem_univ _, rfl⟩⟩

theorem actionVector_probability {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    {action : β → σ} (haction : action ∈ band) :
    (∀ coordinate ∈ bandCoordinates band, (0 : ℝ) ≤ actionVector mass action coordinate) ∧
      (∑ coordinate ∈ bandCoordinates band, (actionVector mass action coordinate : ℝ)) = 1 := by
  have htotal : (0 : ℚ) < ∑ child, mass child := sum_pos (fun child _ => hpos child) univ_nonempty
  constructor
  · intro coordinate _
    unfold actionVector
    split_ifs
    · exact_mod_cast (div_pos (hpos _) htotal).le
    · norm_num
  · have hsubset : (univ.image fun child => (child, action child)) ⊆ bandCoordinates band := by
      intro coordinate hc
      obtain ⟨child, _, rfl⟩ := mem_image.mp hc
      exact action_coordinate_mem band haction child
    have hsum : (∑ coordinate ∈ bandCoordinates band, (actionVector mass action coordinate : ℝ)) =
        ∑ coordinate ∈ univ.image (fun child => (child, action child)),
          (actionVector mass action coordinate : ℝ) := by
      symm
      apply sum_subset hsubset
      intro coordinate _ hnot
      have hne : coordinate.2 ≠ action coordinate.1 := by
        intro heq
        exact hnot (mem_image.mpr ⟨coordinate.1, mem_univ _, Prod.ext rfl heq.symm⟩)
      simp only [actionVector, ite_eq_right hne, Rat.cast_zero]
    rw [hsum, sum_image]
    · simp only [actionVector, ite_true, if_true, Rat.cast_div]
      rw [← sum_div]
      have hcast : (∑ child, (mass child : ℝ)) = ((∑ child, mass child : ℚ) : ℝ) := by
        norm_cast
      rw [hcast]
      exact div_self (by exact_mod_cast htotal.ne')
    · intro i _ j _ hij
      exact congrArg Prod.fst hij

theorem actionVector_coordinate_coverage {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : Finset (β → σ))
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child) :
    ∀ coordinate ∈ bandCoordinates band, ∃ action ∈ band,
      (0 : ℝ) < actionVector mass action coordinate := by
  intro coordinate hcoordinate
  obtain ⟨action, ha, hcoordinate⟩ := mem_biUnion.mp hcoordinate
  obtain ⟨child, _, heq⟩ := mem_image.mp hcoordinate
  subst coordinate
  refine ⟨action, ha, ?_⟩
  simp only [actionVector, ite_true, if_true]
  have htotal : (0 : ℚ) < ∑ child, mass child := sum_pos (fun child _ => hpos child) univ_nonempty
  exact_mod_cast div_pos (hpos child) htotal

theorem actionVector_block_mass {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) (mass : β → ℚ)
    {action : β → σ} (haction : action ∈ band) (child : β) :
    (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child,
      (actionVector mass action coordinate : ℝ)) =
        (mass child / (∑ i, mass i) : ℚ) := by
  rw [sum_eq_single (child, action child)]
  · simp only [actionVector, ite_true, if_true]
  · intro coordinate hc hne
    have hchild : coordinate.1 = child := (mem_filter.mp hc).2
    have hstate : coordinate.2 ≠ action child := by
      intro hstate
      exact hne (Prod.ext hchild hstate)
    simp only [actionVector, hchild, ite_eq_right hstate, Rat.cast_zero]
  · intro hnot
    exact False.elim (hnot (mem_filter.mpr ⟨action_coordinate_mem band haction child, rfl⟩))

theorem band_block_nonempty {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) (hband : band.Nonempty) (child : β) :
    ((bandCoordinates band).filter fun coordinate => coordinate.1 = child).Nonempty := by
  obtain ⟨action, ha⟩ := hband
  exact ⟨(child, action child), mem_filter.mpr ⟨action_coordinate_mem band ha child, rfl⟩⟩

theorem band_hull_block_mass {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : Finset (β → σ)) (mass : β → ℚ) (child : β)
    (p : β × σ → ℝ)
    (hp : p ∈ convexHull ℝ (rationalVertexSet (band.toList.map (actionVector mass)))) :
    (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child, p coordinate) =
      (mass child / (∑ i, mass i) : ℚ) := by
  let targetMass : ℝ := (mass child / (∑ i, mass i) : ℚ)
  have hconvex : Convex ℝ {q : β × σ → ℝ |
      (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child, q coordinate) =
        targetMass} := by
    intro x hx y hy a b _ _ hab
    change (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child,
      (a * x coordinate + b * y coordinate)) = targetMass
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hx, hy]
    calc
      a * targetMass + b * targetMass = (a + b) * targetMass := by ring
      _ = targetMass := by rw [hab, one_mul]
  have hsubset : rationalVertexSet (band.toList.map (actionVector mass)) ⊆
      {q : β × σ → ℝ |
        (∑ coordinate ∈ bandCoordinates band with coordinate.1 = child, q coordinate) =
          targetMass} := by
    rintro _ ⟨vertex, hv, rfl⟩
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact actionVector_block_mass band mass (mem_toList.mp ha) child
  exact convexHull_min hsubset hconvex hp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandRegret
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Regret of the computed rational band mixtures

The optimistic objective is computed in rational arithmetic. The finite
optimizer supplies every predicted vector used here; no maximization
oracle or unproved entropy-regret hypothesis appears in the conclusion.
-/

namespace EditApproximation

open Finset



theorem rationalOptimisticHistory_cast {ι : Type*} (κ : ℚ)
    (gain decrement : ℕ → ι → ℚ) (t : ℕ) (i : ι) :
    (rationalOptimisticHistory κ gain decrement t i : ℝ) =
      optimisticHistory (κ : ℝ) (fun j i => (gain j i : ℝ))
        (fun j i => (decrement j i : ℝ)) t i := by
  simp [rationalOptimisticHistory, optimisticHistory]



theorem rationalOnlineLinear_objective {ι : Type*} (coordinates : Finset ι)
    (η κ : ℚ) (gain decrement : ℕ → ι → ℚ) (t : ℕ) (p : ι → ℝ) :
    entropyValue coordinates 1
        (fun i => (rationalOnlineLinear η κ gain decrement t i : ℝ)) p =
      entropyValue coordinates (η : ℝ)
        (fun i => optimisticHistory (κ : ℝ) (fun j i => (gain j i : ℝ))
          (fun j i => (decrement j i : ℝ)) t i + (gain t i : ℝ)) p := by
  unfold entropyValue
  apply sum_congr rfl
  intro i _
  simp only [rationalOnlineLinear, Rat.cast_mul, Rat.cast_add,
    rationalOptimisticHistory_cast, one_mul]

/-- Fixed-block regret for the actual rational optimizer, with its
prescribed `G^80` iterations and `H^-3` numerical loss. -/
theorem computed_finite_block_entropy_regret {ι β : Type*} [Fintype β] [DecidableEq β]
    (coordinates : Finset ι) (block : ι → β) (vertices : List (ι → ℚ))
    (S H : ℕ) (η κ : ℚ) (rangeBound : ℝ)
    (gain decrement : ℕ → ι → ℚ) (comparator : ι → ℝ)
    (hvertices : vertices ≠ []) (hH : 4 ≤ H)
    (hprobability : ∀ p ∈ vertices,
      (∀ i ∈ coordinates, (0 : ℝ) ≤ p i) ∧ (∑ i ∈ coordinates, (p i : ℝ)) = 1)
    (hcovered : ∀ i ∈ coordinates, ∃ p ∈ vertices, (0 : ℝ) < p i)
    (hcQ : comparator ∈ convexHull ℝ (rationalVertexSet vertices))
    (hblocks : ∀ b, (coordinates.filter (fun i => block i = b)).Nonempty)
    (hblockMass : ∀ p ∈ convexHull ℝ (rationalVertexSet vertices),
      ∀ q ∈ convexHull ℝ (rationalVertexSet vertices), ∀ b,
      (∑ i ∈ coordinates with block i = b, p i) =
        ∑ i ∈ coordinates with block i = b, q i)
    (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) * rangeBound ≤ (κ : ℝ))
    (hdecrementNonneg : ∀ t < S, ∀ i ∈ coordinates, (0 : ℝ) ≤ decrement t i)
    (hrange : ∀ t < S, ∀ i ∈ coordinates, ∀ j ∈ coordinates,
      block i = block j → |(decrement t i : ℝ) - decrement t j| ≤ rangeBound)
    (hdecrement : ∀ i ∈ coordinates, ∑ t ∈ range S, (decrement t i : ℝ) ≤ 1)
    (hgain : ∀ t < S, ∀ i ∈ coordinates,
      -1 ≤ (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ∧
        (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ≤ 0) :
    (∑ t ∈ range S, ∑ i ∈ coordinates,
        ((gain t i : ℝ) + decrement t i) * comparator i) -
        Real.log coordinates.card / (η : ℝ) - 2 * (κ : ℝ) - (S : ℝ) / (H : ℝ) ^ 3 ≤
      ∑ t ∈ range S, ∑ i ∈ coordinates,
        ((gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i) *
          (computedOnlineVector coordinates vertices η κ gain decrement H t i : ℝ) := by
  classical
  have hfinite : ({p : ι → ℚ | p ∈ vertices} : Set (ι → ℚ)).Finite := by simp
  have hcompact := (hfinite.image (fun p : ι → ℚ => fun i => (p i : ℝ))).isCompact_convexHull ℝ
  obtain ⟨witness, hwQ, hw⟩ := rationalVertexHull_positive_witness coordinates vertices
    hvertices (fun p hp => (hprobability p hp).1) hcovered
  have hoptimizer (t : ℕ) := finite_entropy_optimizer coordinates vertices
    (rationalOnlineLinear η κ gain decrement t) H hvertices hH hprobability hcovered
  choose predicted hpred using hoptimizer
  have hpredMax t : IsMaxOn
      (entropyValue coordinates (η : ℝ)
        (fun i => optimisticHistory (κ : ℝ) (fun j i => (gain j i : ℝ))
          (fun j i => (decrement j i : ℝ)) t i + (gain t i : ℝ)))
      (convexHull ℝ (rationalVertexSet vertices)) (predicted t) := by
    intro q hq
    have hbound := (hpred t).2.1 hq
    change entropyValue coordinates 1
        (fun i => (rationalOnlineLinear η κ gain decrement t i : ℝ)) q ≤
      entropyValue coordinates 1
        (fun i => (rationalOnlineLinear η κ gain decrement t i : ℝ)) (predicted t) at hbound
    rw [rationalOnlineLinear_objective, rationalOnlineLinear_objective] at hbound
    exact hbound
  have hκhalfR : (κ : ℝ) ≤ 1 / 2 := by
    calc
      (κ : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hκhalf
      _ = 1 / 2 := by norm_num
  have hregret := finite_block_entropy_regret coordinates block
    (convexHull ℝ (rationalVertexSet vertices)) S (η : ℝ) (κ : ℝ) rangeBound
    (fun j i => (gain j i : ℝ)) (fun j i => (decrement j i : ℝ)) predicted
    witness comparator hcompact (convex_convexHull ℝ _) hwQ hcQ hw
    (rationalVertexHull_probability coordinates vertices hprobability) hblocks hblockMass
    (by exact_mod_cast hη) (by exact_mod_cast hκ) hκhalfR hηrange
    (fun t _ => (hpred t).1) (fun t _ => hpredMax t)
    hdecrementNonneg hrange hdecrement
  have hloss := sum_le_sum fun t (ht : t ∈ range S) =>
    bounded_gain_l1_approximation coordinates
      (fun i => (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i)
      (predicted t) (fun i => (computedOnlineVector coordinates vertices η κ gain decrement H t i : ℝ))
      (1 / (H : ℝ) ^ 3) (hgain t (mem_range.mp ht)) (hpred t).2.2
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hloss
  rw [mul_one_div] at hloss
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ListBandRegret
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regret and sampling for the literal finite band list

The numerical optimizer and exact sampler keep the same listed vertex
order. Passing to the finite set is used only for coordinate support and
convex-hull facts, never to reorder the executable optimizer.
-/

namespace EditApproximation

open Finset

theorem rationalVertexSet_band_list {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (mass : β → ℚ) :
    rationalVertexSet (band.map (actionVector mass)) =
      rationalVertexSet (band.toFinset.toList.map (actionVector mass)) := by
  unfold rationalVertexSet
  congr 1
  ext vertex
  simp only [Set.mem_ofPred_eq, List.mem_map, mem_toList, List.mem_toFinset]

/-- Actual finite-list specialization of the computed entropy optimizer. -/
theorem list_band_computed_entropy_regret_oai {β σ : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] [DecidableEq σ] (band : List (β → σ)) (hband : band ≠ [])
    (mass : β → ℚ) (hpos : ∀ child, 0 < mass child)
    (S H : ℕ) (η κ : ℚ) (rangeBound : ℝ)
    (gain decrement : ℕ → β × σ → ℚ) {comparison : β → σ} (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) * rangeBound ≤ (κ : ℝ))
    (hdecrementNonneg : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset, (0 : ℝ) ≤ decrement t i)
    (hrange : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset, ∀ j ∈ bandCoordinates band.toFinset,
      i.1 = j.1 → |(decrement t i : ℝ) - decrement t j| ≤ rangeBound)
    (hdecrement : ∀ i ∈ bandCoordinates band.toFinset, ∑ t ∈ range S, (decrement t i : ℝ) ≤ 1)
    (hgain : ∀ t < S, ∀ i ∈ bandCoordinates band.toFinset,
      -1 ≤ (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ∧
        (gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i ≤ 0) :
    (∑ t ∈ range S, ∑ i ∈ bandCoordinates band.toFinset,
        ((gain t i : ℝ) + decrement t i) * (actionVector mass comparison i : ℝ)) -
        Real.log (bandCoordinates band.toFinset).card / (η : ℝ) - 2 * (κ : ℝ) - (S : ℝ) / (H : ℝ) ^ 3 ≤
      ∑ t ∈ range S, ∑ i ∈ bandCoordinates band.toFinset,
        ((gain t i : ℝ) + (1 - (κ : ℝ)) * decrement t i) *
          (computedOnlineVector (bandCoordinates band.toFinset) (band.map (actionVector mass))
            η κ gain decrement H t i : ℝ) := by
  have hvertices : band.map (actionVector mass) ≠ [] := by
    cases band with
    | nil => exact False.elim (hband rfl)
    | cons action rest => simp
  have hcSet : comparison ∈ band.toFinset := List.mem_toFinset.mpr hc
  have hset := rationalVertexSet_band_list band mass
  apply computed_finite_block_entropy_regret (bandCoordinates band.toFinset) Prod.fst
    (band.map (actionVector mass)) S H η κ rangeBound gain decrement
    (fun i => (actionVector mass comparison i : ℝ)) hvertices hH
  · intro p hp
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hp
    exact actionVector_probability band.toFinset mass hpos (List.mem_toFinset.mpr ha)
  · intro i hi
    obtain ⟨action, ha, hpositive⟩ := actionVector_coordinate_coverage band.toFinset mass hpos i hi
    exact ⟨actionVector mass action, List.mem_map.mpr ⟨action, List.mem_toFinset.mp ha, rfl⟩, hpositive⟩
  · exact subset_convexHull ℝ _ ⟨actionVector mass comparison, List.mem_map.mpr ⟨comparison, hc, rfl⟩, rfl⟩
  · exact band_block_nonempty band.toFinset ⟨comparison, hcSet⟩
  · intro p hp q hq b
    rw [hset] at hp hq
    rw [band_hull_block_mass band.toFinset mass b p hp, band_hull_block_mass band.toFinset mass b q hq]
  · exact hη
  · exact hκ
  · exact hκhalf
  · exact hηrange
  · exact hdecrementNonneg
  · exact hrange
  · exact hdecrement
  · exact hgain

end EditApproximation

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.EditApproximation.list_band_computed_entropy_regret_oai.{u_1, u_2} := @OAI.EditApproximation.list_band_computed_entropy_regret_oai.{u_1, u_2}
