-- Prove2me | solution 1 for LSWCuttingPlane.ChasingZero.theorem_34
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T01:57:27.742335+00:00
-- url     : https://prove2.me/submissions/f32c23d5-ebcb-40fc-b931-8625ca5eb244

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting
import Theorems.Thm_LSWCuttingPlane_ChasingZero_exp_taylor_bound

open MeasureTheory
open LSWCuttingPlane.ChasingZero

namespace C0Aux

/-- symmetric potential -/
noncomputable def pot {m : ℕ} (α : ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ j, (Real.exp (α * x j) + Real.exp (-(α * x j)))

/-- coefficient of the martingale term -/
noncomputable def coef {m : ℕ} (α : ℝ) (x : Fin m → ℝ) (i j : Fin m) : ℝ :=
  if j = i then 0 else α * (Real.exp (α * x j) - Real.exp (-(α * x j)))

lemma coord_bound (α c x d : ℝ) (hα : 0 ≤ α) (hd : |d| ≤ c) :
    Real.exp (α * (x + d)) + Real.exp (-(α * (x + d))) ≤
      Real.exp (α * x) + Real.exp (-(α * x)) + α * (Real.exp (α * x) - Real.exp (-(α * x))) * d
        + 1 / 2 * α ^ 2 * d ^ 2 * Real.exp (α * c) * (Real.exp (α * x) + Real.exp (-(α * x))) := by
  have h1 := exp_taylor_bound.2 c d x α hd
  have h2 := exp_taylor_bound.2 c d x (-α) hd
  have e1 : α * (x + d) = α * x + α * d := by ring
  have e2 : -(α * (x + d)) = -α * x + -α * d := by ring
  have e3 : Real.exp (α * x + |α| * c) = Real.exp (α * x) * Real.exp (α * c) := by
    rw [abs_of_nonneg hα, Real.exp_add]
  have e4 : Real.exp (-α * x + |-α| * c) = Real.exp (-(α * x)) * Real.exp (α * c) := by
    rw [abs_neg, abs_of_nonneg hα, Real.exp_add]; ring_nf
  rw [e2, e1]
  rw [e3] at h1
  rw [e4] at h2
  have e5 : -α * x = -(α * x) := by ring
  rw [e5] at h2 ⊢
  nlinarith [h1, h2]

lemma abs_le_argmax {m : ℕ} [NeZero m] (v : Fin m → ℝ) (j : Fin m) :
    |v j| ≤ |v (argmaxAbs v)| := by
  have h := Finset.min'_mem (maxAbsCoords v) (maxAbsCoords_nonempty v)
  unfold maxAbsCoords at h
  rw [Finset.mem_filter] at h
  exact h.2 j

lemma two_cosh (a : ℝ) : Real.exp a + Real.exp (-a) = 2 * Real.cosh a := by
  rw [Real.cosh_eq]; ring

lemma kappa_bound (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    1 / 2 * (1 / (2 * (c + R))) ^ 2 * c ^ 2 * Real.exp (1 / (2 * (c + R)) * c) + 7 / 20 ≤
      Real.exp (-(1 / (2 * (c + R)) * (2 * R))) := by
  set α := 1 / (2 * (c + R)) with hα
  have hcr : 0 < c + R := by linarith
  have hαpos : 0 < α := by positivity
  set x := α * c with hx
  have hx0 : 0 < x := by positivity
  have hsum : α * c + α * R = 1 / 2 := by
    rw [hα]; field_simp
  have hx1 : x < 1 / 2 := by have : 0 < α * R := by positivity
                             linarith
  have key : -(α * (2 * R)) = 2 * x + (-1) := by linarith
  rw [key, Real.exp_add]
  have hexp1 : Real.exp 1 < 2.72 := by have := Real.exp_one_lt_d9; linarith
  have hem1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have hem1' : (0.36 : ℝ) ≤ Real.exp (-1) := by
    have hp : 0 < Real.exp (-1) := Real.exp_pos _
    nlinarith
  have h2x : 1 + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x); linarith
  have hhalf : Real.exp x ≤ 2 := by
    have h1 : Real.exp x ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hx1.le
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have hp : 0 < Real.exp (1 / 2) := Real.exp_pos _
    nlinarith
  have hsq : α ^ 2 * c ^ 2 = x ^ 2 := by rw [hx]; ring
  rw [show 1 / 2 * α ^ 2 * c ^ 2 * Real.exp x = 1 / 2 * x ^ 2 * Real.exp x by
    rw [← hsq]; ring]
  have hxe : 0 ≤ Real.exp x := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hhalf (sq_nonneg x), mul_le_mul h2x hem1' (by norm_num)
    (Real.exp_pos _).le]

lemma exp_abs_le (α t : ℝ) (hα : 0 ≤ α) :
    Real.exp (α * |t|) ≤ Real.exp (α * t) + Real.exp (-(α * t)) := by
  rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; linarith [Real.exp_pos (-(α * t))]
  · rw [h]; have : α * -t = -(α * t) := by ring
    rw [this]; linarith [Real.exp_pos (α * t)]

lemma step {m : ℕ} [NeZero m] (α c R : ℝ) (hα : 0 ≤ α) (hc : 0 ≤ c)
    (hκ : 1 / 2 * α ^ 2 * c ^ 2 * Real.exp (α * c) + 7 / 20 ≤ Real.exp (-(α * (2 * R))))
    (x d v : Fin m → ℝ) (hd : ∑ j, d j ^ 2 ≤ c ^ 2) (hv : ‖v - x‖ ≤ R) :
    pot α (Function.update (x + d) (argmaxAbs v) 0) ≤
      (1 - 7 / 20 / (m : ℝ)) * pot α x + 2 + ∑ j, coef α x (argmaxAbs v) j * d j := by
  set i := argmaxAbs v with hi
  set e : ℝ → ℝ := fun t => Real.exp (α * t) + Real.exp (-(α * t)) with he
  obtain ⟨js, -, hjs⟩ := Finset.exists_max_image Finset.univ (fun j => |x j|) Finset.univ_nonempty
  set E2 := e (x js) with hE2
  have hE2pos : 0 ≤ E2 := by
    simp only [hE2, he]; positivity
  -- (a) every coordinate term is at most E2
  have ha : ∀ j, e (x j) ≤ E2 := by
    intro j
    simp only [hE2, he, two_cosh]
    have : Real.cosh (α * x j) ≤ Real.cosh (α * x js) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hα]
      exact mul_le_mul_of_nonneg_left (hjs j (Finset.mem_univ _)) hα
    linarith
  -- (b) the reset coordinate is large
  have hvx : ∀ j, |v j - x j| ≤ R := by
    intro j
    have := norm_le_pi_norm (v - x) j
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  have hb : Real.exp (-(α * (2 * R))) * E2 ≤ e (x i) := by
    have hxi : |x js| - 2 * R ≤ |x i| := by
      have h1 := abs_le_argmax v js
      have h2 := hvx js
      have h3 := hvx i
      rw [← hi] at h1
      have h4 := abs_sub_abs_le_abs_sub (x js) (v js)
      have h5 := abs_sub_abs_le_abs_sub (v i) (x i)
      rw [abs_sub_comm] at h4
      linarith
    have hxi2 : |x i| ≤ |x js| := hjs i (Finset.mem_univ _)
    have hei : e (x i) = Real.exp (α * |x i|) + Real.exp (-(α * |x i|)) := by
      simp only [he, two_cosh]
      rw [show α * |x i| = |α * x i| by rw [abs_mul, abs_of_nonneg hα], Real.cosh_abs]
    have hejs : E2 = Real.exp (α * |x js|) + Real.exp (-(α * |x js|)) := by
      simp only [hE2, he, two_cosh]
      rw [show α * |x js| = |α * x js| by rw [abs_mul, abs_of_nonneg hα], Real.cosh_abs]
    rw [hei, hejs, mul_add, ← Real.exp_add, ← Real.exp_add]
    have t1 : Real.exp (-(α * (2 * R)) + α * |x js|) ≤ Real.exp (α * |x i|) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have t2 : Real.exp (-(α * (2 * R)) + -(α * |x js|)) ≤ Real.exp (-(α * |x i|)) := by
      apply Real.exp_le_exp.mpr
      have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hvx i)
      nlinarith
    linarith
  -- (c) coordinates of d are bounded
  have hdj : ∀ j, |d j| ≤ c := by
    intro j
    have : d j ^ 2 ≤ c ^ 2 := le_trans
      (Finset.single_le_sum (f := fun j => d j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)) hd
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  set K := 1 / 2 * α ^ 2 * Real.exp (α * c) * E2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  -- (d) termwise bound
  have hterm : ∀ j, e (Function.update (x + d) i 0 j) ≤
      e (x j) + coef α x i j * d j + K * d j ^ 2 + (if j = i then 2 - e (x i) else 0) := by
    intro j
    by_cases hj : j = i
    · rw [hj]
      simp only [Function.update_self, he, coef, if_true, mul_zero, Real.exp_zero, neg_zero]
      nlinarith [sq_nonneg (d i)]
    · rw [Function.update_of_ne hj]
      simp only [Pi.add_apply, coef, hj, if_false, add_zero]
      have h1 := coord_bound α c (x j) (d j) hα (hdj j)
      have h2 := ha j
      simp only [he] at h1 h2 ⊢
      have h3 : 1 / 2 * α ^ 2 * d j ^ 2 * Real.exp (α * c) *
          (Real.exp (α * x j) + Real.exp (-(α * x j))) ≤ K * d j ^ 2 := by
        rw [hK]
        have : 0 ≤ 1 / 2 * α ^ 2 * d j ^ 2 * Real.exp (α * c) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h2 this]
      linarith
  have hpot_upd : pot α (Function.update (x + d) i 0) = ∑ j, e (Function.update (x + d) i 0 j) := rfl
  have hpot : pot α x = ∑ j, e (x j) := rfl
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
  clear_value e
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _), ← Finset.mul_sum] at hsum
  -- pot x ≤ m * E2
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hpotle : pot α x ≤ m * E2 := by
    rw [hpot]
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ha j)
    simpa using this
  have hKc : K * ∑ j, d j ^ 2 ≤ (Real.exp (-(α * (2 * R))) - 7 / 20) * E2 := by
    calc K * ∑ j, d j ^ 2 ≤ K * c ^ 2 := mul_le_mul_of_nonneg_left hd hK0
      _ = (1 / 2 * α ^ 2 * c ^ 2 * Real.exp (α * c)) * E2 := by rw [hK]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE2pos
  have hfin : 7 / 20 / (m : ℝ) * pot α x ≤ 7 / 20 * E2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]; nlinarith
  rw [hpot_upd]
  nlinarith

lemma measurable_argmaxAbs {m : ℕ} [NeZero m] :
    Measurable (argmaxAbs : (Fin m → ℝ) → Fin m) := by
  apply measurable_to_countable'
  intro i
  have hset : argmaxAbs ⁻¹' {i} = (⋂ k, {v : Fin m → ℝ | |v k| ≤ |v i|}) ∩
      ⋂ j, {v : Fin m → ℝ | (∀ k, |v k| ≤ |v j|) → i ≤ j} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
    constructor
    · rintro rfl
      refine ⟨fun k => abs_le_argmax v k, fun j hj => Finset.min'_le _ _ ?_⟩
      simp only [maxAbsCoords, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj
    · rintro ⟨h1, h2⟩
      apply le_antisymm
      · exact Finset.min'_le _ _ (by
          simp only [maxAbsCoords, Finset.mem_filter, Finset.mem_univ, true_and]; exact h1)
      · apply Finset.le_min'
        intro j hj
        simp only [maxAbsCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact h2 j hj
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) (by fun_prop)
  · refine MeasurableSet.iInter fun j => ?_
    by_cases hij : i ≤ j
    · simp [hij]
    · have : {v : Fin m → ℝ | (∀ k, |v k| ≤ |v j|) → i ≤ j} =
          (⋂ k, {v : Fin m → ℝ | |v k| ≤ |v j|})ᶜ := by
        ext v; simp [hij]
      rw [this]
      exact (MeasurableSet.iInter fun k => measurableSet_le (by fun_prop) (by fun_prop)).compl

lemma continuous_pot {m : ℕ} (α : ℝ) : Continuous (pot (m := m) α) := by
  unfold pot; fun_prop

lemma traj_succ {Ω : Type*} {m : ℕ} [NeZero m] (Δ y : ℕ → Ω → Fin m → ℝ) (n : ℕ) (ω : Ω) :
    traj Δ y (n + 1) ω = Function.update (traj Δ y n ω + Δ n ω) (argmaxAbs (y n ω)) 0 := rfl

lemma traj_zero {Ω : Type*} {m : ℕ} [NeZero m] (Δ y : ℕ → Ω → Fin m → ℝ) (ω : Ω) :
    traj Δ y 0 ω = 0 := rfl

lemma measurableSet_argmax_eq {Ω : Type*} {m : ℕ} [NeZero m] {mΩ : MeasurableSpace Ω}
    (v : Ω → Fin m → ℝ) (hv : Measurable v) (j : Fin m) :
    MeasurableSet {ω | j = argmaxAbs (v ω)} := by
  have := (measurable_argmaxAbs.comp hv) (measurableSet_singleton j)
  convert this using 1
  ext ω; simp [eq_comm]

lemma update_measurable {Ω : Type*} {m : ℕ} [NeZero m] (mΩ : MeasurableSpace Ω)
    (a d v : Ω → Fin m → ℝ) (ha : Measurable a) (hd : Measurable d) (hv : Measurable v) :
    Measurable (fun ω => Function.update (a ω + d ω) (argmaxAbs (v ω)) 0) := by
  apply measurable_pi_lambda
  intro j
  have : (fun ω => Function.update (a ω + d ω) (argmaxAbs (v ω)) 0 j) =
      fun ω => if j = argmaxAbs (v ω) then 0 else a ω j + d ω j := by
    ext ω; rw [Function.update_apply]; rfl
  rw [this]
  refine Measurable.ite (measurableSet_argmax_eq _ hv j) measurable_const ?_
  exact ((measurable_pi_apply j).comp ha).add ((measurable_pi_apply j).comp hd)

lemma traj_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : MeasureTheory.Filtration ℕ mΩ)
    {m : ℕ} [NeZero m] (Δ y : ℕ → Ω → Fin m → ℝ)
    (hΔ : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Δ k))
    (hy : ∀ k, StronglyMeasurable[ℱ k] (y k)) :
    ∀ n, Measurable[ℱ n] (traj Δ y n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have ih' : Measurable[ℱ (n + 1)] (traj Δ y n) := ih.mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hy' : Measurable[ℱ (n + 1)] (y n) := (hy n).measurable.mono (ℱ.mono (Nat.le_succ n)) le_rfl
    have hΔ' : Measurable[ℱ (n + 1)] (Δ n) := (hΔ n).measurable
    exact update_measurable (ℱ (n + 1)) _ _ _ ih' hΔ' hy'

lemma traj_bound {Ω : Type*} {m : ℕ} [NeZero m] (Δ y : ℕ → Ω → Fin m → ℝ) (c : ℝ)
    (hΔ : ∀ k ω j, |Δ k ω j| ≤ c) (hc : 0 ≤ c) :
    ∀ n ω j, |traj Δ y n ω j| ≤ n * c := by
  intro n
  induction n with
  | zero => intro ω j; simp [traj_zero]
  | succ n ih =>
    intro ω j
    rw [traj_succ, Function.update_apply]
    split_ifs
    · simp only [abs_zero]; positivity
    · simp only [Pi.add_apply]
      have := abs_add_le (traj Δ y n ω j) (Δ n ω j)
      have := ih ω j
      have := hΔ n ω j
      push_cast
      linarith

lemma pot_nonneg {m : ℕ} (α : ℝ) (x : Fin m → ℝ) : 0 ≤ pot α x := by
  unfold pot; positivity

lemma pot_le {m : ℕ} (α B : ℝ) (hα : 0 ≤ α) (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ B) :
    pot α x ≤ m * (2 * Real.exp (α * B)) := by
  unfold pot
  have h : ∀ j, Real.exp (α * x j) + Real.exp (-(α * x j)) ≤ 2 * Real.exp (α * B) := by
    intro j
    have h1 : α * x j ≤ α * B := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hx j)) hα
    have h2 : -(α * x j) ≤ α * B := by
      have := mul_le_mul_of_nonneg_left (le_trans (neg_le_abs (x j)) (hx j)) hα
      linarith
    linarith [Real.exp_le_exp.mpr h1, Real.exp_le_exp.mpr h2]
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h j)
  simpa using this

lemma coef_abs_le {m : ℕ} (α B : ℝ) (hα : 0 ≤ α) (x : Fin m → ℝ) (hx : ∀ j, |x j| ≤ B)
    (i j : Fin m) : |coef α x i j| ≤ α * (2 * Real.exp (α * B)) := by
  unfold coef
  split_ifs
  · simp only [abs_zero]; positivity
  · have h1 : α * x j ≤ α * B := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hx j)) hα
    have h2 : -(α * x j) ≤ α * B := by
      have := mul_le_mul_of_nonneg_left (le_trans (neg_le_abs (x j)) (hx j)) hα
      linarith
    have e1 := Real.exp_le_exp.mpr h1
    have e2 := Real.exp_le_exp.mpr h2
    have p1 := Real.exp_pos (α * x j)
    have p2 := Real.exp_pos (-(α * x j))
    rw [abs_mul, abs_of_nonneg hα]
    apply mul_le_mul_of_nonneg_left _ hα
    rw [abs_le]; constructor <;> linarith

lemma coef_measurable {Ω : Type*} {m : ℕ} [NeZero m] (mΩ : MeasurableSpace Ω) (α : ℝ)
    (a v : Ω → Fin m → ℝ) (ha : Measurable a) (hv : Measurable v) (j : Fin m) :
    Measurable (fun ω => coef α (a ω) (argmaxAbs (v ω)) j) := by
  unfold coef
  refine Measurable.ite (measurableSet_argmax_eq _ hv j) measurable_const ?_
  have hj : Measurable (fun ω => a ω j) := (measurable_pi_apply j).comp ha
  fun_prop

lemma expect_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) {m : ℕ} [NeZero m] (c R : ℝ) (hc : 0 < c) (hR : 0 < R)
    (Δ y : ℕ → Ω → Fin m → ℝ)
    (hΔ_adapted : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Δ k))
    (hy_adapted : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hΔ_mean : ∀ k i, μ[fun ω => Δ k ω i | ℱ k] =ᵐ[μ] 0)
    (hΔ_norm : ∀ k ω, ∑ i, (Δ k ω i) ^ 2 ≤ c ^ 2)
    (hy_close : ∀ k ω, ‖y k ω - traj Δ y k ω‖ ≤ R) :
    ∀ n, Integrable (fun ω => pot (1 / (2 * (c + R))) (traj Δ y n ω)) μ ∧
      ∫ ω, pot (1 / (2 * (c + R))) (traj Δ y n ω) ∂μ ≤ 40 * m / 7 := by
  have hκ := kappa_bound c R hc hR
  set α := 1 / (2 * (c + R)) with hαdef
  have hα : 0 ≤ α := by positivity
  have hΔabs : ∀ k ω j, |Δ k ω j| ≤ c := by
    intro k ω j
    have : Δ k ω j ^ 2 ≤ c ^ 2 := le_trans
      (Finset.single_le_sum (f := fun j => Δ k ω j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ j)) (hΔ_norm k ω)
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hb := traj_bound Δ y c hΔabs hc.le
  have hTm := traj_measurable ℱ Δ y hΔ_adapted hy_adapted
  have hTm' : ∀ n, Measurable (traj Δ y n) := fun n => (hTm n).mono (ℱ.le n) le_rfl
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hPint : ∀ n, Integrable (fun ω => pot α (traj Δ y n ω)) μ := by
    intro n
    refine Integrable.of_bound ((continuous_pot α).measurable.comp (hTm' n)).aestronglyMeasurable
      (m * (2 * Real.exp (α * (n * c)))) (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (pot_nonneg _ _)]
    exact pot_le α _ hα _ (hb n ω)
  have hΔint : ∀ n j, Integrable (fun ω => Δ n ω j) μ := by
    intro n j
    refine Integrable.of_bound ?_ c (ae_of_all _ (fun ω => ?_))
    · exact ((measurable_pi_apply j).comp ((hΔ_adapted n).measurable.mono (ℱ.le (n + 1)) le_rfl)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hΔabs n ω j
  have hCm : ∀ n j, Measurable[ℱ n] (fun ω => coef α (traj Δ y n ω) (argmaxAbs (y n ω)) j) :=
    fun n j => coef_measurable (ℱ n) α _ _ (hTm n) (hy_adapted n).measurable j
  have hprod : ∀ n j, Integrable (fun ω => coef α (traj Δ y n ω) (argmaxAbs (y n ω)) j * Δ n ω j) μ := by
    intro n j
    refine Integrable.bdd_mul (c := α * (2 * Real.exp (α * (n * c)))) (hΔint n j)
      ((hCm n j).mono (ℱ.le n) le_rfl).aestronglyMeasurable (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs]; exact coef_abs_le α _ hα _ (hb n ω) _ _
  have hzero : ∀ n j, ∫ ω, coef α (traj Δ y n ω) (argmaxAbs (y n ω)) j * Δ n ω j ∂μ = 0 := by
    intro n j
    set f := fun ω => coef α (traj Δ y n ω) (argmaxAbs (y n ω)) j with hf
    set g := fun ω => Δ n ω j with hg
    have h1 : μ[f * g | ℱ n] =ᵐ[μ] f * μ[g | ℱ n] :=
      condExp_mul_of_stronglyMeasurable_left (hCm n j).stronglyMeasurable (hprod n j) (hΔint n j)
    have h2 : f * μ[g | ℱ n] =ᵐ[μ] 0 := by
      filter_upwards [hΔ_mean n j] with ω hω
      simp only [Pi.mul_apply, Pi.zero_apply]
      rw [← hg] at hω
      rw [hω]; simp
    calc ∫ ω, f ω * g ω ∂μ = ∫ ω, (f * g) ω ∂μ := rfl
      _ = ∫ ω, (μ[f * g | ℱ n]) ω ∂μ := (integral_condExp (ℱ.le n)).symm
      _ = ∫ ω, (0 : Ω → ℝ) ω ∂μ := integral_congr_ae (h1.trans h2)
      _ = 0 := by simp
  have hstep : ∀ n ω, pot α (traj Δ y (n + 1) ω) ≤ (1 - 7 / 20 / (m : ℝ)) * pot α (traj Δ y n ω) + 2 +
      ∑ j, coef α (traj Δ y n ω) (argmaxAbs (y n ω)) j * Δ n ω j := by
    intro n ω
    rw [traj_succ]
    exact step α c R hα hc.le hκ _ _ _ (hΔ_norm n ω) (hy_close n ω)
  have hrec : ∀ n, ∫ ω, pot α (traj Δ y (n + 1) ω) ∂μ ≤
      (1 - 7 / 20 / (m : ℝ)) * ∫ ω, pot α (traj Δ y n ω) ∂μ + 2 := by
    intro n
    have hint2 : Integrable (fun ω => (1 - 7 / 20 / (m : ℝ)) * pot α (traj Δ y n ω) + 2 +
        ∑ j, coef α (traj Δ y n ω) (argmaxAbs (y n ω)) j * Δ n ω j) μ :=
      (((hPint n).const_mul _).add (integrable_const 2)).add
        (integrable_finsetSum _ (fun j _ => hprod n j))
    refine (integral_mono (hPint (n + 1)) hint2 (fun ω => hstep n ω)).trans (le_of_eq ?_)
    have hA : Integrable (fun ω => (1 - 7 / 20 / (m : ℝ)) * pot α (traj Δ y n ω) + 2) μ :=
      ((hPint n).const_mul _).add (integrable_const 2)
    have hB : Integrable (fun ω => ∑ j, coef α (traj Δ y n ω) (argmaxAbs (y n ω)) j * Δ n ω j) μ :=
      integrable_finsetSum _ (fun j _ => hprod n j)
    have hC : Integrable (fun ω => (1 - 7 / 20 / (m : ℝ)) * pot α (traj Δ y n ω)) μ :=
      (hPint n).const_mul _
    have e1 := integral_add hA hB
    have e2 := integral_add hC (integrable_const (μ := μ) (2 : ℝ))
    have e3 := integral_finsetSum (μ := μ) Finset.univ (fun j _ => hprod n j)
    try simp only at e1 e2 e3
    rw [e1, e2, e3, integral_const_mul]
    simp [hzero]
  intro n
  refine ⟨hPint n, ?_⟩
  induction n with
  | zero =>
    have : ∀ ω, pot α (traj Δ y 0 ω) = 2 * m := by
      intro ω; rw [traj_zero]; unfold pot; simp; ring
    simp only [this, integral_const, probReal_univ, one_smul]
    linarith
  | succ n ih =>
    refine (hrec n).trans ?_
    have hq0 : 0 ≤ 1 - 7 / 20 / (m : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    have := mul_le_mul_of_nonneg_left ih hq0
    have e : (1 - 7 / 20 / (m : ℝ)) * (40 * m / 7) + 2 = 40 * m / 7 := by
      field_simp; ring
    linarith

end C0Aux

open C0Aux in
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) {m : ℕ} [NeZero m] (c R p : ℝ) (hc : 0 < c) (hR : 0 < R)
    (hp : 0 < p) (hp1 : p ≤ 1) (Δ y : ℕ → Ω → Fin m → ℝ)
    (hΔ_adapted : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Δ k))
    (hy_adapted : ∀ k, StronglyMeasurable[ℱ k] (y k))
    (hΔ_mean : ∀ k i, μ[fun ω => Δ k ω i | ℱ k] =ᵐ[μ] 0)
    (hΔ_norm : ∀ k ω, ∑ i, (Δ k ω i) ^ 2 ≤ c ^ 2)
    (hy_close : ∀ k ω, ‖y k ω - traj Δ y k ω‖ ≤ R) :
    ENNReal.ofReal (1 - p) ≤
      μ {ω | ∀ k : ℕ, ‖traj Δ y k ω‖ ≤
        2 * (c + R) * Real.log (4 * (m : ℝ) * ((k : ℝ) + 1) ^ 2 / p)} := by
  have hE := expect_bound μ ℱ c R hc hR Δ y hΔ_adapted hy_adapted hΔ_mean hΔ_norm hy_close
  set α := 1 / (2 * (c + R)) with hαdef
  have hcR : 0 < c + R := by linarith
  have hα : 0 < α := by positivity
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  set lam : ℕ → ℝ := fun n => 4 * (m : ℝ) * ((n : ℝ) + 1) ^ 2 / p with hlam
  have hlam1 : ∀ n, 1 ≤ lam n := by
    intro n
    simp only [hlam]
    rw [le_div_iff₀ hp]
    have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      nlinarith
    nlinarith
  have hlampos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam1 n)
  set bad : ℕ → Set Ω := fun n => {ω | ¬ ‖traj Δ y n ω‖ ≤ 2 * (c + R) * Real.log (lam n)} with hbad
  have hsub : ∀ n, bad n ⊆ {ω | lam n ≤ pot α (traj Δ y n ω)} := by
    intro n ω hω
    by_contra hlt
    simp only [Set.mem_ofPred_eq, not_le] at hlt
    apply hω
    have hlog : 0 ≤ Real.log (lam n) := Real.log_nonneg (hlam1 n)
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    rw [Real.norm_eq_abs]
    have h1 : Real.exp (α * |traj Δ y n ω j|) ≤ pot α (traj Δ y n ω) := by
      refine (exp_abs_le α _ hα.le).trans ?_
      unfold pot
      exact Finset.single_le_sum (f := fun j => Real.exp (α * traj Δ y n ω j) +
        Real.exp (-(α * traj Δ y n ω j))) (fun j _ => by positivity) (Finset.mem_univ j)
    have h2 : α * |traj Δ y n ω j| < Real.log (lam n) :=
      (Real.lt_log_iff_exp_lt (hlampos n)).mpr (h1.trans_lt hlt)
    have h3 : |traj Δ y n ω j| = 2 * (c + R) * (α * |traj Δ y n ω j|) := by
      rw [hαdef]; field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2.le (by positivity)
  have hbad0 : ∀ ω, ω ∉ bad 0 := by
    intro ω hω
    apply hω
    rw [traj_zero, norm_zero]
    have := Real.log_nonneg (hlam1 0)
    positivity
  have hmeas : ∀ n, μ (bad (n + 1)) ≤ ENNReal.ofReal (10 / 7 * p * (1 / ((n : ℝ) + 2) ^ 2)) := by
    intro n
    refine (measure_mono (hsub (n + 1))).trans ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), ← measureReal_def]
    apply ENNReal.ofReal_le_ofReal
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
      (ae_of_all _ (fun ω => pot_nonneg α (traj Δ y (n + 1) ω))) (hE (n + 1)).1 (lam (n + 1))
    have hb := (hE (n + 1)).2
    set S := μ.real {x | lam (n + 1) ≤ pot α (traj Δ y (n + 1) x)} with hS
    have hl : lam (n + 1) = 4 * (m : ℝ) * ((n : ℝ) + 2) ^ 2 / p := by
      simp only [hlam]; push_cast; ring
    have hn2 : (0 : ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
    have hmr : 0 ≤ S := measureReal_nonneg
    have key : lam (n + 1) * S ≤ 40 * m / 7 := hmk.trans hb
    rw [hl] at key
    have hm0 : (0 : ℝ) < m := by linarith
    rw [show 10 / 7 * p * (1 / ((n : ℝ) + 2) ^ 2) = (40 * m / 7) / (4 * (m : ℝ) * ((n : ℝ) + 2) ^ 2 / p) by
      field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- summation
  have hzeta := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  have hzeta' : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have e : ∑ i ∈ Finset.range 2, 1 / ((i : ℕ) : ℝ) ^ 2 = 1 := by
      norm_num [Finset.sum_range_succ]
    rw [e] at hzeta
    have hf : (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) = fun n : ℕ => 1 / (((n + 2 : ℕ)) : ℝ) ^ 2 := by
      ext n; simp
    rw [hf]; exact hzeta
  have hsum := hzeta'.mul_left (10 / 7 * p)
  have hnn : ∀ n : ℕ, 0 ≤ 10 / 7 * p * (1 / ((n : ℝ) + 2) ^ 2) := fun n => by positivity
  have hbadsum : μ (⋃ n, bad (n + 1)) ≤ ENNReal.ofReal p := by
    refine (measure_iUnion_le _).trans ?_
    refine (ENNReal.tsum_le_tsum hmeas).trans ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]
    apply ENNReal.ofReal_le_ofReal
    have := Real.pi_lt_d2
    have := Real.pi_pos
    have hpi : Real.pi ^ 2 / 6 - 1 ≤ 7 / 10 := by nlinarith
    nlinarith
  set good := {ω | ∀ k : ℕ, ‖traj Δ y k ω‖ ≤
        2 * (c + R) * Real.log (4 * (m : ℝ) * ((k : ℝ) + 1) ^ 2 / p)} with hgood
  have hcompl : goodᶜ ⊆ ⋃ n, bad (n + 1) := by
    intro ω hω
    simp only [hgood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨k, hk⟩ := hω
    rcases k with _ | n
    · exact absurd hk (hbad0 ω)
    · exact Set.mem_iUnion.mpr ⟨n, hk⟩
  have h1 : (1 : ENNReal) ≤ μ good + ENNReal.ofReal p := by
    calc (1 : ENNReal) = μ (good ∪ goodᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ μ good + μ goodᶜ := measure_union_le _ _
      _ ≤ μ good + ENNReal.ofReal p := by
        gcongr
        exact (measure_mono hcompl).trans hbadsum
  rw [ENNReal.ofReal_sub _ hp.le, ENNReal.ofReal_one]
  exact tsub_le_iff_right.mpr h1
