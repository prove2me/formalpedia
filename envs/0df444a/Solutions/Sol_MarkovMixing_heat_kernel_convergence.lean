-- Prove2me | solution 1 for MarkovMixing.heat_kernel_convergence
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T20:33:43.532513+00:00
-- url     : https://prove2.me/submissions/2aa0b3cf-e89b-403a-9f6e-3a54d39b6885

import Definitions.Def_mm_continuous
import Theorems.Thm_MarkovMixing_tv_eq_half_l1
import Theorems.Thm_MarkovMixing_convergence_theorem
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open scoped BigOperators
open MarkovMixing

namespace Heat

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Poisson weight `e^{-u} u^k / k!`. -/
noncomputable def pw (u : ℝ) (k : ℕ) : ℝ := Real.exp (-u) * u ^ k / (Nat.factorial k)

lemma pw_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) : 0 ≤ pw u k := by
  unfold pw
  positivity

lemma pw_pos {u : ℝ} (hu : 0 < u) (k : ℕ) : 0 < pw u k := by
  unfold pw
  positivity

lemma hasSum_pw_mul (u lam : ℝ) :
    HasSum (fun k : ℕ => pw u k * lam ^ k) (Real.exp (-u) * Real.exp (u * lam)) := by
  have h0 : HasSum (fun k : ℕ => (u * lam) ^ k / (Nat.factorial k))
      (Real.exp (u * lam)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (u * lam)
  have h1 := h0.mul_left (Real.exp (-u))
  have hfun : (fun k : ℕ => pw u k * lam ^ k)
      = fun k : ℕ => Real.exp (-u) * ((u * lam) ^ k / (Nat.factorial k)) := by
    funext k
    unfold pw
    rw [mul_pow]
    ring
  rw [hfun]
  exact h1

lemma hasSum_pw (u : ℝ) : HasSum (pw u) 1 := by
  have h := hasSum_pw_mul u 1
  have hfun : (fun k : ℕ => pw u k * (1 : ℝ) ^ k) = pw u := by
    funext k; simp
  rw [hfun] at h
  have : Real.exp (-u) * Real.exp (u * 1) = 1 := by
    rw [mul_one, ← Real.exp_add]
    simp
  rwa [this] at h

lemma summable_pw {u : ℝ} : Summable (pw u) := (hasSum_pw u).summable

/-- A `[0,1]`-valued sequence weighted by Poisson weights is absolutely
summable. -/
lemma summable_pw_mul {u : ℝ} (hu : 0 ≤ u) (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    Summable (fun k => ‖pw u k * f k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (summable_pw (u := u))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pw_nonneg hu k)]
  calc pw u k * |f k| ≤ pw u k * 1 :=
        mul_le_mul_of_nonneg_left (hf k) (pw_nonneg hu k)
    _ = pw u k := mul_one _

/-- The convolution identity for Poisson weights. -/
lemma pw_conv (s t : ℝ) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, pw s p.1 * pw t p.2 = pw (s + t) n := by
  have hbin : (s + t) ^ n
      = ∑ p ∈ Finset.antidiagonal n, (n.choose p.1 : ℝ) * (s ^ p.1 * t ^ p.2) := by
    rw [(Commute.all s t).add_pow' n]
    exact Finset.sum_congr rfl fun p _ => by rw [nsmul_eq_mul]
  have hexp : Real.exp (-s) * Real.exp (-t) = Real.exp (-(s + t)) := by
    rw [← Real.exp_add]
    ring_nf
  unfold pw
  rw [hbin, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have h1 : p.1 ≤ n := by omega
  have hfac : (n.choose p.1 : ℝ) * (Nat.factorial p.1 : ℝ) * (Nat.factorial p.2 : ℝ)
      = (Nat.factorial n : ℝ) := by
    have h2 : n - p.1 = p.2 := by omega
    have h3 := Nat.choose_mul_factorial_mul_factorial h1
    rw [h2] at h3
    exact_mod_cast h3
  have hp1 : (Nat.factorial p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp2 : (Nat.factorial p.2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpn : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hC : (n.choose p.1 : ℝ) ≠ 0 := by
    have := Nat.choose_pos h1
    exact_mod_cast this.ne'
  rw [← hexp, ← hfac]
  field_simp

section Kernel

variable {P : Matrix V V ℝ}

lemma pow_entry_nonneg (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma pow_row_sum (hP : IsStochastic P) : ∀ (t : ℕ) (x : V), ∑ y, (P ^ t) x y = 1 := by
  intro t
  induction t with
  | zero => intro x; simp [Matrix.one_apply]
  | succ t ih =>
    intro x
    have h : ∀ y : V, (P ^ (t + 1)) x y = ∑ z, (P ^ t) x z * P z y := by
      intro y; rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_comm]
    have e : ∀ z : V, ∑ y, (P ^ t) x z * P z y = (P ^ t) x z := by
      intro z; rw [← Finset.mul_sum, hP.2 z, mul_one]
    rw [Finset.sum_congr rfl (fun z _ => e z), ih x]

lemma pow_entry_le_one (hP : IsStochastic P) (t : ℕ) (x y : V) : (P ^ t) x y ≤ 1 := by
  have h1 : (P ^ t) x y ≤ ∑ z, (P ^ t) x z :=
    Finset.single_le_sum (f := fun z => (P ^ t) x z)
      (fun z _ => pow_entry_nonneg hP t x z) (Finset.mem_univ y)
  rw [pow_row_sum hP t x] at h1
  exact h1

lemma pow_abs_le_one (hP : IsStochastic P) (x y : V) (k : ℕ) : |(P ^ k) x y| ≤ 1 := by
  rw [abs_of_nonneg (pow_entry_nonneg hP k x y)]
  exact pow_entry_le_one hP k x y

lemma summable_norm_heat (hP : IsStochastic P) {t : ℝ} (ht : 0 ≤ t) (x y : V) :
    Summable (fun k : ℕ => ‖pw t k * (P ^ k) x y‖) :=
  summable_pw_mul ht _ (pow_abs_le_one hP x y)

lemma summable_heat (hP : IsStochastic P) {t : ℝ} (ht : 0 ≤ t) (x y : V) :
    Summable (fun k : ℕ => pw t k * (P ^ k) x y) :=
  (summable_norm_heat hP ht x y).of_norm

lemma heatKernel_eq (t : ℝ) (x y : V) :
    heatKernel P t x y = ∑' k : ℕ, pw t k * (P ^ k) x y := rfl

lemma hasSum_heat (hP : IsStochastic P) {t : ℝ} (ht : 0 ≤ t) (x y : V) :
    HasSum (fun k : ℕ => pw t k * (P ^ k) x y) (heatKernel P t x y) :=
  (summable_heat hP ht x y).hasSum

lemma heatKernel_nonneg (hP : IsStochastic P) {t : ℝ} (ht : 0 ≤ t) (x y : V) :
    0 ≤ heatKernel P t x y :=
  (hasSum_heat hP ht x y).nonneg fun k =>
    mul_nonneg (pw_nonneg ht k) (pow_entry_nonneg hP k x y)

lemma heatKernel_row_sum (hP : IsStochastic P) {t : ℝ} (ht : 0 ≤ t) (x : V) :
    ∑ y, heatKernel P t x y = 1 := by
  have h1 : HasSum (fun k : ℕ => ∑ y, pw t k * (P ^ k) x y) (∑ y, heatKernel P t x y) :=
    hasSum_sum fun y _ => hasSum_heat hP ht x y
  have h2 : ∀ k : ℕ, ∑ y, pw t k * (P ^ k) x y = pw t k := by
    intro k
    rw [← Finset.mul_sum, pow_row_sum hP k x, mul_one]
  rw [funext h2] at h1
  exact h1.unique (hasSum_pw t)

lemma heatKernel_isStochastic (hP : IsStochastic P) {t : ℝ} (ht : 0 ≤ t) :
    IsStochastic (heatKernel P t) :=
  ⟨fun x y => heatKernel_nonneg hP ht x y, fun x => heatKernel_row_sum hP ht x⟩

lemma heatKernel_stationary (hP : IsStochastic P) {π : V → ℝ} (hπ : IsStationary P π)
    {t : ℝ} (ht : 0 ≤ t) : IsStationary (heatKernel P t) π := by
  refine ⟨hπ.1, ?_⟩
  funext y
  show ∑ x, π x * heatKernel P t x y = π y
  have hvec : ∀ k : ℕ, ∑ x, π x * (P ^ k) x y = π y := by
    intro k
    have hpow : ∀ m : ℕ, Matrix.vecMul π (P ^ m) = π := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]
    exact congrFun (hpow k) y
  have h1 : HasSum (fun k : ℕ => ∑ x, π x * (pw t k * (P ^ k) x y))
      (∑ x, π x * heatKernel P t x y) :=
    hasSum_sum fun x _ => (hasSum_heat hP ht x y).mul_left (π x)
  have h2 : ∀ k : ℕ, ∑ x, π x * (pw t k * (P ^ k) x y) = pw t k * π y := by
    intro k
    have e : ∀ x : V, π x * (pw t k * (P ^ k) x y) = pw t k * (π x * (P ^ k) x y) :=
      fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum, hvec k]
  rw [funext h2] at h1
  have h3 : HasSum (fun k : ℕ => pw t k * π y) (π y) := by
    simpa using (hasSum_pw t).mul_right (π y)
  exact h1.unique h3

/-- The semigroup property `H_{s+t} = H_s H_t`, by the Cauchy product of the
two Poisson series. -/
lemma heat_semigroup (hP : IsStochastic P) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatKernel P (s + t) = heatKernel P s * heatKernel P t := by
  ext x y
  set F : V → ℕ → ℝ := fun z n =>
    ∑ q ∈ Finset.antidiagonal n,
      (pw s q.1 * (P ^ q.1) x z) * (pw t q.2 * (P ^ q.2) z y) with hF
  have hzsum : ∀ z : V, HasSum (F z) (heatKernel P s x z * heatKernel P t z y) := by
    intro z
    have hsum : Summable (F z) :=
      (summable_norm_sum_mul_antidiagonal_of_summable_norm
        (summable_norm_heat hP hs x z) (summable_norm_heat hP ht z y)).of_norm
    have hval : ∑' n, F z n = heatKernel P s x z * heatKernel P t z y := by
      rw [heatKernel_eq, heatKernel_eq]
      exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (summable_norm_heat hP hs x z) (summable_norm_heat hP ht z y)).symm
    rw [← hval]
    exact hsum.hasSum
  have hbig : HasSum (fun n => ∑ z, F z n) (∑ z, heatKernel P s x z * heatKernel P t z y) :=
    hasSum_sum fun z _ => hzsum z
  have hterm : ∀ n : ℕ, ∑ z, F z n = pw (s + t) n * (P ^ n) x y := by
    intro n
    have e1 : ∑ z, F z n
        = ∑ q ∈ Finset.antidiagonal n, ∑ z, (pw s q.1 * (P ^ q.1) x z) * (pw t q.2 * (P ^ q.2) z y) :=
      Finset.sum_comm
    have e2 : ∀ q ∈ Finset.antidiagonal n,
        ∑ z, (pw s q.1 * (P ^ q.1) x z) * (pw t q.2 * (P ^ q.2) z y)
          = (pw s q.1 * pw t q.2) * (P ^ n) x y := by
      intro q hq
      rw [Finset.mem_antidiagonal] at hq
      have e3 : ∀ z : V, (pw s q.1 * (P ^ q.1) x z) * (pw t q.2 * (P ^ q.2) z y)
          = (pw s q.1 * pw t q.2) * ((P ^ q.1) x z * (P ^ q.2) z y) := fun z => by ring
      rw [Finset.sum_congr rfl (fun z _ => e3 z), ← Finset.mul_sum]
      congr 1
      have : (P ^ n) x y = ∑ z, (P ^ q.1) x z * (P ^ q.2) z y := by
        rw [← hq, pow_add, Matrix.mul_apply]
      rw [this]
    rw [e1, Finset.sum_congr rfl e2, ← Finset.sum_mul, pw_conv]
  rw [funext hterm] at hbig
  have hgoal : HasSum (fun n : ℕ => pw (s + t) n * (P ^ n) x y)
      (heatKernel P (s + t) x y) := hasSum_heat hP (by linarith) x y
  rw [Matrix.mul_apply]
  exact hgoal.unique hbig

lemma heatKernel_zero (hP : IsStochastic P) : heatKernel P 0 = 1 := by
  ext x y
  have h1 : HasSum (fun k : ℕ => pw 0 k * (P ^ k) x y) (heatKernel P 0 x y) :=
    hasSum_heat hP le_rfl x y
  have h2 : ∀ k : ℕ, pw 0 k * (P ^ k) x y = if k = 0 then (1 : Matrix V V ℝ) x y else 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [pw]
    · have hz : (0 : ℝ) ^ k = 0 := zero_pow (by omega)
      have hk0 : k ≠ 0 := by omega
      simp [pw, hz, hk0]
  rw [funext h2] at h1
  exact h1.unique (hasSum_ite_eq 0 ((1 : Matrix V V ℝ) x y))

lemma heatKernel_nat (hP : IsStochastic P) : ∀ n : ℕ, heatKernel P (n : ℝ) = heatKernel P 1 ^ n := by
  intro n
  induction n with
  | zero => simpa using heatKernel_zero hP
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, heat_semigroup hP (by positivity) zero_le_one, ih, pow_succ]

/-- For `t > 0` the heat kernel is strictly positive on an irreducible chain. -/
lemma heatKernel_pos (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    {t : ℝ} (ht : 0 < t) (x y : V) : 0 < heatKernel P t x y := by
  obtain ⟨k, hk⟩ := hirr x y
  have hle : pw t k * (P ^ k) x y ≤ heatKernel P t x y :=
    le_hasSum (hasSum_heat hP ht.le x y) k
      (fun b _ => mul_nonneg (pw_nonneg ht.le b) (pow_entry_nonneg hP b x y))
  exact lt_of_lt_of_le (mul_pos (pw_pos ht k) hk) hle

lemma irreducible_of_pos {Q : Matrix V V ℝ} (h : ∀ x y, 0 < Q x y) :
    MarkovMixing.Irreducible Q := fun x y => ⟨1, by simpa using h x y⟩

lemma aperiodic_of_pos_diag {Q : Matrix V V ℝ} (h : ∀ x, 0 < Q x x) : Aperiodic Q := by
  intro x
  have hmem : (1 : ℕ) ∈ returnSet Q x := ⟨le_rfl, by simpa using h x⟩
  have hset : {d : ℕ | ∀ t ∈ returnSet Q x, d ∣ t} = {1} := by
    ext d
    constructor
    · intro hd
      have h1 := hd 1 hmem
      exact Nat.dvd_one.mp h1
    · intro hd
      have hd1 : d = 1 := hd
      subst hd1
      intro t _
      exact one_dvd t
  show sSup {d : ℕ | ∀ t ∈ returnSet Q x, d ∣ t} = 1
  rw [hset]
  exact csSup_singleton 1

lemma tvDist_nonneg (μ ν : V → ℝ) : 0 ≤ tvDist μ ν := by
  have hb : BddAbove (Set.range fun B : Finset V => |∑ x ∈ B, μ x - ∑ x ∈ B, ν x|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have := le_ciSup hb (∅ : Finset V)
  simp only [tvDist]
  simpa using this

lemma le_distStationary (Q : Matrix V V ℝ) (π : V → ℝ) (n : ℕ) (z : V) :
    tvDist (rowDist Q n z) π ≤ distStationary Q π n := by
  have hb : BddAbove (Set.range fun w : V => tvDist (rowDist Q n w) π) :=
    Set.Finite.bddAbove (Set.finite_range _)
  exact le_ciSup hb z

/-- Total variation distance to `π` of a mixture is at most the worst distance
of the ingredients. -/
lemma tvDist_mix {a : V → ℝ} (ha : IsDist a) {μ : V → V → ℝ} (hμ : ∀ z, IsDist (μ z))
    {π : V → ℝ} (hπ : IsDist π) {c : ℝ} (h : ∀ z, tvDist (μ z) π ≤ c) :
    tvDist (fun y => ∑ z, a z * μ z y) π ≤ c := by
  have hν : IsDist (fun y => ∑ z, a z * μ z y) := by
    refine ⟨fun y => Finset.sum_nonneg fun z _ => mul_nonneg (ha.1 z) ((hμ z).1 y), ?_⟩
    rw [Finset.sum_comm]
    have e : ∀ z : V, ∑ y, a z * μ z y = a z := by
      intro z; rw [← Finset.mul_sum, (hμ z).2, mul_one]
    rw [Finset.sum_congr rfl (fun z _ => e z), ha.2]
  rw [(MarkovMixing.tv_eq_half_l1 _ _ hν hπ).1]
  have hpt : ∀ y : V, |(∑ z, a z * μ z y) - π y| ≤ ∑ z, a z * |μ z y - π y| := by
    intro y
    have e : (∑ z, a z * μ z y) - π y = ∑ z, a z * (μ z y - π y) := by
      have : ∑ z, a z * (μ z y - π y) = (∑ z, a z * μ z y) - (∑ z, a z) * π y := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [this, ha.2, one_mul]
    rw [e]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun z _ => by rw [abs_mul, abs_of_nonneg (ha.1 z)]
  have hsum : ∑ y, |(∑ z, a z * μ z y) - π y| ≤ 2 * c := by
    refine le_trans (Finset.sum_le_sum fun y _ => hpt y) ?_
    rw [Finset.sum_comm]
    have e : ∀ z : V, ∑ y, a z * |μ z y - π y| = a z * (2 * tvDist (μ z) π) := by
      intro z
      rw [← Finset.mul_sum]
      congr 1
      rw [(MarkovMixing.tv_eq_half_l1 _ _ (hμ z) hπ).1]
      ring
    rw [Finset.sum_congr rfl (fun z _ => e z)]
    calc ∑ z, a z * (2 * tvDist (μ z) π) ≤ ∑ z, a z * (2 * c) := by
          refine Finset.sum_le_sum fun z _ => ?_
          exact mul_le_mul_of_nonneg_left (by linarith [h z]) (ha.1 z)
      _ = 2 * c := by rw [← Finset.sum_mul, ha.2, one_mul]
  show 2⁻¹ * ∑ y, |(fun y => ∑ z, a z * μ z y) y - π y| ≤ c
  simp only []
  linarith

end Kernel

end Heat

open Heat

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ)
    (hπ : MarkovMixing.IsStationary P π) :
    Filter.Tendsto (fun t : ℝ => MarkovMixing.contDistStationary P π t)
      Filter.atTop (nhds 0) := by
  classical
  set Q : Matrix V V ℝ := MarkovMixing.heatKernel P 1 with hQ
  have hQst : MarkovMixing.IsStochastic Q := heatKernel_isStochastic hP zero_le_one
  have hQstat : MarkovMixing.IsStationary Q π := heatKernel_stationary hP hπ zero_le_one
  have hQpos : ∀ x y : V, 0 < Q x y := fun x y => heatKernel_pos hP hirr one_pos x y
  have hQirr : MarkovMixing.Irreducible Q := irreducible_of_pos hQpos
  have hQap : MarkovMixing.Aperiodic Q := aperiodic_of_pos_diag fun x => hQpos x x
  obtain ⟨α, hα, C, hC, hbd⟩ :=
    MarkovMixing.convergence_theorem Q hQst hQirr hQap π hQstat
  -- the continuous distance is squeezed by the discrete one at the integer part
  have hkey : ∀ t : ℝ, 0 ≤ t →
      MarkovMixing.contDistStationary P π t ≤ C * α ^ (⌊t⌋₊ : ℕ) := by
    intro t ht
    set n : ℕ := ⌊t⌋₊ with hn
    have hnt : (n : ℝ) ≤ t := Nat.floor_le ht
    have hr : 0 ≤ t - (n : ℝ) := by linarith
    have hsplit : MarkovMixing.heatKernel P t = MarkovMixing.heatKernel P (t - n) * Q ^ n := by
      have h1 : MarkovMixing.heatKernel P ((t - n) + n)
          = MarkovMixing.heatKernel P (t - n) * MarkovMixing.heatKernel P (n : ℝ) :=
        heat_semigroup hP hr (Nat.cast_nonneg n)
      rw [show (t - (n:ℝ)) + (n:ℝ) = t by ring] at h1
      rw [h1, heatKernel_nat hP n]
    have hrow : ∀ x : V, MarkovMixing.tvDist (fun y => MarkovMixing.heatKernel P t x y) π
        ≤ MarkovMixing.distStationary Q π n := by
      intro x
      have he : (fun y => MarkovMixing.heatKernel P t x y)
          = fun y => ∑ z, MarkovMixing.heatKernel P (t - n) x z * MarkovMixing.rowDist Q n z y := by
        funext y
        rw [hsplit, Matrix.mul_apply]
        rfl
      rw [he]
      refine tvDist_mix ?_ ?_ hπ.1 ?_
      · exact ⟨fun z => heatKernel_nonneg hP hr x z, heatKernel_row_sum hP hr x⟩
      · intro z
        exact ⟨fun y => pow_entry_nonneg hQst n z y, pow_row_sum hQst n z⟩
      · intro z
        exact le_distStationary Q π n z
    have hsup : MarkovMixing.contDistStationary P π t ≤ MarkovMixing.distStationary Q π n :=
      ciSup_le hrow
    exact le_trans hsup (hbd n)
  have hnn : ∀ t : ℝ, 0 ≤ MarkovMixing.contDistStationary P π t := by
    intro t
    refine le_trans (tvDist_nonneg (fun y => MarkovMixing.heatKernel P t (Classical.arbitrary V) y) π) ?_
    have hb : BddAbove (Set.range fun x : V =>
        MarkovMixing.tvDist (fun y => MarkovMixing.heatKernel P t x y) π) :=
      Set.Finite.bddAbove (Set.finite_range _)
    exact le_ciSup hb (Classical.arbitrary V)
  have hup : Filter.Tendsto (fun t : ℝ => C * α ^ (⌊t⌋₊ : ℕ)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => C * α ^ n) Filter.atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hα.1) hα.2
      simpa using this.const_mul C
    exact h1.comp tendsto_nat_floor_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun t => hnn t) ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact hkey t ht
