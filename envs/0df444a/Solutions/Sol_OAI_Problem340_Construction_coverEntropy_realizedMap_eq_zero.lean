-- Prove2me | solution 1 for OAI.Problem340.Construction.coverEntropy_realizedMap_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T23:13:27.156688+00:00
-- url     : https://prove2.me/submissions/265ec40c-85a4-42df-b91f-67d3e4cfd2b4

import Mathlib
import Definitions.Def_C1EntropyCounterexample
import Definitions.Def_OAIQWEC000

instance p340Fact100 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

section
-- module Solutions.OAIQW_Problem340.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Clock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Clock

lemma cutoff_one {x : ℝ} (hx : |x| ≤ 1) : cutoff x = 1 := by
  apply profileCutoff.one_of_mem_closedBall
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  simpa [profileCutoff, Real.dist_eq, abs_of_nonneg (sq_nonneg x)] using hx2

lemma cutoff_zero {x : ℝ} (hx : 6 / 5 ≤ |x|) : cutoff x = 0 := by
  apply profileCutoff.zero_of_le_dist
  have hx2 : 36 / 25 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  simpa [profileCutoff, Real.dist_eq, abs_of_nonneg (sq_nonneg x)] using hx2

lemma localBarrier_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    localBarrier x = x ^ 2 / 4 := by
  simp [localBarrier, cutoff_one hx]

lemma localBarrier_of_abs_ge {x : ℝ} (hx : 6 / 5 ≤ |x|) :
    localBarrier x = 1 := by
  simp [localBarrier, cutoff_zero hx]

lemma localBarrier_nonneg (x : ℝ) : 0 ≤ localBarrier x := by
  have hη : 0 ≤ cutoff x := cutoff_nonneg _
  have hη' : cutoff x ≤ 1 := cutoff_le_one _
  have hp : 0 ≤ cutoff x * x ^ 2 / 4 := by positivity
  unfold localBarrier
  linarith

lemma localBarrier_le_one (x : ℝ) : localBarrier x ≤ 1 := by
  by_cases hx : 6 / 5 ≤ |x|
  · rw [localBarrier_of_abs_ge hx]
  · have hx' : |x| < 6 / 5 := lt_of_not_ge hx
    have hx2 : x ^ 2 ≤ 4 := by
      have hm := (abs_lt.mp hx').1
      have hp := (abs_lt.mp hx').2
      nlinarith [sq_nonneg x]
    have hη : 0 ≤ cutoff x := cutoff_nonneg _
    have hmul : cutoff x * x ^ 2 ≤ cutoff x * 4 := mul_le_mul_of_nonneg_left hx2 hη
    unfold localBarrier
    linarith

lemma localBarrier_eq_zero_iff (x : ℝ) : localBarrier x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hη : 0 ≤ cutoff x := cutoff_nonneg _
    have hη' : cutoff x ≤ 1 := cutoff_le_one _
    have hp : 0 ≤ cutoff x * x ^ 2 / 4 := by positivity
    have h1 : cutoff x = 1 := by
      unfold localBarrier at hx
      linarith
    unfold localBarrier at hx
    rw [h1] at hx
    nlinarith [sq_nonneg x]
  · rintro rfl
    norm_num [localBarrier, cutoff_one (x := 0) (by norm_num)]

lemma abs_coordinate_le (t : ℝ) : |coordinate t| ≤ |t - 50| := by
  have hs : |Real.sin (Real.pi * (t - 50) / 100)| ≤
      |Real.pi * (t - 50) / 100| := Real.abs_sin_le_abs
  have hp : 0 ≤ Real.pi := Real.pi_pos.le
  have hπ : 30 * Real.pi ≤ 100 := by linarith [Real.pi_lt_d2]
  have ha : 0 ≤ |t - 50| := abs_nonneg _
  simp only [abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos (show (0 : ℝ) < 100 by norm_num)] at hs
  unfold coordinate
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < 30 by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_right hπ ha]

lemma barrier_nonneg (t : ℝ) : 0 ≤ barrier t := localBarrier_nonneg _

lemma barrier_le_one (t : ℝ) : barrier t ≤ 1 := localBarrier_le_one _

lemma barrier_stops (t : ℝ) (ht : t ≤ 50) : t + barrier t ≤ 50 := by
  by_cases hsmall : 50 - t ≤ 1
  · have hd : 0 ≤ 50 - t := by linarith
    have habs : |t - 50| = 50 - t := by rw [abs_of_nonpos (by linarith)]; ring
    have hcoord : |coordinate t| ≤ 1 := by
      calc |coordinate t| ≤ |t - 50| := abs_coordinate_le t
           _ ≤ 1 := by rw [habs]; exact hsmall
    have hbound : (coordinate t) ^ 2 ≤ (50 - t) ^ 2 := by
      have h := abs_coordinate_le t
      rw [habs] at h
      nlinarith [(abs_nonneg (coordinate t)), sq_abs (coordinate t)]
    rw [barrier, localBarrier_of_abs_le_one hcoord]
    nlinarith
  · have hlarge : 1 ≤ 50 - t := le_of_lt (lt_of_not_ge hsmall)
    linarith [barrier_le_one t]

lemma barrier_eq_zero_iff (t : ℝ) :
    barrier t = 0 ↔ ∃ k : ℤ, t = 50 + 100 * (k : ℝ) := by
  rw [barrier, localBarrier_eq_zero_iff]
  unfold coordinate
  rw [mul_eq_zero]
  simp only [show (30 : ℝ) ≠ 0 by norm_num, false_or, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    apply (mul_right_inj' hp).mp
    nlinarith [hk]
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    ring

lemma abs_coordinate_lower {t : ℝ} (ht : |t - 50| ≤ 50) :
    (3 / 5 : ℝ) * |t - 50| ≤ |coordinate t| := by
  have hp : 0 ≤ Real.pi := Real.pi_pos.le
  have ha : |Real.pi * (t - 50) / 100| = Real.pi * |t - 50| / 100 := by
    rw [abs_div, abs_mul, abs_of_nonneg hp]
    norm_num
  have harg : |Real.pi * (t - 50) / 100| ≤ Real.pi / 2 := by
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_left ht hp]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [ha] at hs
  have heq : 2 / Real.pi * (Real.pi * |t - 50| / 100) = |t - 50| / 50 := by
    field_simp
    ring
  rw [heq] at hs
  unfold coordinate
  rw [abs_mul]
  norm_num
  linarith

lemma barrier_plateau {t : ℝ} (ht0 : 0 ≤ t) (ht100 : t ≤ 100)
    (hfar : 2 ≤ |t - 50|) : barrier t = 1 := by
  apply localBarrier_of_abs_ge
  have habs : |t - 50| ≤ 50 := by
    apply abs_le.mpr
    constructor <;> linarith
  have h := abs_coordinate_lower habs
  linarith

lemma increment_nonneg (t : ℝ) {e : ℝ} (he : 0 ≤ e) :
    0 ≤ increment t e := by
  unfold increment
  have hb := barrier_nonneg t
  have hb' := barrier_le_one t
  positivity

lemma barrier_le_increment (t : ℝ) {e : ℝ} (he : 0 ≤ e) :
    barrier t ≤ increment t e := by
  unfold increment
  have hp : 0 ≤ (1 - barrier t) * e := mul_nonneg (sub_nonneg.mpr (barrier_le_one t)) he
  linarith

lemma increment_le_one (t : ℝ) {e : ℝ} (he : e ≤ 1) : increment t e ≤ 1 := by
  unfold increment
  have hp := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr (barrier_le_one t))
  linarith

lemma increment_eq_one_of_barrier_eq_one {t e : ℝ} (h : barrier t = 1) :
    increment t e = 1 := by
  simp [increment, h]

end Problem340.Clock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PeriodicEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Function
open scoped Uniformity

namespace Problem340
namespace PeriodicEntropy

variable {X : Type*} {T : X → X} {k : ℕ}

theorem dynEntourage_period_subset (hk : 0 < k) (hperiod : T^[k] = id)
    (U : Set (X × X)) (n : ℕ) :
    Dynamics.dynEntourage T U k ⊆ Dynamics.dynEntourage T U n := by
  rintro ⟨x, y⟩ hxy
  rw [Dynamics.mem_dynEntourage] at hxy ⊢
  intro j _
  have hx : IsPeriodicPt T k x := by simp [IsPeriodicPt, IsFixedPt, hperiod]
  have hy : IsPeriodicPt T k y := by simp [IsPeriodicPt, IsFixedPt, hperiod]
  simpa only [hx.iterate_mod_apply j, hy.iterate_mod_apply j] using
    hxy (j % k) (Nat.mod_lt j hk)

theorem isDynCoverOf_all_of_period (hk : 0 < k) (hperiod : T^[k] = id)
    {U : Set (X × X)} {F s : Set X}
    (hs : Dynamics.IsDynCoverOf T F U k s) (n : ℕ) :
    Dynamics.IsDynCoverOf T F U n s :=
  hs.mono_entourage (dynEntourage_period_subset hk hperiod U n)

theorem coverEntropy_eq_zero_of_period [UniformSpace X] [CompactSpace X] [Nonempty X]
    (hk : 0 < k) (hperiod : T^[k] = id) :
    Dynamics.coverEntropy T (Set.univ : Set X) = 0 := by
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T Set.univ_nonempty)
  unfold Dynamics.coverEntropy
  refine iSup₂_le fun U hU => ?_
  obtain ⟨s, hs⟩ := Dynamics.exists_isDynCoverOf_of_isCompact_invariant
    isCompact_univ (Set.mapsTo_univ T Set.univ) hU k
  have hspos : 0 < s.card := Finset.card_pos.mpr (hs.nonempty Set.univ_nonempty)
  have hbound : ∀ n, Dynamics.coverMincard T Set.univ U n ≤ (s.card : ℕ∞) :=
    fun n => (isDynCoverOf_all_of_period hk hperiod hs n).coverMincard_le_card
  unfold Dynamics.coverEntropyEntourage
  calc
    ExpGrowth.expGrowthSup (fun n =>
        (Dynamics.coverMincard T Set.univ U n).toENNReal) ≤
        ExpGrowth.expGrowthSup (fun _ : ℕ => ((s.card : ℕ∞).toENNReal)) :=
      ExpGrowth.expGrowthSup_monotone (fun n => ENat.toENNReal_mono (hbound n))
    _ = 0 := ExpGrowth.expGrowthSup_const (by exact_mod_cast hspos.ne') (by simp)

end PeriodicEntropy
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockAtInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340
namespace ClockAtInfinity

theorem step_period : step^[100] = id := by
  have h : (100 : ℕ) • ((1 : ℝ) : Clock) = 0 := by
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  funext t
  change (fun x : Clock => x + ((1 : ℝ) : Clock))^[100] t = t
  rw [add_right_iterate]
  simp only [h, add_zero]

theorem coverEntropy_step : Dynamics.coverEntropy step (Set.univ : Set Clock) = 0 := by
  let : Fact (0 < (100 : ℝ)) := ⟨by norm_num⟩
  exact PeriodicEntropy.coverEntropy_eq_zero_of_period (by norm_num) step_period

theorem coverEntropy_clockImage {X : Type*} [UniformSpace X]
    {T : X → X} {φ : Clock → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ step T) :
    Dynamics.coverEntropy T (Set.range φ) = 0 := by
  let : Fact (0 < (100 : ℝ)) := ⟨by norm_num⟩
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T (Set.range_nonempty φ))
  have h := Dynamics.coverEntropy_image_le_of_uniformContinuous hsem
    (CompactSpace.uniformContinuous_of_continuous hφ) Set.univ
  simpa only [Set.image_univ, coverEntropy_step] using h

end ClockAtInfinity
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set
open scoped Topology

namespace Problem340.ClockDynamics

theorem bounded_clock_limit {t : ℕ → ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t)) :
    ∃ T : ℝ, Tendsto t atTop (𝓝 T) ∧
      Tendsto (fun n => t (n + 1) - t n) atTop (𝓝 0) := by
  have hlimit : Tendsto t atTop (𝓝 (⨆ n, t n)) :=
    tendsto_atTop_ciSup hmono hbounded
  refine ⟨⨆ n, t n, hlimit, ?_⟩
  have hnext : Tendsto (fun n => t (n + 1)) atTop (𝓝 (⨆ n, t n)) :=
    hlimit.comp (tendsto_add_atTop_nat 1)
  simpa using hnext.sub hlimit

theorem bounded_clock_limit_barrier {t : ℕ → ℝ} {b : ℝ → ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t))
    (hb : Continuous b) (hb_nonneg : ∀ x, 0 ≤ b x)
    (hstep : ∀ n, b (t n) ≤ t (n + 1) - t n) :
    ∃ T : ℝ, Tendsto t atTop (𝓝 T) ∧ b T = 0 := by
  obtain ⟨T, hlimit, hdiff⟩ := bounded_clock_limit hmono hbounded
  refine ⟨T, hlimit, ?_⟩
  have hzero : Tendsto (fun n => b (t n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => hb_nonneg (t n)) hstep hdiff
  exact tendsto_nhds_unique (hb.tendsto T |>.comp hlimit) hzero

theorem bounded_clock_limit_lattice {t : ℕ → ℝ} {b : ℝ → ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t))
    (hb : Continuous b) (hb_nonneg : ∀ x, 0 ≤ b x)
    (hstep : ∀ n, b (t n) ≤ t (n + 1) - t n)
    (hzeros : ∀ x, b x = 0 → ∃ k : ℤ, x = 50 + 100 * (k : ℝ)) :
    ∃ k : ℤ, Tendsto t atTop (𝓝 (50 + 100 * (k : ℝ))) := by
  obtain ⟨T, hlimit, hzero⟩ :=
    bounded_clock_limit_barrier hmono hbounded hb hb_nonneg hstep
  obtain ⟨k, rfl⟩ := hzeros T hzero
  exact ⟨k, hlimit⟩

theorem barrier_trapping {t r : ℕ → ℝ} {a T R : ℝ} {N : ℕ}
    (htN : a ≤ t N ∧ t N ≤ T) (hrN : r N ≤ R)
    (hstep : ∀ n, N ≤ n → a ≤ t n → t n ≤ T → r n ≤ R →
      (a ≤ t (n + 1) ∧ t (n + 1) ≤ T) ∧ r (n + 1) ≤ R) :
    ∀ n, N ≤ n → (a ≤ t n ∧ t n ≤ T) ∧ r n ≤ R := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨htN, hrN⟩
  | succ n hn ih => exact hstep n hn ih.1.1 ih.1.2 ih.2

theorem exists_first_crossing {t : ℕ → ℝ} {a : ℝ}
    (hstart : t 0 < a) (hstep : ∀ n, t (n + 1) - t n ≤ 1)
    (hevent : ∃ n, a ≤ t n) :
    ∃ n, a ≤ t n ∧ t n < a + 1 ∧ ∀ m, m < n → t m < a := by
  classical
  let n := Nat.find hevent
  have hn : a ≤ t n := Nat.find_spec hevent
  have hbefore : ∀ m, m < n → t m < a := by
    intro m hm
    exact lt_of_not_ge (Nat.find_min hevent hm)
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    rw [hnzero] at hn
    linarith
  refine ⟨n, hn, ?_, hbefore⟩
  have hp : t (n - 1) < a := hbefore (n - 1) (by omega)
  have hs := hstep (n - 1)
  have heq : n - 1 + 1 = n := by omega
  rw [heq] at hs
  linarith

theorem squaring_tendsto_zero {R : Type*} [SeminormedRing R] {z : ℕ → R}
    (hstep : ∀ n, z (n + 1) = z n ^ 2) (hsmall : ‖z 0‖ < 1) :
    Tendsto z atTop (𝓝 0) := by
  have hformula : ∀ n, z n = z 0 ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hstep, ih, ← pow_mul, Nat.pow_succ]
  have hpower := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
  exact hpower.congr (fun n => (hformula n).symm)

theorem eventually_squaring_tendsto_zero {R : Type*} [SeminormedRing R]
    {z : ℕ → R} (hstep : ∀ᶠ n in atTop, z (n + 1) = z n ^ 2)
    (hsmall : ∀ᶠ n in atTop, ‖z n‖ < 1) : Tendsto z atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hstep.and hsmall)
  apply (tendsto_add_atTop_iff_nat N).mp
  apply squaring_tendsto_zero
  · intro n
    have h := (hN (n + N) (by omega)).1
    convert h using 1
    congr 1
    omega
  · simpa using (hN N le_rfl).2

theorem eventually_small_of_bounded_clock {t r : ℕ → ℝ} {R c : ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t)) (hc : 0 < c)
    (hfast : ∀ n, R ≤ r n → c ≤ t (n + 1) - t n) :
    ∀ᶠ n in atTop, r n < R := by
  obtain ⟨T, hlimit, hdiff⟩ := bounded_clock_limit hmono hbounded
  have hsmall := hdiff.eventually (gt_mem_nhds hc)
  filter_upwards [hsmall] with n hn
  by_contra h
  exact (not_le_of_gt hn) (hfast n (le_of_not_gt h))

theorem preparation_norm_gt_half {t : ℕ → ℝ} {z : ℕ → ℂ} {N : ℕ}
    (hmono : Monotone t) (hunbounded : ¬ BddAbove (Set.range t))
    (hstart : 8 ≤ t N ∧ t N ≤ 50)
    (htrap : ∀ n, N ≤ n → 8 ≤ t n → t n ≤ 50 → ‖z n‖ ≤ 1 / 2 →
      t (n + 1) ≤ 50 ∧ z (n + 1) = z n ^ 2) :
    1 / 2 < ‖z N‖ := by
  by_contra h
  have hsmall : ‖z N‖ ≤ 1 / 2 := le_of_not_gt h
  have hinvariant : ∀ n, N ≤ n → (8 ≤ t n ∧ t n ≤ 50) ∧ ‖z n‖ ≤ 1 / 2 := by
    apply barrier_trapping hstart hsmall
    intro n hn hlow hhigh hz
    obtain ⟨hclock, hsquare⟩ := htrap n hn hlow hhigh hz
    refine ⟨⟨hlow.trans (hmono (Nat.le_succ n)), hclock⟩, ?_⟩
    rw [hsquare, norm_pow]
    nlinarith [norm_nonneg (z n)]
  apply hunbounded
  refine ⟨50, ?_⟩
  rintro x ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · exact (hinvariant n hn).1.2
  · exact (hmono (le_of_not_ge hn)).trans hstart.2

end Problem340.ClockDynamics

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem orbitClockLift_succ {X : Type*} (f : X → X) (h : X → ℝ)
    (x : X) (t₀ : ℝ) (n : ℕ) :
    orbitClockLift f h x t₀ (n + 1) =
      orbitClockLift f h x t₀ n + h (f^[n] x) := by
  simp only [orbitClockLift, Finset.sum_range_succ, add_assoc]

theorem coe_orbitClockLift {X : Type*} (P : ℝ)
    (f : X → X) (h : X → ℝ) (clock : X → AddCircle P)
    (hclock : ∀ x, clock (f x) = clock x + (h x : AddCircle P))
    (x : X) (t₀ : ℝ) (h₀ : (t₀ : AddCircle P) = clock x) (n : ℕ) :
    (orbitClockLift f h x t₀ n : AddCircle P) = clock (f^[n] x) := by
  induction n with
  | zero => simpa using h₀
  | succ n hn =>
      rw [orbitClockLift_succ, Function.iterate_succ_apply', hclock, ← hn]
      simp

theorem monotone_orbitClockLift {X : Type*} (f : X → X) (h : X → ℝ)
    (hh : ∀ x, 0 ≤ h x) (x : X) (t₀ : ℝ) :
    Monotone (orbitClockLift f h x t₀) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [orbitClockLift_succ]
  exact le_add_of_nonneg_right (hh _)

theorem orbitClockLift_step_bounds {X : Type*} (f : X → X) (h : X → ℝ)
    (hh : ∀ x, h x ∈ Set.Icc (0 : ℝ) 1) (x : X) (t₀ : ℝ) (n : ℕ) :
    orbitClockLift f h x t₀ (n + 1) - orbitClockLift f h x t₀ n ∈
      Set.Icc (0 : ℝ) 1 := by
  rw [orbitClockLift_succ, add_sub_cancel_left]
  exact hh _

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set
open scoped Topology OnePoint

namespace Problem340.Clock

namespace LiftedOrbit

variable {t e : ℕ → ℝ} (h : LiftedOrbit t e)
include h

lemma monotone : Monotone t := by
  apply monotone_nat_of_le_succ
  intro n
  rw [h.update]
  exact le_add_of_nonneg_right (increment_nonneg _ (h.cutoff_nonneg n))

lemma barrier_le_difference (n : ℕ) : barrier (t n) ≤ t (n + 1) - t n := by
  rw [h.update]
  simpa using barrier_le_increment (t n) (h.cutoff_nonneg n)

theorem bounded_limit (hbounded : BddAbove (Set.range t)) :
    ∃ k : ℤ, Tendsto t atTop (𝓝 (50 + 100 * (k : ℝ))) := by
  apply ClockDynamics.bounded_clock_limit_lattice h.monotone hbounded
    (contDiff_barrier (n := 0)).continuous barrier_nonneg h.barrier_le_difference
  intro x hx
  exact (barrier_eq_zero_iff x).mp hx

theorem bounded_circle_limit (hbounded : BddAbove (Set.range t)) :
    Tendsto (fun n => (t n : AddCircle (100 : ℝ))) atTop
      (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) := by
  obtain ⟨k, hlimit⟩ := h.bounded_limit hbounded
  have hperiod : (((50 + 100 * (k : ℝ)) : ℝ) : AddCircle (100 : ℝ)) =
      ((50 : ℝ) : AddCircle (100 : ℝ)) := by
    have heq : (100 : ℝ) * (k : ℝ) = k • (100 : ℝ) := by
      simp [zsmul_eq_mul, mul_comm]
    rw [heq, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, add_zero]
  have hcircle : Tendsto (fun n => (t n : AddCircle (100 : ℝ))) atTop
      (𝓝 (((50 + 100 * (k : ℝ)) : ℝ) : AddCircle (100 : ℝ))) :=
    ((AddCircle.continuous_mk' (100 : ℝ)).tendsto (50 + 100 * (k : ℝ))).comp hlimit
  simpa only [hperiod] using hcircle

lemma cutoff_le_difference (n : ℕ) : e n ≤ t (n + 1) - t n := by
  rw [h.update]
  have hp := mul_nonneg (barrier_nonneg (t n)) (sub_nonneg.mpr (h.cutoff_le_one n))
  unfold increment
  nlinarith

theorem cutoff_tendsto_zero (hbounded : BddAbove (Set.range t)) :
    Tendsto e atTop (𝓝 0) := by
  obtain ⟨_, _, hdifference⟩ := ClockDynamics.bounded_clock_limit h.monotone hbounded
  exact squeeze_zero h.cutoff_nonneg h.cutoff_le_difference hdifference

theorem eventually_observation_zero {β : ℝ → ℝ}
    (hbounded : BddAbove (Set.range t)) (hperiodic : Function.Periodic β 100)
    (hzero : ∀ x ∈ Set.Ioo (48 : ℝ) 52, β x = 0) :
    ∀ᶠ n in atTop, β (t n) = 0 := by
  obtain ⟨k, hlimit⟩ := h.bounded_limit hbounded
  have hshift : Tendsto (fun n => t n - (k : ℝ) * 100) atTop (𝓝 50) := by
    have heq : 50 + 100 * (k : ℝ) - (k : ℝ) * 100 = 50 := by ring
    simpa only [heq] using hlimit.sub_const ((k : ℝ) * 100)
  have hnear : ∀ᶠ n in atTop, t n - (k : ℝ) * 100 ∈ Set.Ioo (48 : ℝ) 52 :=
    hshift.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hnear] with n hn
  have hz := hzero _ hn
  rwa [hperiodic.sub_int_mul_eq k] at hz

theorem eventually_norm_lt {V : Type*} [SeminormedAddCommGroup V]
    {z : ℕ → V} {r : ℝ} (hbounded : BddAbove (Set.range t))
    (hcutoff : ∀ n, r ≤ ‖z n‖ → e n = 1) :
    ∀ᶠ n in atTop, ‖z n‖ < r := by
  apply ClockDynamics.eventually_small_of_bounded_clock h.monotone hbounded
    (show (0 : ℝ) < 1 by norm_num)
  intro n hn
  rw [h.update, hcutoff n hn, increment_one]
  linarith

theorem main_tendsto_zero {R : Type*} [SeminormedRing R] {z : ℕ → R}
    {r : ℝ} (hbounded : BddAbove (Set.range t)) (hr : r ≤ 1)
    (hcutoff : ∀ n, r ≤ ‖z n‖ → e n = 1)
    (hsquare : ∀ᶠ n in atTop, z (n + 1) = z n ^ 2) :
    Tendsto z atTop (𝓝 0) := by
  apply ClockDynamics.eventually_squaring_tendsto_zero hsquare
  filter_upwards [h.eventually_norm_lt hbounded hcutoff] with n hn
  exact hn.trans_le hr

theorem main_tendsto_zero_of_readouts {ι : Type*} [Fintype ι]
    {z : ℕ → ℂ} (hbounded : BddAbove (Set.range t))
    (hcutoff : ∀ n, 3 / 4 ≤ ‖z n‖ → e n = 1)
    (β : ι → ℝ → ℝ) (u : ℕ → ι → ℂ)
    (hperiodic : ∀ i, Function.Periodic (β i) 100)
    (hzero : ∀ i x, x ∈ Set.Ioo (48 : ℝ) 52 → β i x = 0)
    (hupdate : ∀ n, z (n + 1) = z n ^ 2 + ∑ i, β i (t n) • u n i) :
    Tendsto z atTop (𝓝 0) := by
  have hcoeff : ∀ᶠ n in atTop, ∀ i, β i (t n) = 0 :=
    eventually_all.mpr (fun i => h.eventually_observation_zero hbounded
      (hperiodic i) (hzero i))
  apply h.main_tendsto_zero hbounded (show (3 / 4 : ℝ) ≤ 1 by norm_num) hcutoff
  filter_upwards [hcoeff] with n hn
  rw [hupdate]
  simp [hn]

theorem avoids_invariant_fast_set {X : Type*} {z : ℕ → X} {S : Set X}
    (hbounded : BddAbove (Set.range t))
    (hstable : ∀ n, z n ∈ S → z (n + 1) ∈ S)
    (hfast : ∀ n, z n ∈ S → e n = 1) : ∀ n, z n ∉ S := by
  intro N hN
  have hforever : ∀ n, N ≤ n → z n ∈ S := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hN
    | succ n _ ih => exact hstable n ih
  have hsmall : ∀ᶠ n in atTop, e n < 1 :=
    (h.cutoff_tendsto_zero hbounded).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  have hlt := hM (N + M) (by omega)
  rw [hfast (N + M) (hforever _ (by omega))] at hlt
  exact lt_irrefl _ hlt

theorem onePoint_main_tendsto_zero_of_readouts {ι : Type*} [Fintype ι]
    {z : ℕ → OnePoint ℂ} (hbounded : BddAbove (Set.range t))
    (hpole : ∀ n, z n = ∞ → z (n + 1) = ∞)
    (hfast_pole : ∀ n, z n = ∞ → e n = 1)
    (hcutoff : ∀ n (w : ℂ), z n = (w : OnePoint ℂ) → 3 / 4 ≤ ‖w‖ → e n = 1)
    (β : ι → ℝ → ℝ) (u : ℕ → ι → ℂ)
    (hperiodic : ∀ i, Function.Periodic (β i) 100)
    (hzero : ∀ i x, x ∈ Set.Ioo (48 : ℝ) 52 → β i x = 0)
    (hupdate : ∀ n (w : ℂ), z n = (w : OnePoint ℂ) →
      z (n + 1) = ((w ^ 2 + ∑ i, β i (t n) • u n i : ℂ) : OnePoint ℂ)) :
    Tendsto z atTop (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
  have hfinite : ∀ n, z n ≠ ∞ :=
    h.avoids_invariant_fast_set (S := {∞}) hbounded hpole hfast_pole
  choose w hw using fun n => OnePoint.ne_infty_iff_exists.mp (hfinite n)
  have hrec : ∀ n, w (n + 1) = w n ^ 2 + ∑ i, β i (t n) • u n i := by
    intro n
    apply OnePoint.coe_injective
    rw [hw (n + 1)]
    exact hupdate n (w n) (hw n).symm
  have hlim : Tendsto w atTop (𝓝 0) :=
    h.main_tendsto_zero_of_readouts hbounded
      (fun n hn => hcutoff n (w n) (hw n).symm hn) β u hperiodic hzero hrec
  have hcoe := (OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hlim
  exact hcoe.congr hw

end LiftedOrbit
end Problem340.Clock

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Set

namespace Problem340

theorem clock_readings_separated {t : ℕ → ℝ} (ht : Monotone t)
    {i j : ℕ} (hij : i < j) (hstep : t (i + 1) = t i + 1) :
    t i + 1 ≤ t j := by
  rw [← hstep]
  exact ht (Nat.succ_le_of_lt hij)

theorem clock_readout_unique {t : ℕ → ℝ} {β : ℝ → ℝ} {a b : ℝ}
    (ht : Monotone t) (hwidth : b - a < 1)
    (hsupport : ∀ x, β x ≠ 0 → a < x ∧ x < b)
    (hstep : ∀ n, β (t n) ≠ 0 → t (n + 1) = t n + 1)
    {i j : ℕ} (hi : β (t i) ≠ 0) (hj : β (t j) ≠ 0) : i = j := by
  obtain hij | hij | hij := lt_trichotomy i j
  · have hsep := clock_readings_separated ht hij (hstep i hi)
    have hi' := hsupport (t i) hi
    have hj' := hsupport (t j) hj
    linarith
  · exact hij
  · have hsep := clock_readings_separated ht hij (hstep j hj)
    have hi' := hsupport (t i) hi
    have hj' := hsupport (t j) hj
    linarith

theorem clock_unit_speed_add {t : ℕ → ℝ} {a b : ℝ}
    (ht : Monotone t)
    (hstep : ∀ n, a ≤ t n → t n ≤ b → t (n + 1) = t n + 1)
    (i d : ℕ) (ha : a ≤ t i) (hb : t (i + d) ≤ b) :
    t (i + d) = t i + (d : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd : t (i + d) ≤ b := (ht (by omega)).trans hb
    have hlo : a ≤ t (i + d) := ha.trans (ht (by omega))
    have heq := hstep (i + d) hlo hd
    have hprev := ih hd
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.cast_add, Nat.cast_one,
      hprev, add_assoc] using heq

theorem clock_preparation_card_le_five {t : ℕ → ℝ}
    (ht : Monotone t)
    (hstep : ∀ n, 8 ≤ t n → t n ≤ 12 → t (n + 1) = t n + 1)
    (I : Finset ℕ) (hI : ∀ i ∈ I, 8 < t i ∧ t i < 12) : I.card ≤ 5 := by
  classical
  by_cases hne : I.Nonempty
  · let i := I.min' hne
    have hi : i ∈ I := Finset.min'_mem I hne
    have hsub : I ⊆ Finset.Icc i (i + 4) := by
      intro j hj
      have hij : i ≤ j := Finset.min'_le I j hj
      have hadd : i + (j - i) = j := Nat.add_sub_of_le hij
      have htime := clock_unit_speed_add ht hstep i (j - i)
        (hI i hi).1.le (by simpa [hadd] using (hI j hj).2.le)
      rw [hadd] at htime
      have hgap : (j - i : ℝ) < 4 := by
        have hi' := (hI i hi).1
        have hj' := (hI j hj).2
        have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) :=
          Nat.cast_sub hij
        rw [hcast] at htime
        linarith
      have hgap' : j - i < 4 := by
        have : ((j - i : ℕ) : ℝ) < (4 : ℕ) := by
          simpa [Nat.cast_sub hij] using hgap
        exact_mod_cast this
      exact Finset.mem_Icc.mpr ⟨hij, by omega⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hc
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

theorem clock_prediction_agreement {X : Type*} {x y : ℕ → X}
    {clock : X → ℝ} {a b : ℝ} {N : ℕ}
    (hzero : x 0 = y 0)
    (hbefore : ∀ n < N, x n = y n → clock (x n) < a → x (n + 1) = y (n + 1))
    (hxstep : ∀ n < N, a ≤ clock (x n) → clock (x n) ≤ b →
      clock (x (n + 1)) = clock (x n) + 1)
    (hystep : ∀ n < N, a ≤ clock (y n) → clock (y n) ≤ b →
      clock (y (n + 1)) = clock (y n) + 1)
    (hbound : ∀ n < N, clock (x n) ≤ b) :
    ∀ n ≤ N, clock (x n) = clock (y n) := by
  have hfast (n : ℕ) (hn : n < N) (heq : clock (x n) = clock (y n))
      (ha : a ≤ clock (x n)) :
      clock (x (n + 1)) = clock (y (n + 1)) ∧ a ≤ clock (x (n + 1)) := by
    have hx := hxstep n hn ha (hbound n hn)
    have hy := hystep n hn (heq ▸ ha) (heq ▸ hbound n hn)
    constructor
    · rw [hx, hy, heq]
    · linarith
  have hinv : ∀ n ≤ N,
      x n = y n ∨ (clock (x n) = clock (y n) ∧ a ≤ clock (x n)) := by
    intro n
    induction n with
    | zero => intro _; exact Or.inl hzero
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      rcases ih (by omega) with heq | ⟨heq, ha⟩
      · by_cases ha : clock (x n) < a
        · exact Or.inl (hbefore n hn' heq ha)
        · exact Or.inr (hfast n hn' (congrArg clock heq) (le_of_not_gt ha))
      · exact Or.inr (hfast n hn' heq ha)
  intro n hn
  rcases hinv n hn with heq | ⟨heq, _⟩
  · exact congrArg clock heq
  · exact heq

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ClockPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340

theorem exists_complete_clock_passage {t : ℕ → ℝ} {a : ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hstart : t 0 < a) (hunbounded : ∀ A : ℝ, ∃ n, A ≤ t n) :
    ∃ lo hi : ℕ, lo < hi ∧
      a ≤ t lo ∧ t lo < a + 1 ∧
      a + 100 ≤ t hi ∧ t hi < a + 101 ∧
      ∀ n, lo ≤ n → n < hi → a ≤ t n ∧ t n < a + 100 := by
  have hstep' : ∀ n, t (n + 1) - t n ≤ 1 := by
    intro n
    linarith [hstep n]
  obtain ⟨lo, hlo, hloupper, _⟩ :=
    ClockDynamics.exists_first_crossing hstart hstep' (hunbounded a)
  obtain ⟨hi, hhi, hhiupper, hminimal⟩ := ClockDynamics.exists_first_crossing
    (show t 0 < a + 100 by linarith) hstep' (hunbounded (a + 100))
  have hlohi : lo < hi := by
    by_contra h
    have := hmono (show hi ≤ lo by omega)
    linarith
  refine ⟨lo, hi, hlohi, hlo, hloupper, hhi, by linarith, ?_⟩
  intro n hln hnh
  exact ⟨hlo.trans (hmono hln), hminimal n hnh⟩

theorem exists_clock_crossing_between {t : ℕ → ℝ} {a : ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < a)
    (hend : a + 1 ≤ t hi) :
    ∃ n, lo ≤ n ∧ n < hi ∧ a ≤ t n ∧ t n < a + 1 := by
  obtain ⟨k, hklo, hkhi, _⟩ := ClockDynamics.exists_first_crossing
    (t := fun k => t (lo + k)) (a := a) (by simpa using hstart)
    (fun k => by
      have h := hstep (lo + k)
      simp only [Nat.add_assoc] at *
      linarith)
    ⟨hi - lo, by simpa [Nat.add_sub_of_le hlohi] using (by linarith : a ≤ t hi)⟩
  refine ⟨lo + k, by omega, ?_, hklo, hkhi⟩
  by_contra h
  have := hmono (show hi ≤ lo + k by omega)
  linarith

theorem exists_preparation_plateau {t : ℕ → ℝ} {α : ℝ → ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < 1) (hend : 100 ≤ t hi)
    (hplateau : ∀ x, 9 ≤ x → x ≤ 11 → α x = 1) :
    ∃ i ∈ Finset.Ico lo hi, α (t i) = 1 := by
  obtain ⟨i, hlo, hhi, h9, h10⟩ := exists_clock_crossing_between hmono hstep
    hlohi (show t lo < 9 by linarith) (show (9 : ℝ) + 1 ≤ t hi by linarith)
  exact ⟨i, Finset.mem_Ico.mpr ⟨hlo, hhi⟩, hplateau _ h9 (by linarith)⟩

theorem preparation_indices_properties {t : ℕ → ℝ} {α : ℝ → ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < 1) (hend : 100 ≤ t hi)
    (hsupport : ∀ x, 0 < α x → 8 < x ∧ x < 12)
    (hplateau : ∀ x, 9 ≤ x → x ≤ 11 → α x = 1)
    (hunit : ∀ n, 8 ≤ t n → t n ≤ 12 → t (n + 1) = t n + 1) :
    let I := (Finset.Ico lo hi).filter (fun i => 0 < α (t i))
    I.Nonempty ∧ I.card ≤ 5 ∧ ∃ i ∈ I, α (t i) = 1 := by
  classical
  let I := (Finset.Ico lo hi).filter (fun i => 0 < α (t i))
  obtain ⟨i, hiI, hiα⟩ := exists_preparation_plateau hmono hstep hlohi hstart hend hplateau
  have himem : i ∈ I := Finset.mem_filter.mpr ⟨hiI, by rw [hiα]; norm_num⟩
  have hcard : I.card ≤ 5 := by
    apply clock_preparation_card_le_five hmono hunit I
    intro n hn
    exact hsupport (t n) (Finset.mem_filter.mp hn).2
  change I.Nonempty ∧ I.card ≤ 5 ∧ ∃ i ∈ I, α (t i) = 1
  exact ⟨⟨i, himem⟩, by omega, i, himem, hiα⟩

theorem exists_reset_before_preparation {t : ℕ → ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < 1) (hend : 100 ≤ t hi) :
    ∃ r ∈ Finset.Ico lo hi, 2 ≤ t r ∧ t r < 3 ∧
      ∀ i, 8 < t i → r + 1 ≤ i := by
  obtain ⟨r, hlo, hhi, h2, h3⟩ := exists_clock_crossing_between hmono hstep
    hlohi (show t lo < 2 by linarith) (show (2 : ℝ) + 1 ≤ t hi by linarith)
  refine ⟨r, Finset.mem_Ico.mpr ⟨hlo, hhi⟩, h2, by linarith, ?_⟩
  intro i hi
  by_contra h
  have := hmono (show i ≤ r by omega)
  linarith

theorem exists_readout_plateau {t : ℕ → ℝ} {ι : Type*} {β : ι → ℝ → ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < 1) (hend : 100 ≤ t hi)
    (hcover : ∀ x, 76 ≤ x → x ≤ 77 → ∃ l, β l x = 1) :
    ∃ j ∈ Finset.Ico lo hi, 76 ≤ t j ∧ t j < 77 ∧ ∃ l, β l (t j) = 1 := by
  obtain ⟨j, hlo, hhi, h76, h77⟩ := exists_clock_crossing_between hmono hstep
    hlohi (show t lo < 76 by linarith) (show (76 : ℝ) + 1 ≤ t hi by linarith)
  refine ⟨j, Finset.mem_Ico.mpr ⟨hlo, hhi⟩, h76, by linarith, ?_⟩
  exact hcover _ h76 (by linarith)

end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.CompactLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem exists_compact_set_small_fiber_labels {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∃ b : s → Fin K,
      ∀ x y, b x = b y → dist (x : X) (y : X) < ε := by
  classical
  obtain ⟨t, _hts, ht, hcover⟩ := hs.finite_cover_balls (half_pos hε)
  let := ht.fintype
  have hex (x : s) : ∃ c : t, dist (x : X) (c : X) < ε / 2 := by
    have hx := hcover x.property
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    exact ⟨⟨c, hc⟩, hxc⟩
  choose c hc using hex
  refine ⟨Fintype.card t, fun x => (Fintype.equivFin t) (c x), ?_⟩
  intro x y hxy
  have heq : c x = c y := (Fintype.equivFin t).injective hxy
  have hx := hc x
  have hy := hc y
  rw [← heq, dist_comm (y : X) (c x : X)] at hy
  have htriangle := dist_triangle (x : X) (c x : X) (y : X)
  linarith

theorem exists_small_fiber_labels {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∃ b : X → Fin K, ∀ x y, b x = b y → dist x y < ε := by
  obtain ⟨K, b, hb⟩ := exists_compact_set_small_fiber_labels
    (s := (Set.univ : Set X)) isCompact_univ hε
  exact ⟨K, fun x => b ⟨x, Set.mem_univ x⟩,
    fun x y hxy => hb ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩ hxy⟩

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ReadoutCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem340

theorem readoutInterval_length (i : Fin 3) :
    (readoutCenter i + 2 / 5) - (readoutCenter i - 2 / 5) < 1 := by linarith

theorem readoutCoeff_eq_one (i : Fin 3) {t : ℝ}
    (ht : |t - readoutCenter i| ≤ 1 / 4) : readoutCoeff i t = 1 := by
  apply (readoutBump i).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, readoutBump] using ht

theorem readoutCoeff_cover {t : ℝ} (ht : t ∈ Set.Icc 76 77) :
    ∃ i : Fin 3, readoutCoeff i t = 1 := by
  rcases ht with ⟨ht0, ht1⟩
  by_cases h0 : t ≤ 76 + 1 / 4
  · refine ⟨0, readoutCoeff_eq_one 0 ?_⟩
    norm_num [readoutCenter, abs_le]
    constructor <;> linarith
  · by_cases h1 : t ≤ 76 + 3 / 4
    · refine ⟨1, readoutCoeff_eq_one 1 ?_⟩
      norm_num [readoutCenter, abs_le]
      constructor <;> linarith
    · refine ⟨2, readoutCoeff_eq_one 2 ?_⟩
      norm_num [readoutCenter, abs_le]
      constructor <;> linarith

theorem preparationCoeff_nonneg (t : ℝ) : 0 ≤ preparationCoeff t :=
  preparationBump.nonneg

theorem preparationCoeff_le_one (t : ℝ) : preparationCoeff t ≤ 1 :=
  preparationBump.le_one

theorem preparationCoeff_eq_one {t : ℝ} (ht : t ∈ Set.Icc 9 11) :
    preparationCoeff t = 1 := by
  apply preparationBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, Real.dist_eq, preparationBump, abs_le]
  constructor <;> linarith [ht.1, ht.2]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SphereCutoffsAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology

namespace Problem340.SphereCutoffs

theorem affineClockGate_mem_Icc (z : ℂ) : affineClockGate z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem affineClockGate_eq_zero {z : ℂ} (h : ‖z‖ ≤ 1 / 2) :
    affineClockGate z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : affineHeight z ≤ -3 / 5 := by
    apply (div_le_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (norm_nonneg z) h]
  linarith

theorem affinePreparationCutoff_eq_one {z : ℂ}
    (hlo : 1 / 2 ≤ ‖z‖) (hhi : ‖z‖ ≤ 1) : affinePreparationCutoff z = 1 := by
  have hl : -3 / 5 ≤ affineHeight z := by
    apply (le_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hlo]
  have hh : affineHeight z ≤ 0 := by
    apply (div_le_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (norm_nonneg z) hhi]
  unfold affinePreparationCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 5 * affineHeight z + 4),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 1 - 2 * affineHeight z)]
  norm_num

theorem hasCompactSupport_affinePreparationCutoff :
    HasCompactSupport affinePreparationCutoff := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2)
  intro z hz
  have hz' : 2 < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  apply affinePreparationCutoff_eq_zero_of_large
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hz'.le]

theorem onePointClockGate_mem_Icc (z : OnePoint ℂ) :
    onePointClockGate z ∈ Set.Icc (0 : ℝ) 1 := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => exact affineClockGate_mem_Icc z

end Problem340.SphereCutoffs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.GainProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

lemma gainProfile_eq_gain (L : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (7 : ℝ) 90) :
    gainProfile L t = L := by
  have hb : gainBump t = 1 := by
    apply gainBump.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    norm_num [gainBump]
    constructor <;> linarith [ht.1, ht.2]
  simp [gainProfile, hb]

lemma gainProfile_eq_zero (L : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (2 : ℝ) 5) :
    gainProfile L t = 0 := by
  have hb : gainBump t = 0 := by
    apply gainBump.zero_of_le_dist
    rw [Real.dist_eq]
    change (89 / 2 : ℝ) ≤ |t - 51|
    rw [abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.2]
  simp [gainProfile, hb]

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.Saturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Problem340

theorem saturationProfile_monotoneOn (R : ℝ) (hR : 1 ≤ R) :
    MonotoneOn (saturationProfile R hR) (Icc 0 R) := by
  intro a ha b hb hab
  rw [saturationProfile_eq_primitive R hR (by simpa [abs_of_nonneg ha.1] using ha.2),
    saturationProfile_eq_primitive R hR (by simpa [abs_of_nonneg hb.1] using hb.2)]
  exact saturationPrimitive_monotone hab

theorem norm_saturation (R : ℝ) (hR : 1 ≤ R) (z : ℂ) :
    ‖saturation R hR z‖ = saturationProfile R hR ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    simp [saturationProfile, saturationPrimitive]
  · rw [saturation, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (saturationProfile_nonneg R hR (norm_nonneg z))
        (norm_nonneg z)), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

theorem norm_saturation_le_two (R : ℝ) (hR : 1 ≤ R) (z : ℂ) :
    ‖saturation R hR z‖ ≤ 2 := by
  rw [norm_saturation]
  exact saturationProfile_le_two R hR (norm_nonneg z)

theorem norm_sphereSaturation_le_two (R : ℝ) (hR : 1 ≤ R) (z : OnePoint ℂ) :
    ‖sphereSaturation R hR z‖ ≤ 2 := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => exact norm_saturation_le_two R hR z

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem concrete_gate_mem_Icc (L : ℝ) (hL : 2 < L) (z : Sphere) :
    (concreteData L hL).gate z ∈ Set.Icc (0 : ℝ) 1 :=
  SphereCutoffs.onePointClockGate_mem_Icc z

theorem concrete_cutoff_mem_Icc (L : ℝ) (hL : 2 < L) (z : Sphere) :
    (concreteData L hL).cutoff z ∈ Set.Icc (0 : ℝ) 1 :=
  SphereCutoffs.onePointPreparationCutoff_mem_Icc z

@[simp] theorem concrete_gate_zero (L : ℝ) (hL : 2 < L) :
    (concreteData L hL).gate ((0 : ℂ) : Sphere) = 0 := by
  exact SphereCutoffs.affineClockGate_eq_zero (by simp)

theorem concreteMap_infty_zero (L : ℝ) (hL : 2 < L)
    (t : AddCircle (100 : ℝ)) :
    concreteMap L hL (t, ∞, fun _ => ((0 : ℂ) : Sphere)) =
      (t + (1 : ℝ), ∞, fun _ => ((0 : ℂ) : Sphere)) := by
  simp [concreteMap, rawMap]

private theorem readoutCoeff_fifty (i : Fin 3) : readoutCoeff i 50 = 0 := by
  by_contra h
  have hs : (50 : ℝ) ∈ Function.support (readoutCoeff i) := h
  rw [readoutCoeff_support] at hs
  have hb := readoutInterval_subset i hs
  norm_num at hb

@[simp] theorem periodicReadout_fifty (i : Fin 3) :
    periodicReadout i ((50 : ℝ) : AddCircle (100 : ℝ)) = 0 := by
  rw [periodicReadout, AddCircle.liftIco_coe_apply (by norm_num)]
  exact readoutCoeff_fifty i

@[simp] theorem readout_fifty (D : SphereData) (v : Fin 3 → Sphere) :
    readout D ((50 : ℝ) : AddCircle (100 : ℝ)) v = 0 := by
  simp [readout]

@[simp] theorem clockIncrement_fifty_zero (L : ℝ) (hL : 2 < L) :
    clockIncrement (concreteData L hL) ((50 : ℝ) : AddCircle (100 : ℝ))
      ((0 : ℂ) : Sphere) = 0 := by
  rw [clockIncrement, AddCircle.liftIco_coe_apply (by norm_num)]
  simp only [concrete_gate_zero, Clock.increment_zero]
  exact (Clock.barrier_eq_zero_iff 50).2 ⟨0, by norm_num⟩

@[simp] theorem periodicGain_fifty (L : ℝ) (hL : 2 < L) :
    periodicGain (concreteData L hL) ((50 : ℝ) : AddCircle (100 : ℝ)) = L := by
  rw [periodicGain, AddCircle.liftIco_coe_apply (by norm_num)]
  exact gainProfile_eq_gain L (by norm_num)

theorem concreteMap_fifty_zero (L : ℝ) (hL : 2 < L) (v : Fin 3 → Sphere) :
    concreteMap L hL (((50 : ℝ) : AddCircle (100 : ℝ)), ((0 : ℂ) : Sphere), v) =
      (((50 : ℝ) : AddCircle (100 : ℝ)), ((0 : ℂ) : Sphere),
        fun i => (((L : ℂ) * (concreteData L hL).saturation (v i)) : Sphere)) := by
  simp [concreteMap, rawMap]

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapQuotientContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology OnePoint

namespace Problem340.Construction

lemma continuous_readout (D : SphereData) (hS : Continuous D.saturation) :
    Continuous (fun x : AddCircle (100 : ℝ) × (Fin 3 → Sphere) => readout D x.1 x.2) := by
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  exact (Complex.continuous_ofReal.comp ((continuous_periodicReadout i).comp continuous_fst)).mul
    (hS.comp ((continuous_apply i).comp continuous_snd))

lemma continuous_rawMap_of_coefficients (D : SphereData)
    (hg : Continuous D.gate)
    (hinput : ∀ i : Fin 3,
      Continuous (fun x : AddCircle (100 : ℝ) × Sphere => input D i x.1 x.2))
    (hS : Continuous D.saturation) (hperiodicGain : Continuous (periodicGain D)) :
    Continuous (rawMap D) := by
  have hmain : Continuous (fun x : RawManifold => x.2.1) :=
    continuous_fst.comp continuous_snd
  have hregs : Continuous (fun x : RawManifold => x.2.2) :=
    continuous_snd.comp continuous_snd
  have hpair : Continuous (fun x : RawManifold => (x.1, x.2.1)) :=
    continuous_fst.prodMk hmain
  have hc := (continuous_clockIncrement D hg).comp hpair
  have hclock : Continuous (Prod.fst : RawManifold → AddCircle (100 : ℝ)) := continuous_fst
  have hpairRegs := hclock.prodMk hregs
  have hr := (continuous_readout D hS).comp hpairRegs
  have hgain := Complex.continuous_ofReal.comp
    (hperiodicGain.comp hclock)
  have hu (i : Fin 3) :=
    (hinput i).comp hpair
  exact (continuous_fst.add ((AddCircle.continuous_mk' 100).comp hc)).prodMk
    ((continuous_perturbedSquare.comp (hr.prodMk hmain)).prodMk
      (continuous_pi fun i => OnePoint.continuous_coe.comp
        ((hgain.mul (hS.comp ((continuous_apply i).comp hregs))).add (hu i))))

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ConcreteContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem continuous_concrete_baseInput (L : ℝ) (hL : 2 < L) (i : Fin 3) :
    Continuous (fun x : ℝ × Sphere => baseInput (concreteData L hL) i x.1 x.2) := by
  apply continuous_baseInput_of_standard_cutoffs _ rfl rfl
  change 1 < L
  linarith

theorem continuous_concrete_input (L : ℝ) (hL : 2 < L) (i : Fin 3) :
    Continuous (fun x : AddCircle (100 : ℝ) × Sphere =>
      input (concreteData L hL) i x.1 x.2) :=
  continuous_input_of_baseInput _ i (continuous_concrete_baseInput L hL i)

theorem concrete_gain_seam (L : ℝ) (hL : 2 < L) :
    (concreteData L hL).gain 0 = (concreteData L hL).gain 100 := by
  change gainProfile L 0 = gainProfile L 100
  rw [gainProfile_zero_outside (by norm_num), gainProfile_zero_outside (by norm_num)]

theorem continuous_concrete_periodicGain (L : ℝ) (hL : 2 < L) :
    Continuous (periodicGain (concreteData L hL)) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  apply AddCircle.liftIco_zero_continuous
  · exact concrete_gain_seam L hL
  · exact (gainProfile_contDiff L).continuous.continuousOn

theorem continuous_concreteMap (L : ℝ) (hL : 2 < L) :
    Continuous (concreteMap L hL) := by
  apply continuous_rawMap_of_coefficients (concreteData L hL)
  · exact SphereCutoffs.continuous_onePointClockGate
  · exact continuous_concrete_input L hL
  · exact sphereSaturation_continuous (3 * L) _
  · exact continuous_concrete_periodicGain L hL

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RegisterErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter

namespace Problem340.RegisterErasure

theorem recurring_periodic_window
    (t : ℕ → ℝ) (ht : Monotone t) (hunbounded : Tendsto t atTop atTop)
    {P d : ℝ} (hP : 0 < P)
    (hstep : ∀ n, t (n + 1) ≤ t n + d) (a : ℝ) (N : ℕ) :
    ∃ n ≥ N, ∃ k : ℤ, t n ∈ Set.Icc (a + P * (k : ℝ)) (a + P * (k : ℝ) + d) := by
  obtain ⟨k, hk⟩ := exists_int_gt ((t N - a) / P)
  have hthreshold : t N < a + P * (k : ℝ) := by
    have := (div_lt_iff₀ hP).mp hk
    nlinarith
  have hex : ∃ n, a + P * (k : ℝ) ≤ t n :=
    (hunbounded.eventually_ge_atTop (a + P * (k : ℝ))).exists
  let n := Nat.find hex
  have hn : a + P * (k : ℝ) ≤ t n := Nat.find_spec hex
  have hN : N < n := by
    by_contra h
    have hle : n ≤ N := by omega
    exact (not_le_of_gt hthreshold) (hn.trans (ht hle))
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hprev : t m < a + P * (k : ℝ) := by
    apply lt_of_not_ge
    exact Nat.find_min hex (by dsimp [n] at hm; omega)
  refine ⟨n, hN.le, k, hn, ?_⟩
  rw [hm]
  linarith [hstep m]

theorem recurring_zero_gain
    (t a : ℕ → ℝ) (ht : Monotone t) (hunbounded : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hreset : ∀ n (k : ℤ), t n ∈ Set.Icc (2 + 100 * (k : ℝ)) (5 + 100 * (k : ℝ)) → a n = 0) :
    ∀ N, ∃ n ≥ N, a n = 0 := by
  intro N
  obtain ⟨n, hn, k, hlo, hhi⟩ := recurring_periodic_window t ht hunbounded
    (show (0 : ℝ) < 100 by norm_num) hstep 2 N
  exact ⟨n, hn, hreset n k ⟨hlo, by linarith⟩⟩

theorem gain_zero_on_lifted_reset_window
    (A : ℝ → ℝ) (hper : Function.Periodic A 100)
    (hzero : ∀ s ∈ Set.Icc (2 : ℝ) 5, A s = 0)
    (t : ℝ) (k : ℤ)
    (ht : t ∈ Set.Icc (2 + 100 * (k : ℝ)) (5 + 100 * (k : ℝ))) :
    A t = 0 := by
  rw [← hper.sub_int_mul_eq k]
  apply hzero
  constructor <;> nlinarith [ht.1, ht.2]

theorem recurring_zero_periodic_gain
    (t : ℕ → ℝ) (A : ℝ → ℝ) (hper : Function.Periodic A 100)
    (hzero : ∀ s ∈ Set.Icc (2 : ℝ) 5, A s = 0)
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1) :
    ∀ N, ∃ n ≥ N, A (t n) = 0 := by
  apply recurring_zero_gain t (fun n => A (t n)) ht htop hstep
  intro n k hn
  exact gain_zero_on_lifted_reset_window A hper hzero (t n) k hn

theorem eventually_cutoff_zero_of_norm_escape
    {E F : Type*} [SeminormedAddGroup E] [Zero F]
    (χ : E → F) (hχ : HasCompactSupport χ) (z : ℕ → E)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    ∀ᶠ n in atTop, χ (z n) = 0 := by
  obtain ⟨R, hR⟩ := hχ.isCompact.isBounded.exists_norm_le
  filter_upwards [hz.eventually_gt_atTop R] with n hn
  by_contra hne
  exact (not_le_of_gt hn) (hR (z n) (subset_tsupport χ hne))

theorem eventually_base_of_recurring_reset
    {E X : Type*} [AddCommGroup E] [Module ℝ E]
    (base : X) (embed : E → X) (hembed : embed 0 = base)
    (S : X → E) (hS : S base = 0) (a : ℕ → ℝ) (u : ℕ → E) (v : ℕ → X)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + u n))
    (hu : ∀ᶠ n in atTop, u n = 0)
    (hreset : ∀ N, ∃ n ≥ N, a n = 0) :
    ∀ᶠ n in atTop, v n = base := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  obtain ⟨r, hr, ha⟩ := hreset N
  have hzero : v (r + 1) = base := by
    rw [hrec, ha, zero_smul, hN r hr, add_zero, hembed]
  apply eventually_atTop.mpr
  refine ⟨r + 1, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hzero
  | succ n hn ih =>
      rw [hrec, ih, hS, smul_zero, hN n (by omega), add_zero, hembed]

theorem eventually_all_base_of_recurring_reset
    {ι E X : Type*} [AddCommGroup E] [Module ℝ E]
    (base : X) (embed : E → X) (hembed : embed 0 = base)
    (S : X → E) (hS : S base = 0) (a : ℕ → ℝ)
    (u : ℕ → ι → E) (v : ℕ → ι → X)
    (hrec : ∀ n i, v (n + 1) i = embed (a n • S (v n i) + u n i))
    (hu : ∀ᶠ n in atTop, ∀ i, u n i = 0)
    (hreset : ∀ N, ∃ n ≥ N, a n = 0) :
    ∀ᶠ n in atTop, ∀ i, v n i = base := by
  have hp := eventually_base_of_recurring_reset
    (fun _ : ι => base) (fun w : ι → E => fun i => embed (w i))
    (by ext i; exact hembed)
    (fun w : ι → X => fun i => S (w i)) (by ext i; exact hS)
    a u v (fun n => funext (hrec n))
    (hu.mono (fun n hn => funext hn)) hreset
  exact hp.mono (fun n hn i => congrFun hn i)

end Problem340.RegisterErasure

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped OnePoint

namespace Problem340.ConstructionErasure

open Construction

local instance instFactLtRealOfNat_solutions : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

lemma inputTerm_eq_zero_of_cutoff (D : SphereData) (z : Sphere)
    (hz : D.cutoff z = 0) (i : Fin 3) (n : ℕ) (t : ℝ) :
    inputTerm D i n t z = 0 := by
  simp [inputTerm, hz]

lemma baseInput_eq_zero_of_cutoff (D : SphereData) (z : Sphere)
    (hz : D.cutoff z = 0) (i : Fin 3) (t : ℝ) :
    baseInput D i t z = 0 := by
  simp [baseInput, inputTerm_eq_zero_of_cutoff D z hz]

lemma input_eq_zero_of_cutoff (D : SphereData) (z : Sphere)
    (hz : D.cutoff z = 0) (i : Fin 3) (t : AddCircle (100 : ℝ)) :
    input D i t z = 0 := by
  simp [input, AddCircle.liftIco, baseInput_eq_zero_of_cutoff D z hz]

lemma periodicGain_lift_periodic (D : SphereData) :
    Function.Periodic (fun t : ℝ => _root_.OAI.Problem340.Construction.periodicGain D (t : AddCircle (100 : ℝ))) 100 := by
  intro t
  simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]

lemma periodicGain_lift_reset (D : SphereData)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0)
    (s : ℝ) (hs : s ∈ Set.Icc (2 : ℝ) 5) :
    _root_.OAI.Problem340.Construction.periodicGain D (s : AddCircle (100 : ℝ)) = 0 := by
  rw [_root_.OAI.Problem340.Construction.periodicGain, AddCircle.liftIco_zero_coe_apply (show s ∈ Set.Ico (0 : ℝ) 100 by
    constructor <;> linarith [hs.1, hs.2])]
  exact hgain s hs

theorem rawMap_registers_eventually_zero
    (D : SphereData) (x : RawManifold) (t : ℕ → ℝ)
    (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0)
    (hclock : ∀ n, ((rawMap D)^[n] x).1 = (t n : AddCircle (100 : ℝ)))
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hcutoff : ∀ᶠ n in atTop, D.cutoff (((rawMap D)^[n] x).2.1) = 0) :
    ∀ᶠ n in atTop, ∀ i : Fin 3, ((rawMap D)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  apply RegisterErasure.eventually_all_base_of_recurring_reset
    ((0 : ℂ) : Sphere) (fun z : ℂ => (z : Sphere)) rfl
    D.saturation hS
    (fun n => _root_.OAI.Problem340.Construction.periodicGain D (((rawMap D)^[n] x).1))
    (fun n i => input D i (((rawMap D)^[n] x).1) (((rawMap D)^[n] x).2.1))
    (fun n => ((rawMap D)^[n] x).2.2)
  · intro n i
    rw [Function.iterate_succ_apply']
    simp only [rawMap, Complex.real_smul]
  · filter_upwards [hcutoff] with n hn i
    exact input_eq_zero_of_cutoff D _ hn i _
  · intro N
    obtain ⟨n, hn, hzero⟩ := RegisterErasure.recurring_zero_periodic_gain t
      (fun s : ℝ => _root_.OAI.Problem340.Construction.periodicGain D (s : AddCircle (100 : ℝ)))
      (periodicGain_lift_periodic D) (periodicGain_lift_reset D hgain)
      ht htop hstep N
    exact ⟨n, hn, by rw [hclock]; exact hzero⟩

theorem rawMap_registers_eventually_zero_of_norm_escape
    (D : SphereData) (x : RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0)
    (hclock : ∀ n, ((rawMap D)^[n] x).1 = (t n : AddCircle (100 : ℝ)))
    (hmain : ∀ n, ((rawMap D)^[n] x).2.1 = (z n : Sphere))
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hχ : HasCompactSupport (fun w : ℂ => D.cutoff (w : Sphere)))
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    ∀ᶠ n in atTop, ∀ i : Fin 3, ((rawMap D)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  apply rawMap_registers_eventually_zero D x t hS hgain hclock ht htop hstep
  have he := RegisterErasure.eventually_cutoff_zero_of_norm_escape
    (fun w : ℂ => D.cutoff (w : Sphere)) hχ z hz
  filter_upwards [he] with n hn
  simpa only [hmain] using hn

lemma clockIncrement_infty (D : SphereData) (hgate : D.gate ∞ = 1)
    (t : AddCircle (100 : ℝ)) : clockIncrement D t ∞ = 1 := by
  simp [clockIncrement, hgate, AddCircle.liftIco]

theorem rawMap_orbit_infty (D : SphereData) (hgate : D.gate ∞ = 1)
    (t₀ : ℝ) (v : Fin 3 → Sphere) :
    ∀ n, ((rawMap D)^[n] ((t₀ : AddCircle (100 : ℝ)), ∞, v)).1 =
        ((t₀ + n : ℝ) : AddCircle (100 : ℝ)) ∧
      ((rawMap D)^[n] ((t₀ : AddCircle (100 : ℝ)), ∞, v)).2.1 = ∞ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      constructor
      · change (((rawMap D)^[n] ((t₀ : AddCircle (100 : ℝ)), ∞, v)).1 +
          (clockIncrement D _ _ : ℝ)) = _
        rw [ih.2, clockIncrement_infty D hgate, ih.1]
        simp [Nat.cast_add, Nat.cast_one, add_assoc]
      · change perturbedSquare _ (((rawMap D)^[n] _).2.1) = ∞
        rw [ih.2]
        rfl

theorem rawMap_infty_registers_eventually_zero
    (D : SphereData) (t₀ : ℝ) (v : Fin 3 → Sphere)
    (hgate : D.gate ∞ = 1) (hχ : D.cutoff ∞ = 0)
    (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (hgain : ∀ s ∈ Set.Icc (2 : ℝ) 5, D.gain s = 0) :
    ∀ᶠ n in atTop, ∀ i : Fin 3,
      ((rawMap D)^[n] ((t₀ : AddCircle (100 : ℝ)), ∞, v)).2.2 i = ((0 : ℂ) : Sphere) := by
  apply rawMap_registers_eventually_zero D ((t₀ : AddCircle (100 : ℝ)), ∞, v)
    (fun n => t₀ + n) hS hgain
  · intro n
    exact (rawMap_orbit_infty D hgate t₀ v n).1
  · intro m n hmn
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  · exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => t₀) atTop (nhds t₀)).add_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  · intro n
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  · exact Eventually.of_forall (fun n => by rw [(rawMap_orbit_infty D hgate t₀ v n).2, hχ])

end Problem340.ConstructionErasure

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapOrbitLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem liftIco_coe_of_periodic {Y : Type*} {P : ℝ} [Fact (0 < P)]
    (a : ℝ) (f : ℝ → Y) (hf : Function.Periodic f P) (t : ℝ) :
    AddCircle.liftIco P a f (t : AddCircle P) = f t := by
  change f (AddCircle.equivIco P a (t : AddCircle P)) = f t
  rw [← hf.lift_coe (AddCircle.equivIco P a (t : AddCircle P)),
    AddCircle.coe_equivIco, hf.lift_coe]

@[simp] theorem clockIncrement_coe (D : SphereData) (t : ℝ) (z : Sphere) :
    clockIncrement D (t : AddCircle (100 : ℝ)) z = Clock.increment t (D.gate z) :=
  liftIco_coe_of_periodic 0 _ (Clock.increment_periodic (D.gate z)) t

theorem clockIncrement_mem_Icc (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (t : AddCircle (100 : ℝ)) (z : Sphere) :
    clockIncrement D t z ∈ Set.Icc (0 : ℝ) 1 := by
  change Clock.increment ((AddCircle.equivIco 100 0 t : ℝ)) (D.gate z) ∈ _
  exact ⟨Clock.increment_nonneg _ (hgate z).1,
    Clock.increment_le_one _ (hgate z).2⟩

theorem coe_rawClockLift (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (n : ℕ) :
    (rawClockLift D x t₀ n : AddCircle (100 : ℝ)) = ((rawMap D)^[n] x).1 :=
  coe_orbitClockLift 100 (rawMap D) _ Prod.fst (fun _ => rfl) x t₀ h₀ n

theorem rawClockLift_succ (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (n : ℕ) :
    rawClockLift D x t₀ (n + 1) = rawClockLift D x t₀ n +
      Clock.increment (rawClockLift D x t₀ n) (D.gate (((rawMap D)^[n] x).2.1)) := by
  change orbitClockLift _ _ _ _ (n + 1) = _
  rw [orbitClockLift_succ]
  change rawClockLift D x t₀ n + clockIncrement D ((rawMap D)^[n] x).1
    (((rawMap D)^[n] x).2.1) = _
  rw [← coe_rawClockLift D x t₀ h₀ n, clockIncrement_coe]

theorem monotone_rawClockLift (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ) : Monotone (rawClockLift D x t₀) :=
  monotone_orbitClockLift (rawMap D) _
    (fun y => (clockIncrement_mem_Icc D hgate y.1 y.2.1).1) x t₀

theorem rawClockLift_step_bounds (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ) (n : ℕ) :
    rawClockLift D x t₀ (n + 1) - rawClockLift D x t₀ n ∈ Set.Icc (0 : ℝ) 1 :=
  orbitClockLift_step_bounds (rawMap D) _
    (fun y => clockIncrement_mem_Icc D hgate y.1 y.2.1) x t₀ n

theorem coe_rawClockLift_sub_period (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ) :
    ((rawClockLift D x t₀ n - 100 * (k : ℝ) : ℝ) : AddCircle (100 : ℝ)) =
      ((rawMap D)^[n] x).1 := by
  rw [mul_comm (100 : ℝ), ← zsmul_eq_mul, AddCircle.coe_sub,
    AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, sub_zero]
  exact coe_rawClockLift D x t₀ h₀ n

theorem rawClockLift_sub_period_succ (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ) :
    rawClockLift D x t₀ (n + 1) - 100 * (k : ℝ) =
      (rawClockLift D x t₀ n - 100 * (k : ℝ)) +
        Clock.increment (rawClockLift D x t₀ n - 100 * (k : ℝ))
          (D.gate (((rawMap D)^[n] x).2.1)) := by
  have hper := (Clock.increment_periodic (D.gate (((rawMap D)^[n] x).2.1))).sub_int_mul_eq
    (x := rawClockLift D x t₀ n) k
  rw [mul_comm (k : ℝ) 100] at hper
  rw [hper, rawClockLift_succ D x t₀ h₀ n]
  ring

theorem periodicReadout_at_passage_clock (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ)
    (hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100)
    (i : Fin 3) :
    periodicReadout i (((rawMap D)^[n] x).1) =
      readoutCoeff i (rawClockLift D x t₀ n - 100 * (k : ℝ)) := by
  rw [← coe_rawClockLift_sub_period D x t₀ h₀ k n]
  exact AddCircle.liftIco_coe_apply (p := (100 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hs)

theorem main_update_at_passage_clock (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (k : ℤ) (n : ℕ)
    (hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100) :
    ((rawMap D)^[n + 1] x).2.1 =
      perturbedSquare (20 * ∑ i : Fin 3,
        (readoutCoeff i (rawClockLift D x t₀ n - 100 * (k : ℝ)) : ℂ) *
          D.saturation (((rawMap D)^[n] x).2.2 i)) (((rawMap D)^[n] x).2.1) := by
  rw [Function.iterate_succ_apply']
  change perturbedSquare (readout D ((rawMap D)^[n] x).1
    ((rawMap D)^[n] x).2.2) ((rawMap D)^[n] x).2.1 = _
  simp only [readout, periodicReadout_at_passage_clock D x t₀ h₀ k n hs]

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ConcreteErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped OnePoint

namespace Problem340.ConcreteErasure

open Construction ConstructionErasure

local instance instFactLtRealOfNat_solutions_rad4b56_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
theorem concreteMap_registers_eventually_zero_of_norm_escape
    (L : ℝ) (hL : 2 < L) (x : RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (hclock : ∀ n, ((concreteMap L hL)^[n] x).1 = (t n : AddCircle (100 : ℝ)))
    (hmain : ∀ n, ((concreteMap L hL)^[n] x).2.1 = (z n : Sphere))
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    ∀ᶠ n in atTop, ∀ i : Fin 3,
      ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  apply rawMap_registers_eventually_zero_of_norm_escape (concreteData L hL) x t z
    (concrete_saturation_zero L hL)
  · intro s hs
    exact gainProfile_eq_zero L hs
  · exact hclock
  · exact hmain
  · exact ht
  · exact htop
  · exact hstep
  · exact SphereCutoffs.hasCompactSupport_affinePreparationCutoff
  · exact hz

theorem concreteMap_infty_eventually_zero
    (L : ℝ) (hL : 2 < L) (t : AddCircle (100 : ℝ)) (v : Fin 3 → Sphere) :
    ∀ᶠ n in atTop,
      ((concreteMap L hL)^[n] (t, ∞, v)).2.1 = ∞ ∧
      ∀ i : Fin 3, ((concreteMap L hL)^[n] (t, ∞, v)).2.2 i = ((0 : ℂ) : Sphere) := by
  obtain ⟨t₀, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hreg := rawMap_infty_registers_eventually_zero (concreteData L hL) t₀ v
    (concrete_gate_infty L hL) rfl (concrete_saturation_zero L hL)
    (fun s hs => gainProfile_eq_zero L hs)
  filter_upwards [hreg] with n hn
  exact ⟨(rawMap_orbit_infty (concreteData L hL) (concrete_gate_infty L hL) t₀ v n).2, hn⟩

private theorem tendsto_atTop_of_eventually_unit_steps (t : ℕ → ℝ)
    (hstep : ∀ᶠ n in atTop, t (n + 1) = t n + 1) : Tendsto t atTop atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
  have hformula : ∀ m : ℕ, t (m + N) = t N + m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          t (m + 1 + N) = t (m + N + 1) := by congr 1; omega
          _ = t (m + N) + 1 := hN (m + N) (by omega)
          _ = t N + (m + 1 : ℕ) := by rw [ih]; push_cast; ring
  apply (tendsto_add_atTop_iff_nat N).mp
  simp_rw [hformula]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => t N) atTop (nhds (t N))).add_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))

theorem concreteMap_registers_eventually_zero_of_escape
    (L : ℝ) (hL : 2 < L) (x : RawManifold) (z : ℕ → ℂ)
    (hmain : ∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    ∀ᶠ n in atTop, ∀ i : Fin 3,
      ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere) := by
  obtain ⟨t₀, ht₀⟩ := QuotientAddGroup.mk_surjective x.1
  let t := rawClockLift (concreteData L hL) x t₀
  have hunit : ∀ᶠ n in atTop, t (n + 1) = t n + 1 := by
    filter_upwards [hz.eventually_ge_atTop 1] with n hn
    have hgate : (concreteData L hL).gate (((rawMap (concreteData L hL))^[n] x).2.1) = 1 := by
      change (concreteData L hL).gate (((concreteMap L hL)^[n] x).2.1) = 1
      rw [← hmain n]
      apply SphereCutoffs.affineClockGate_eq_one
      linarith
    change rawClockLift _ _ _ (n + 1) = _
    rw [rawClockLift_succ _ _ _ ht₀, hgate, Clock.increment_one]
  apply concreteMap_registers_eventually_zero_of_norm_escape L hL x t z
  · intro n
    exact (coe_rawClockLift _ _ _ ht₀ n).symm
  · intro n
    exact (hmain n).symm
  · exact monotone_rawClockLift _ (concrete_gate_mem_Icc L hL) x t₀
  · exact tendsto_atTop_of_eventually_unit_steps t hunit
  · intro n
    have hs := (rawClockLift_step_bounds _ (concrete_gate_mem_Icc L hL) x t₀ n).2
    change t (n + 1) - t n ≤ 1 at hs
    linarith
  · exact hz

end Problem340.ConcreteErasure

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.EntropyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set Uniformity
open scoped Topology ENNReal

namespace Problem340

lemma log_nat_div_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

lemma expGrowthSup_nat_pow (d : ℕ) :
    ExpGrowth.expGrowthSup (fun n : ℕ => (n : ℝ≥0∞) ^ d) = 0 := by
  have h : Tendsto (fun n : ℕ => (d : ℝ) * (Real.log (n : ℝ) / n))
      atTop (𝓝 0) := by
    simpa using log_nat_div_tendsto_zero.const_mul (d : ℝ)
  have h' := EReal.tendsto_coe.mpr h
  have heq : (fun n : ℕ => ENNReal.log ((n : ℝ≥0∞) ^ d) / (n : EReal))
      =ᶠ[atTop] (fun n : ℕ => (((d : ℝ) * (Real.log (n : ℝ) / n) : ℝ) : EReal)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [ENNReal.log_pow]
    have hlog : ENNReal.log (n : ℝ≥0∞) = (Real.log (n : ℝ) : EReal) := by
      rw [← ENNReal.ofReal_natCast, ENNReal.log_ofReal_of_pos hnR]
    rw [hlog]
    change (((d : ℝ) * Real.log (n : ℝ) / n : ℝ) : EReal) = _
    congr 1
    ring
  exact (h'.congr' heq.symm).limsup_eq

lemma expGrowthSup_le_zero_of_polynomial_bound {u : ℕ → ℝ≥0∞} (C d : ℕ)
    (h : ∀ᶠ n in atTop, u n ≤ (C : ℝ≥0∞) * (n + 1) ^ d) :
    ExpGrowth.expGrowthSup u ≤ 0 := by
  have hbound : ∀ᶠ n in atTop,
      u n ≤ ((C : ℝ≥0∞) * 2 ^ d) * (n : ℝ≥0∞) ^ d := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    apply hn.trans
    calc
      (C : ℝ≥0∞) * (n + 1) ^ d ≤ (C : ℝ≥0∞) * (2 * (n : ℝ≥0∞)) ^ d := by
        gcongr
        exact_mod_cast (show n + 1 ≤ 2 * n by omega)
      _ = ((C : ℝ≥0∞) * 2 ^ d) * (n : ℝ≥0∞) ^ d := by rw [mul_pow, mul_assoc]
  exact (ExpGrowth.expGrowthSup_le_of_eventually_le (by finiteness) hbound).trans_eq
    (expGrowthSup_nat_pow d)

lemma coverEntropy_eq_zero_of_polynomial_net_bound {X : Type*} [UniformSpace X]
    (T : X → X) {F : Set X} (hF : F.Nonempty)
    (h : ∀ U ∈ 𝓤 X, ∃ C d : ℕ, ∀ n : ℕ,
      Dynamics.netMaxcard T F U n ≤ (C * (n + 1) ^ d : ℕ)) :
    Dynamics.coverEntropy T F = 0 := by
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T hF)
  rw [Dynamics.coverEntropy_eq_iSup_netEntropyEntourage]
  apply iSup₂_le
  intro U hU
  obtain ⟨C, d, hbound⟩ := h U hU
  apply expGrowthSup_le_zero_of_polynomial_bound C d
  exact Filter.Eventually.of_forall fun n => by
    simpa using ENat.toENNReal_mono (hbound n)

end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.EntropyCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340.EntropyCoding

theorem card_sparseCode_le (n k : ℕ) (P Q : Type*)
    [Fintype P] [Fintype Q] [Nonempty Q] :
    Fintype.card (SparseCode n k P Q) ≤
      2 ^ n * Fintype.card P ^ n * Fintype.card Q ^ k := by
  classical
  unfold SparseCode
  rw [Fintype.card_sigma]
  calc
    ∑ s : {s : Finset (Fin n) // s.card ≤ k},
        Fintype.card ((Fin n → P) × (s.1 → Q))
      ≤ ∑ _s : {s : Finset (Fin n) // s.card ≤ k},
          Fintype.card P ^ n * Fintype.card Q ^ k := by
            apply Finset.sum_le_sum
            intro s _
            simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_coe]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Fintype.card_pos) s.2)
    _ = Fintype.card {s : Finset (Fin n) // s.card ≤ k} *
        (Fintype.card P ^ n * Fintype.card Q ^ k) := by simp
    _ ≤ 2 ^ n * (Fintype.card P ^ n * Fintype.card Q ^ k) := by
      apply Nat.mul_le_mul_right
      simpa only [Fintype.card_finset, Fintype.card_fin] using
        Fintype.card_subtype_le (fun s : Finset (Fin n) => s.card ≤ k)
    _ = _ := by ac_rfl

open Set SetRel Dynamics

theorem exists_dynCover_of_finite_code {X C : Type*} [Nonempty X] [Fintype C]
    (T : X → X) (U : SetRel X X) (n : ℕ) (code : X → C)
    (hcode : ∀ x y, code x = code y → (x, y) ∈ dynEntourage T U n) :
    ∃ s : Finset X, IsDynCoverOf T Set.univ U n s ∧ s.card ≤ Fintype.card C := by
  classical
  let repr : C → X := fun c =>
    if h : ∃ x, code x = c then Classical.choose h else Classical.arbitrary X
  have hrepr (x : X) : code (repr (code x)) = code x := by
    simp only [repr, dite_eq_left (show ∃ y, code y = code x from ⟨x, rfl⟩)]
    exact Classical.choose_spec (show ∃ y, code y = code x from ⟨x, rfl⟩)
  refine ⟨Finset.univ.image repr, ?_, ?_⟩
  · intro x _
    refine ⟨repr (code x), ?_, hcode x (repr (code x)) (hrepr x).symm⟩
    exact Finset.mem_image.mpr ⟨code x, Finset.mem_univ _, rfl⟩
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)

theorem exists_dynCover_of_sparse_code {X P Q : Type*}
    [Nonempty X] [Fintype P] [Fintype Q] [Nonempty Q]
    (T : X → X) (U : SetRel X X) [U.IsSymm] (m r k : ℕ)
    (p : P → X) (q : Q → X) (code : X → SparseCode r k P Q)
    (hcode : ∀ x (i : Fin r),
      (T^[m * i.val] x, center p q (code x) i) ∈ dynEntourage T U m) :
    ∃ s : Finset X, IsDynCoverOf T Set.univ (U ○ U) (m * r) s ∧
      s.card ≤ 2 ^ r * Fintype.card P ^ r * Fintype.card Q ^ k := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_dynCover_of_finite_code T (U ○ U) (m * r) code (by
    intro x y hxy
    rw [mem_dynEntourage]
    intro j hj
    have hm : 0 < m := by nlinarith
    have hi : j / m < r := Nat.div_lt_of_lt_mul hj
    let i : Fin r := ⟨j / m, hi⟩
    have hx := (mem_dynEntourage.mp (hcode x i)) (j % m) (Nat.mod_lt j hm)
    have hy := (mem_dynEntourage.mp (hcode y i)) (j % m) (Nat.mod_lt j hm)
    rw [hxy] at hx
    have hstep : (T^[j % m] (T^[m * i.val] x),
        T^[j % m] (T^[m * i.val] y)) ∈ U ○ U :=
      ⟨T^[j % m] (center p q (code y) i), hx, U.symm hy⟩
    simpa only [i, ← Function.iterate_add_apply, Nat.mod_add_div] using hstep)
  exact ⟨s, hs, hcard.trans (card_sparseCode_le r k P Q)⟩

theorem card_filter_fin_eq_range (r : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin r => p i.val)).card =
      ((Finset.range r).filter p).card := by
  classical
  have hmap : (Finset.univ.filter (fun i : Fin r => p i.val)).map Fin.valEmbedding =
      (Finset.range r).filter p := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.isLt, hi⟩
    · rintro ⟨hj, hp⟩
      exact ⟨⟨j, hj⟩, hp, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap]

theorem exists_dynCover_of_sparse_visits {X P Q : Type*}
    [Nonempty X] [Fintype P] [Fintype Q] [Nonempty P] [Nonempty Q]
    (T : X → X) (U : SetRel X X) [U.IsSymm] (m r k : ℕ)
    (V : Set X) (p : P → X) (q : Q → X)
    (hp : ∀ x ∈ V, ∃ a : P, (x, p a) ∈ dynEntourage T U m)
    (hq : ∀ x, ∃ b : Q, (x, q b) ∈ dynEntourage T U m)
    (hsparse : ∀ x, (exceptionalBlocks T V m r x).card ≤ k) :
    ∃ s : Finset X, IsDynCoverOf T Set.univ (U ○ U) (m * r) s ∧
      s.card ≤ 2 ^ r * Fintype.card P ^ r * Fintype.card Q ^ k := by
  classical
  let bad (x : X) : Finset (Fin r) := exceptionalBlocks T V m r x
  have good_exists (x : X) (i : Fin r) :
      ∃ a : P, T^[m * i.val] x ∈ V →
        (T^[m * i.val] x, p a) ∈ dynEntourage T U m := by
    by_cases hi : T^[m * i.val] x ∈ V
    · obtain ⟨a, ha⟩ := hp _ hi
      exact ⟨a, fun _ => ha⟩
    · exact ⟨Classical.arbitrary P, fun h => (hi h).elim⟩
  choose good hgood using good_exists
  have other_exists (x : X) (i : Fin r) :
      ∃ b : Q, (T^[m * i.val] x, q b) ∈ dynEntourage T U m := hq _
  choose other hother using other_exists
  let code (x : X) : SparseCode r k P Q :=
    ⟨⟨bad x, hsparse x⟩, good x, fun i => other x i.val⟩
  apply exists_dynCover_of_sparse_code T U m r k p q code
  intro x i
  simp only [center, code]
  split_ifs with hi
  · exact hother x i
  · apply hgood x i
    simpa only [bad, exceptionalBlocks, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi

theorem coverMincard_le_of_sparse_visits {X P Q : Type*}
    [Nonempty X] [Fintype P] [Fintype Q] [Nonempty P] [Nonempty Q]
    (T : X → X) (U : SetRel X X) [U.IsSymm] (m r k : ℕ)
    (V : Set X) (p : P → X) (q : Q → X)
    (hp : ∀ x ∈ V, ∃ a : P, (x, p a) ∈ dynEntourage T U m)
    (hq : ∀ x, ∃ b : Q, (x, q b) ∈ dynEntourage T U m)
    (hsparse : ∀ x, (exceptionalBlocks T V m r x).card ≤ k) :
    coverMincard T Set.univ (U ○ U) (m * r) ≤
      (2 ^ r * Fintype.card P ^ r * Fintype.card Q ^ k : ℕ) := by
  obtain ⟨s, hs, hcard⟩ := exists_dynCover_of_sparse_visits T U m r k V p q hp hq hsparse
  exact hs.coverMincard_le_card.trans (by exact_mod_cast hcard)

end Problem340.EntropyCoding

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SparseVisits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Function Set Filter
open scoped BigOperators

namespace Problem340

theorem birkhoffSum_le_of_good_blocks {X : Type*} (T : X → X) (g : X → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) {J : ℕ} (hg : ∀ x, g x ≤ 1)
    (hblock : ∀ x, ∃ k : ℕ, 0 < k ∧ k ≤ J ∧
      birkhoffSum T g k x ≤ τ * k) :
    ∀ n : ℕ, ∀ x, birkhoffSum T g n x ≤ τ * n + J := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    obtain ⟨k, hkpos, hkJ, hk⟩ := hblock x
    by_cases hkn : k ≤ n
    · have hn : n - k < n := Nat.sub_lt (lt_of_lt_of_le hkpos hkn) hkpos
      have htail := ih (n - k) hn (T^[k] x)
      have hsplit := birkhoffSum_add T g k (n - k) x
      rw [Nat.add_sub_of_le hkn] at hsplit
      rw [hsplit]
      have hcast : (k : ℝ) + (n - k : ℕ) = n := by
        exact_mod_cast Nat.add_sub_of_le hkn
      nlinarith
    · have hsum : birkhoffSum T g n x ≤ (n : ℝ) := by
        unfold birkhoffSum
        calc
          (∑ i ∈ Finset.range n, g (T^[i] x)) ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _hi => hg (T^[i] x)
          _ = n := by simp
      have hnJ : n ≤ J := le_trans (le_of_lt (lt_of_not_ge hkn)) hkJ
      have hnJ' : (n : ℝ) ≤ J := by exact_mod_cast hnJ
      have hnonneg : 0 ≤ τ * (n : ℝ) := mul_nonneg hτ (Nat.cast_nonneg n)
      linarith

theorem exists_good_block_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {g : X → ℝ} (hg : UpperSemicontinuous g)
    {τ : ℝ} (hgood : ∀ x, ∃ n : ℕ, birkhoffSum T g n x < τ * n) :
    ∃ J : ℕ, ∀ x, ∃ k : ℕ, 0 < k ∧ k ≤ J ∧
      birkhoffSum T g k x ≤ τ * k := by
  classical
  let U : ℕ → Set X := fun n => {x | birkhoffSum T g n x < τ * n}
  have hU : ∀ n, IsOpen (U n) := by
    intro n
    have hsum : UpperSemicontinuous (birkhoffSum T g n) := by
      unfold birkhoffSum
      apply upperSemicontinuous_sum
      intro i _hi
      exact hg.comp (hT.iterate i)
    exact hsum.isOpen_preimage (τ * n)
  have hcover : (Set.univ : Set X) ⊆ ⋃ n, U n := by
    intro x _hx
    obtain ⟨n, hn⟩ := hgood x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨s.sup id, ?_⟩
  intro x
  obtain ⟨k, hks, hk⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  refine ⟨k, ?_, Finset.le_sup (f := id) hks, le_of_lt hk⟩
  by_contra h
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
  simp [U, hk0] at hk

theorem exists_good_block_of_eventually_zero {X : Type*} (T : X → X) (g : X → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (x : X)
    (hzero : ∀ᶠ n in atTop, g (T^[n] x) = 0) :
    ∃ n : ℕ, birkhoffSum T g n x < τ * n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hzero
  obtain ⟨n, hn⟩ := exists_nat_gt (birkhoffSum T g N x / τ)
  have htail : birkhoffSum T g n (T^[N] x) = 0 := by
    unfold birkhoffSum
    apply Finset.sum_eq_zero
    intro i _hi
    rw [← Function.iterate_add_apply]
    exact hN (i + N) (Nat.le_add_left N i)
  refine ⟨N + n, ?_⟩
  rw [birkhoffSum_add, htail, add_zero, Nat.cast_add, mul_add]
  have hlt : birkhoffSum T g N x < (n : ℝ) * τ := (div_lt_iff₀ hτ).mp hn
  have hnonneg : 0 ≤ τ * (N : ℝ) := mul_nonneg hτ.le (Nat.cast_nonneg N)
  nlinarith

theorem exists_uniform_birkhoffSum_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {g : X → ℝ} (hg : UpperSemicontinuous g)
    (hg_le : ∀ x, g x ≤ 1)
    (hzero : ∀ x, ∀ᶠ n in atTop, g (T^[n] x) = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ x, birkhoffSum T g n x ≤ τ * n + J := by
  obtain ⟨J, hJ⟩ := exists_good_block_bound hT hg
    (fun x => exists_good_block_of_eventually_zero T g hτ x (hzero x))
  exact ⟨J, birkhoffSum_le_of_good_blocks T g hτ.le hg_le hJ⟩

theorem exists_sparse_visits_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {V : Set X} (hV : IsOpen V)
    (hentry : ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ x,
      (outsideVisitsCount T V n x : ℝ) ≤ τ * n + J := by
  classical
  let g : X → ℝ := Vᶜ.indicator (fun _ => 1)
  have hg : UpperSemicontinuous g := hV.isClosed_compl.upperSemicontinuous_indicator zero_le_one
  have hgle : ∀ x, g x ≤ 1 := by
    intro x
    simp only [g, Set.indicator_apply]
    split_ifs <;> norm_num
  have hgzero : ∀ x, ∀ᶠ n in atTop, g (T^[n] x) = 0 := by
    intro x
    filter_upwards [hentry x] with n hn
    simp [g, hn]
  obtain ⟨J, hJ⟩ := exists_uniform_birkhoffSum_bound hT hg hgle hgzero hτ
  refine ⟨J, ?_⟩
  intro n x
  have hsum : birkhoffSum T g n x =
      (((Finset.range n).filter (fun i => T^[i] x ∉ V)).card : ℝ) := by
    simp only [birkhoffSum, g, Set.indicator_apply, Set.mem_compl_iff]
    rw [← Finset.sum_filter]
    simp
  change (((Finset.range n).filter (fun i => T^[i] x ∉ V)).card : ℝ) ≤ _
  rw [← hsum]
  exact hJ n x

theorem exists_sparse_sampled_visits_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {V : Set X} (hV : IsOpen V)
    (hentry : ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V)
    {m : ℕ} (hm : 0 < m) {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ x,
      (outsideVisitsCount (T^[m]) V n x : ℝ) ≤ τ * n + J := by
  apply exists_sparse_visits_bound (hT.iterate m) hV ?_ hτ
  intro x
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hentry x)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← Function.iterate_mul]
  apply hN (m * n)
  refine hn.trans ?_
  simpa using Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hm)

theorem eventually_mem_of_tendsto_infDist {X : Type*} [PseudoMetricSpace X]
    {K V : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (hV : IsOpen V) (hKV : K ⊆ V) {u : ℕ → X}
    (hu : Tendsto (fun n => Metric.infDist (u n) K) atTop (nhds 0)) :
    ∀ᶠ n in atTop, u n ∈ V := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hV hKV
  filter_upwards [hu.eventually (gt_mem_nhds hδ)] with n hn
  exact hsub ((Metric.mem_thickening_iff_infDist_lt hne).mpr hn)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.EntropySparseCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340.EntropyCoding

open Set SetRel Dynamics

theorem exceptionalBlocks_card_eq_outsideVisitsCount {X : Type*}
    (T : X → X) (V : Set X) (m r : ℕ) (x : X) :
    (exceptionalBlocks T V m r x).card = outsideVisitsCount (T^[m]) V r x := by
  classical
  unfold exceptionalBlocks outsideVisitsCount
  simp only [← Function.iterate_mul]
  exact card_filter_fin_eq_range r (fun i => T^[m * i] x ∉ V)

theorem coverMincard_le_of_sparse_visits_finset {X : Type*} [Nonempty X]
    (T : X → X) (U : SetRel X X) [U.IsSymm] (m r k : ℕ)
    (V : Set X) (p q : Finset X) (hpne : p.Nonempty) (hqne : q.Nonempty)
    (hp : IsDynCoverOf T V U m p) (hq : IsDynCoverOf T Set.univ U m q)
    (hsparse : ∀ x, outsideVisitsCount (T^[m]) V r x ≤ k) :
    coverMincard T Set.univ (U ○ U) (m * r) ≤
      (2 ^ r * p.card ^ r * q.card ^ k : ℕ) := by
  classical
  let : Nonempty p := Finset.Nonempty.coe_sort hpne
  let : Nonempty q := Finset.Nonempty.coe_sort hqne
  have hp' : ∀ x ∈ V, ∃ a : p, (x, (a : X)) ∈ dynEntourage T U m := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hp hx
    exact ⟨⟨a, ha⟩, hax⟩
  have hq' : ∀ x, ∃ b : q, (x, (b : X)) ∈ dynEntourage T U m := by
    intro x
    obtain ⟨b, hb, hbx⟩ := hq (Set.mem_univ x)
    exact ⟨⟨b, hb⟩, hbx⟩
  have hsparse' : ∀ x, (exceptionalBlocks T V m r x).card ≤ k := by
    intro x
    rw [exceptionalBlocks_card_eq_outsideVisitsCount]
    exact hsparse x
  simpa only [Fintype.card_coe] using
    coverMincard_le_of_sparse_visits T U m r k V
      (fun a : p => (a : X)) (fun b : q => (b : X)) hp' hq' hsparse'

theorem exists_open_neighborhood_dynCover {X : Type*} [TopologicalSpace X]
    {T : X → X} (hT : Continuous T) {U : SetRel X X} (hU : IsOpen U)
    {K : Set X} {m : ℕ} {p : Finset X} (hp : IsDynCoverOf T K U m p) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ IsDynCoverOf T V U m p := by
  let V : Set X := ⋃ a ∈ p, {x | (x, a) ∈ dynEntourage T U m}
  have hopen : IsOpen V := by
    apply isOpen_iUnion
    intro a
    apply isOpen_iUnion
    intro _
    exact (isOpen.dynEntourage hT hU m).preimage (continuous_id.prodMk continuous_const)
  refine ⟨V, hopen, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hp hx
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hxa⟩⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨a, ha, hxa⟩

end Problem340.EntropyCoding

end OAI
end

section
-- module Solutions.OAIQW_Problem340.EntropyLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set SetRel Filter Function Dynamics
open scoped Topology Uniformity

namespace Problem340

lemma ereal_le_of_sparse_block_bounds {H : EReal} {A B m : ℝ}
    (h : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      H ≤ (((A + τ * B + C / n) / m : ℝ) : EReal)) :
    H ≤ ((A / m : ℝ) : EReal) := by
  have hτ : ∀ τ : ℝ, 0 < τ → H ≤ (((A + τ * B) / m : ℝ) : EReal) := by
    intro τ hτ
    obtain ⟨C, hC⟩ := h τ hτ
    have hlim : Tendsto (fun n : ℕ => (A + τ * B + C / n) / m)
        atTop (𝓝 ((A + τ * B) / m)) := by
      simpa using (tendsto_const_nhds.add
        (tendsto_const_div_atTop_nhds_zero_nat C)).div_const m
    apply ge_of_tendsto (EReal.tendsto_coe.mpr hlim)
    exact eventually_atTop.mpr ⟨1, fun n hn => hC n (by omega)⟩
  have hlim : Tendsto (fun n : ℕ => (A + (1 / ((n : ℝ) + 1)) * B) / m)
      atTop (𝓝 (A / m)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const B)).div_const m
  apply ge_of_tendsto (EReal.tendsto_coe.mpr hlim)
  exact Eventually.of_forall fun n => hτ _ (by positivity)

lemma IsDynCoverOf.entropy_le_real_log_card_div {X : Type*}
    {T : X → X} {F : Set X} {U : SetRel X X} [U.IsSymm]
    (hF : MapsTo T F F) {s : Finset X} {n : ℕ}
    (hn : 0 < n) (hs : 0 < s.card) (hcover : IsDynCoverOf T F U n s) :
    coverEntropyEntourage T F (U ○ U) ≤
      ((Real.log (s.card : ℝ) / n : ℝ) : EReal) := by
  have h := hcover.coverEntropyEntourage_le_log_card_div hF (Nat.ne_of_gt hn)
  have hlog : ENNReal.log (s.card : ENNReal) = (Real.log (s.card : ℝ) : EReal) := by
    rw [ENNReal.log_pos_real (by exact_mod_cast Nat.ne_of_gt hs) (by simp)]
    simp
  rw [hlog] at h
  simpa only [EReal.coe_div, EReal.coe_natCast] using h

lemma log_sparse_word_bound {P Q m r k J : ℕ} {τ : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hm : 0 < m) (hr : 0 < r)
    (hk : (k : ℝ) ≤ τ * r + J) :
    Real.log ((2 ^ r * P ^ r * Q ^ k : ℕ) : ℝ) / (m * r) ≤
      (Real.log 2 + Real.log P + τ * Real.log Q +
        ((J : ℝ) * Real.log Q) / r) / m := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
  have hlog : Real.log ((2 ^ r * P ^ r * Q ^ k : ℕ) : ℝ) =
      (r : ℝ) * Real.log 2 + r * Real.log P + k * Real.log Q := by
    push_cast
    rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ hP'.ne')) (pow_ne_zero _ hQ'.ne'),
      Real.log_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hP'.ne'),
      Real.log_pow, Real.log_pow, Real.log_pow]
  rw [hlog]
  apply (div_le_div_iff₀ (mul_pos hm' hr') hm').mpr
  have hcost := mul_le_mul_of_nonneg_right hk hlogQ
  have hcancel : ((J : ℝ) * Real.log Q / r) * r = J * Real.log Q :=
    div_mul_cancel₀ _ hr'.ne'
  nlinarith

theorem coverEntropyEntourage_le_of_sparse_block_covers {X : Type*}
    {T : X → X} {F : Set X} {U : SetRel X X} [U.IsSymm]
    (hF : MapsTo T F F) (hFne : F.Nonempty) {P Q m : ℕ}
    (hP : 0 < P) (hQ : 0 < Q) (hm : 0 < m)
    (hcodes : ∀ τ : ℝ, 0 < τ → ∃ J : ℕ, ∀ r : ℕ,
      ∃ s : Finset X, ∃ k : ℕ, IsDynCoverOf T F U (m * r) s ∧
        s.card ≤ 2 ^ r * P ^ r * Q ^ k ∧ (k : ℝ) ≤ τ * r + J) :
    coverEntropyEntourage T F (U ○ U) ≤
      (((Real.log 2 + Real.log P) / m : ℝ) : EReal) := by
  apply ereal_le_of_sparse_block_bounds (B := Real.log Q)
  intro τ hτ
  obtain ⟨J, hJ⟩ := hcodes τ hτ
  refine ⟨(J : ℝ) * Real.log Q, ?_⟩
  intro r hr
  obtain ⟨s, k, hcover, hcard, hk⟩ := hJ r
  have hs : 0 < s.card := Finset.card_pos.mpr (by
    simpa only [Finset.coe_nonempty] using hcover.nonempty hFne)
  have hlog : Real.log (s.card : ℝ) ≤
      Real.log ((2 ^ r * P ^ r * Q ^ k : ℕ) : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hs)
    exact_mod_cast hcard
  have hdiv : Real.log (s.card : ℝ) / (m * r) ≤
      (Real.log 2 + Real.log P + τ * Real.log Q +
        ((J : ℝ) * Real.log Q) / r) / m :=
    (div_le_div_of_nonneg_right hlog (by positivity)).trans
      (log_sparse_word_bound hP hQ hm hr hk)
  exact (IsDynCoverOf.entropy_le_real_log_card_div hF (Nat.mul_pos hm hr) hs hcover).trans
    (by exact_mod_cast hdiv)

lemma exists_small_log_dynCover_of_zero_entropy {X : Type*} [UniformSpace X]
    {T : X → X} {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    (hInv : MapsTo T K K) (hzero : coverEntropy T K = 0)
    {U : SetRel X X} (hU : U ∈ 𝓤 X) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ s : Finset X,
      IsDynCoverOf T K U m s ∧ 0 < s.card ∧
        (Real.log 2 + Real.log (s.card : ℝ)) / m < ε := by
  have hrate : ExpGrowth.expGrowthSup (fun n => (coverMincard T K U n).toENNReal) <
      ((ε / 2 : ℝ) : EReal) := by
    have hh := coverEntropyEntourage_le_coverEntropy T K hU
    rw [hzero] at hh
    exact hh.trans_lt (by exact_mod_cast (half_pos hε))
  have hbound := ExpGrowth.eventually_le_exp hrate
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.log 2 / n < ε / 2 :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).eventually_lt_const (half_pos hε)
  have hex : ∀ᶠ m : ℕ in atTop, N ≤ m ∧ 0 < m ∧ ∃ s : Finset X,
      IsDynCoverOf T K U m s ∧ 0 < s.card ∧
        (Real.log 2 + Real.log (s.card : ℝ)) / m < ε := by
    filter_upwards [hbound, hsmall, eventually_ge_atTop N, eventually_ge_atTop 1]
      with m hm hsmall hmN hm1
    obtain ⟨s, hcover, hcard⟩ := (coverMincard_finite_iff T K U m).mp
      (coverMincard_finite_of_isCompact_invariant hK hInv hU m)
    have hs : 0 < s.card := Finset.card_pos.mpr (by
      simpa only [Finset.coe_nonempty] using hcover.nonempty hKne)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    refine ⟨hmN, by omega, s, hcover, hs, ?_⟩
    rw [← hcard, ENat.toENNReal_coe] at hm
    have hlog := ENNReal.log_monotone hm
    rw [EReal.log_exp, ENNReal.log_pos_real (by exact_mod_cast Nat.ne_of_gt hs)
      (by simp)] at hlog
    have hreal : Real.log (s.card : ℝ) ≤ (ε / 2) * m := by
      simpa only [ENNReal.toReal_natCast, ← EReal.coe_natCast,
        ← EReal.coe_mul, EReal.coe_le_coe_iff] using hlog
    have hdiv : Real.log (s.card : ℝ) / m ≤ ε / 2 :=
      (div_le_iff₀ hmpos).mpr hreal
    rw [add_div]
    linarith
  exact hex.exists

theorem entropy_le_of_neighborhood_attracting_dynCover {X : Type*}
    [UniformSpace X] [CompactSpace X] [Nonempty X]
    {T : X → X} (hT : Continuous T) {K : Set X}
    (_hK : IsCompact K) (hKne : K.Nonempty)
    (hattract : ∀ V : Set X, IsOpen V → K ⊆ V →
      ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V)
    {U : SetRel X X} [U.IsSymm] (hU : U ∈ 𝓤 X) (hUopen : IsOpen U)
    {m : ℕ} (hm : 0 < m) {p : Finset X}
    (hp : IsDynCoverOf T K U m p) :
    coverEntropyEntourage T Set.univ ((U ○ U) ○ (U ○ U)) ≤
      (((Real.log 2 + Real.log p.card) / m : ℝ) : EReal) := by
  classical
  obtain ⟨V, hV, hKV, hpV⟩ :=
    EntropyCoding.exists_open_neighborhood_dynCover hT hUopen hp
  obtain ⟨q, hq⟩ := exists_isDynCoverOf_of_isCompact_invariant
    isCompact_univ (show MapsTo T Set.univ Set.univ from fun _ _ => mem_univ _) hU m
  have hpne : p.Nonempty := by
    simpa only [Finset.coe_nonempty] using hp.nonempty hKne
  have hqne : q.Nonempty := by
    simpa only [Finset.coe_nonempty] using hq.nonempty (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
  apply coverEntropyEntourage_le_of_sparse_block_covers
    (show MapsTo T Set.univ Set.univ from fun _ _ => mem_univ _)
    Set.univ_nonempty (Finset.card_pos.mpr hpne) (Finset.card_pos.mpr hqne) hm
  intro τ hτ
  obtain ⟨J, hJ⟩ := exists_sparse_sampled_visits_bound
    hT hV (hattract V hV hKV) hm hτ
  refine ⟨J, ?_⟩
  intro r
  let k := ⌊τ * (r : ℝ) + J⌋₊
  have hbound : coverMincard T Set.univ (U ○ U) (m * r) ≤
      (2 ^ r * p.card ^ r * q.card ^ k : ℕ) := by
    apply EntropyCoding.coverMincard_le_of_sparse_visits_finset
      T U m r k V p q hpne hqne hpV hq
    intro x
    exact Nat.le_floor (hJ r x)
  have hfinite : coverMincard T Set.univ (U ○ U) (m * r) < ⊤ :=
    hbound.trans_lt (WithTop.coe_lt_top _)
  obtain ⟨s, hs, hscard⟩ :=
    (coverMincard_finite_iff T Set.univ (U ○ U) (m * r)).mp hfinite
  refine ⟨s, k, hs, ?_, Nat.floor_le (by positivity)⟩
  rw [← hscard] at hbound
  exact_mod_cast hbound

theorem coverEntropy_eq_zero_of_neighborhood_attraction {X : Type*}
    [UniformSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hInv : MapsTo T K K)
    (hzero : coverEntropy T K = 0)
    (hattract : ∀ V : Set X, IsOpen V → K ⊆ V →
      ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V) :
    coverEntropy T Set.univ = 0 := by
  let : Nonempty X := hKne.nonempty
  apply le_antisymm ?_ (coverEntropy_nonneg T Set.univ_nonempty)
  apply iSup₂_le
  intro U hU
  obtain ⟨V, hV, hVopen, hVsymm, hVU⟩ := comp_open_symm_mem_uniformity_sets hU
  obtain ⟨W, hW, hWopen, hWsymm, hWV⟩ := comp_open_symm_mem_uniformity_sets hV
  let : SetRel.IsSymm W := hWsymm
  have hsub : ((W ○ W) ○ (W ○ W)) ⊆ U :=
    (SetRel.comp_subset_comp hWV hWV).trans hVU
  have hsmall : ∀ ε : ℝ, 0 < ε → coverEntropyEntourage T Set.univ U ≤ (ε : EReal) := by
    intro ε hε
    obtain ⟨m, hm1, hm, p, hp, hpne, hlog⟩ :=
      exists_small_log_dynCover_of_zero_entropy hK hKne hInv hzero hW hε 1
    have hlocal := entropy_le_of_neighborhood_attracting_dynCover hT hK hKne hattract hW hWopen hm hp
    exact (coverEntropyEntourage_antitone T Set.univ hsub).trans
      (hlocal.trans (EReal.coe_le_coe hlog.le))
  have hlim : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : EReal))
      atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ge_of_tendsto' hlim fun n => hsmall _ (by positivity)

theorem coverEntropy_eq_zero_of_pointwise_attraction {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hInv : MapsTo T K K)
    (hzero : coverEntropy T K = 0)
    (hattract : ∀ x, Tendsto (fun n => Metric.infDist (T^[n] x) K) atTop (𝓝 0)) :
    coverEntropy T Set.univ = 0 := by
  apply coverEntropy_eq_zero_of_neighborhood_attraction hT hK hKne hInv hzero
  intro V hV hKV x
  exact eventually_mem_of_tendsto_infDist hK hKne hV hKV (hattract x)

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PhaseAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem aligned_square_norm
    (z θ : ℂ) (r c : ℝ) (hθ : ‖θ‖ = 1) (hz : z = (r : ℂ) * θ)
    (_hr : 0 ≤ r) (hc : 0 ≤ c) :
    ‖z ^ 2 + (c : ℂ) * θ ^ 2‖ = r ^ 2 + c := by
  rw [hz]
  have halign : ((r : ℂ) * θ) ^ 2 + (c : ℂ) * θ ^ 2 =
      ((r ^ 2 + c : ℝ) : ℂ) * θ ^ 2 := by push_cast; ring
  rw [halign, norm_mul, norm_pow, hθ, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact add_nonneg (sq_nonneg r) hc

theorem aligned_square_ne_zero
    (z θ : ℂ) (r c : ℝ) (hθ : ‖θ‖ = 1) (hz : z = (r : ℂ) * θ)
    (hr : 0 < r) (hc : 0 ≤ c) :
    z ^ 2 + (c : ℂ) * θ ^ 2 ≠ 0 := by
  apply norm_pos_iff.mp
  rw [aligned_square_norm z θ r c hθ hz hr.le hc]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) hc

theorem pow_two_pow_le_of_square_le
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hstep : ∀ n, (r n) ^ 2 ≤ r (n + 1)) (n : ℕ) :
    (r 0) ^ (2 ^ n) ≤ r n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (r 0) ^ (2 ^ (n + 1)) = ((r 0) ^ (2 ^ n)) ^ 2 := by
          rw [pow_succ, pow_mul]
        _ ≤ (r n) ^ 2 := pow_le_pow_left₀ (pow_nonneg (hr 0) _) ih 2
        _ ≤ r (n + 1) := hstep n

theorem tendsto_atTop_of_square_le
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hstep : ∀ n, (r n) ^ 2 ≤ r (n + 1)) (hinit : 1 < r 0) :
    Filter.Tendsto r Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (pow_two_pow_le_of_square_le r hr hstep)
  exact (tendsto_pow_atTop_atTop_of_one_lt hinit).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))

theorem aligned_orbit_phase_until
    (z : ℕ → ℂ) (c : ℕ → ℝ) (θ : ℂ) (N : ℕ)
    (hθ : ‖θ‖ = 1) (hc : ∀ n, 0 ≤ c n)
    (hinit : z 0 = (‖z 0‖ : ℂ) * θ) (hz0 : z 0 ≠ 0)
    (hstep : ∀ n, n < N → z (n + 1) = z n ^ 2 + (c n : ℂ) * θ ^ (2 ^ (n + 1))) :
    ∀ n, n ≤ N → z n ≠ 0 ∧ z n = (‖z n‖ : ℂ) * θ ^ (2 ^ n) := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa using And.intro hz0 hinit
  | succ n ih =>
      intro hnN
      have ih := ih (by omega)
      have hstepn := hstep n (by omega)
      have hu : ‖θ ^ (2 ^ n)‖ = 1 := by rw [norm_pow, hθ, one_pow]
      have hpow : θ ^ (2 ^ (n + 1)) = (θ ^ (2 ^ n)) ^ 2 := by
        rw [pow_succ, pow_mul]
      have hn : 0 < ‖z n‖ := norm_pos_iff.mpr ih.1
      have hnorm : ‖z (n + 1)‖ = ‖z n‖ ^ 2 + c n := by
        rw [hstepn, hpow]
        exact aligned_square_norm _ _ _ _ hu ih.2 hn.le (hc n)
      constructor
      · rw [hstepn, hpow]
        exact aligned_square_ne_zero _ _ _ _ hu ih.2 hn (hc n)
      · rw [hnorm]
        conv_lhs => rw [hstepn, ih.2]
        rw [hpow]
        push_cast
        ring

theorem aligned_readout_sum
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (a : ι → ℝ) (β : κ → ℝ) (v : κ → ℂ) (θ : ℂ)
    (hv : ∀ l ∈ J, v l = ((β l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (a i : ℂ) * θ) :
    (20 : ℂ) * (∑ l ∈ J, (β l : ℂ) * v l) =
      ((2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, a i) : ℝ) : ℂ) * θ := by
  have hs : (∑ l ∈ J, (β l : ℂ) * v l) =
      ((∑ l ∈ J, (β l : ℂ) ^ 2) / 10) *
        (∑ i ∈ I, (a i : ℂ)) * θ := by
    calc
      (∑ l ∈ J, (β l : ℂ) * v l) =
          ∑ l ∈ J, ((β l : ℂ) ^ 2 / 10) *
            (∑ i ∈ I, (a i : ℂ)) * θ := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hv l hl, ← Finset.sum_mul]
        push_cast
        ring
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div]
  rw [hs]
  push_cast
  ring

theorem readout_gain_ge_two
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (a : ι → ℝ) (β : κ → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i)
    (hi : ∃ i ∈ I, a i = 1) (hl : ∃ l ∈ J, β l = 1) :
    2 ≤ 2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, a i) := by
  obtain ⟨i, hiI, hai⟩ := hi
  obtain ⟨l, hlJ, hβl⟩ := hl
  have hsA : 1 ≤ ∑ i ∈ I, a i := by
    simpa [hai] using Finset.single_le_sum ha hiI
  have hsB : 1 ≤ ∑ l ∈ J, β l ^ 2 := by
    simpa [hβl] using Finset.single_le_sum (fun l _ => sq_nonneg (β l)) hlJ
  nlinarith [mul_le_mul hsB hsA (by norm_num : (0 : ℝ) ≤ 1)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hsB)]

theorem tendsto_atTop_of_eventually_square_le
    (r : ℕ → ℝ) (N : ℕ) (hr : ∀ n, N ≤ n → 0 ≤ r n)
    (hstep : ∀ n, N ≤ n → (r n) ^ 2 ≤ r (n + 1)) (hinit : 1 < r N) :
    Filter.Tendsto r Filter.atTop Filter.atTop := by
  apply (Filter.tendsto_add_atTop_iff_nat N).1
  apply tendsto_atTop_of_square_le (fun n => r (n + N))
  · intro n
    exact hr _ (Nat.le_add_left _ _)
  · intro n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hstep (n + N) (Nat.le_add_left _ _)
  · simpa using hinit

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.GlobalEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set
open scoped Topology
open scoped OnePoint

namespace Problem340.GlobalEscape

theorem tendsto_coe_infty_of_norm {ι E : Type*} [NormedAddCommGroup E]
    [ProperSpace E] {l : Filter ι} {z : ι → E}
    (hz : Tendsto (fun n => ‖z n‖) l atTop) :
    Tendsto (fun n => (z n : OnePoint E)) l (𝓝 ∞) := by
  have hc : Tendsto z l (coclosedCompact E) := by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp hz
  exact OnePoint.tendsto_coe_infty.comp hc

lemma period_le_of_readout {t : ℝ} {k₀ k : ℤ}
    (hlo : 100 * (k₀ : ℝ) ≤ t) (hhi : t < 100 * (k : ℝ) + 80) :
    k₀ ≤ k := by
  by_contra h
  have hk : k + 1 ≤ k₀ := by omega
  have hkR : (k : ℝ) + 1 ≤ k₀ := by exact_mod_cast hk
  linarith

theorem square_le_after_passage
    (t r : ℕ → ℝ) (ht : Monotone t)
    (hgap : ∀ n, (∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < t n ∧
      t n < 100 * (k : ℝ) + 80)) → (r n) ^ 2 ≤ r (n + 1))
    (hpass : ∀ k : ℤ, t 0 < 100 * (k : ℝ) →
      ∃ s hi : ℕ, t s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ t hi ∧
        ∀ n, s ≤ n → n < hi → (r n) ^ 2 ≤ r (n + 1))
    {k₀ : ℤ} {N : ℕ} (hstart : t 0 < 100 * (k₀ : ℝ))
    (hN : 100 * (k₀ : ℝ) ≤ t N) :
    ∀ n, N ≤ n → (r n) ^ 2 ≤ r (n + 1) := by
  intro n hn
  by_cases hquiet : ∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < t n ∧
      t n < 100 * (k : ℝ) + 80)
  · exact hgap n hquiet
  push Not at hquiet
  obtain ⟨k, hklo, hkhi⟩ := hquiet
  have hk : k₀ ≤ k := period_le_of_readout (hN.trans (ht hn)) hkhi
  have hkR : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨s, hi, hs, hhi, hbound⟩ := hpass k (by linarith)
  apply hbound n
  · by_contra h
    have hns : n ≤ s := by omega
    have := ht hns
    linarith
  · by_contra h
    have hhin : hi ≤ n := by omega
    have := ht hhin
    linarith

theorem tendsto_atTop_of_passage_bounds
    (t r : ℕ → ℝ) (ht : Monotone t) (hr : ∀ n, 0 ≤ r n)
    (hgap : ∀ n, (∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < t n ∧
      t n < 100 * (k : ℝ) + 80)) → (r n) ^ 2 ≤ r (n + 1))
    (hpass : ∀ k : ℤ, t 0 < 100 * (k : ℝ) →
      ∃ s hi : ℕ, t s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ t hi ∧
        ∀ n, s ≤ n → n < hi → (r n) ^ 2 ≤ r (n + 1))
    (hlarge : ∃ k₀ : ℤ, ∃ N : ℕ, t 0 < 100 * (k₀ : ℝ) ∧
      100 * (k₀ : ℝ) ≤ t N ∧ 1 < r N) :
    Tendsto r atTop atTop := by
  obtain ⟨k₀, N, hstart, hN, hrN⟩ := hlarge
  exact Problem340.tendsto_atTop_of_eventually_square_le r N
    (fun n _ => hr n) (square_le_after_passage t r ht hgap hpass hstart hN) hrN

theorem tendsto_atTop_of_complete_passages
    (t r : ℕ → ℝ) (ht : Monotone t) (hr : ∀ n, 0 ≤ r n)
    (hgap : ∀ n, (∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < t n ∧
      t n < 100 * (k : ℝ) + 80)) → (r n) ^ 2 ≤ r (n + 1))
    (hpass : ∀ k : ℤ, t 0 < 100 * (k : ℝ) →
      ∃ s hi : ℕ, 100 * (k : ℝ) ≤ t s ∧ t s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ t hi ∧
        (∀ n, s ≤ n → n < hi → (r n) ^ 2 ≤ r (n + 1)) ∧
        ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < r j) :
    Tendsto r atTop atTop := by
  apply tendsto_atTop_of_passage_bounds t r ht hr hgap
  · intro k hk
    obtain ⟨s, hi, _, hs, hhi, hsq, _⟩ := hpass k hk
    exact ⟨s, hi, hs, hhi, hsq⟩
  · obtain ⟨k, hk⟩ := exists_int_gt (t 0 / 100)
    have hk' : t 0 < 100 * (k : ℝ) := by linarith
    obtain ⟨s, hi, hs, _, _, _, j, hsj, _, hj⟩ := hpass k hk'
    exact ⟨k, j, hk', hs.trans (ht hsj), hj⟩

end Problem340.GlobalEscape

end OAI
end

section
-- module Solutions.OAIQW_Problem340.ImageEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set SetRel UniformSpace
open scoped Uniformity ENNReal

namespace Problem340

theorem dynCover_prefix_product
    {X : Type*} [Nonempty X] (T : X → X) (F : Set X)
    (U : SetRel X X) [U.IsSymm] (n : ℕ) (s t : Finset X)
    (hs : Dynamics.IsDynCoverOf T F U 1 s)
    (ht : Dynamics.IsDynCoverOf T (T '' F) U n t) :
    ∃ c : Finset X,
      Dynamics.IsDynCoverOf T F (U ○ U) (n + 1) c ∧
      c.card ≤ s.card * t.card := by
  classical
  have hchoose : ∀ p : s × t, ∃ y : X, ∀ x ∈ F,
      (x, (p.1 : X)) ∈ U → (T x, (p.2 : X)) ∈ Dynamics.dynEntourage T U n →
      (x, y) ∈ Dynamics.dynEntourage T (U ○ U) (n + 1) := by
    intro p
    by_cases h : ∃ z ∈ F, (z, (p.1 : X)) ∈ U ∧
        (T z, (p.2 : X)) ∈ Dynamics.dynEntourage T U n
    · obtain ⟨z, hzF, hzU, hzD⟩ := h
      refine ⟨z, ?_⟩
      intro x hxF hxU hxD
      rw [Dynamics.mem_dynEntourage]
      intro k hk
      cases k with
      | zero =>
          simpa only [Function.iterate_zero, id_eq] using
            (show (x, z) ∈ U ○ U from ⟨p.1, hxU, U.symm hzU⟩)
      | succ k =>
          have hk' : k < n := Nat.lt_of_succ_lt_succ hk
          have hxk := Dynamics.mem_dynEntourage.mp hxD k hk'
          have hzk := Dynamics.mem_dynEntourage.mp hzD k hk'
          simpa only [Function.iterate_succ_apply] using
            (show (T^[k] (T x), T^[k] (T z)) ∈ U ○ U from
              ⟨T^[k] (p.2 : X), hxk, U.symm hzk⟩)
    · refine ⟨Classical.choice inferInstance, ?_⟩
      intro x hxF hxU hxD
      exact (h ⟨x, hxF, hxU, hxD⟩).elim
  choose pick hpick using hchoose
  refine ⟨Finset.univ.image pick, ?_, ?_⟩
  · intro x hxF
    obtain ⟨a, ha, hxa⟩ := hs hxF
    obtain ⟨b, hb, hxb⟩ := ht (mem_image_of_mem T hxF)
    let p : s × t := (⟨a, ha⟩, ⟨b, hb⟩)
    refine ⟨pick p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, ?_⟩
    apply hpick p x hxF
    · simpa only [Dynamics.dynEntourage_one] using hxa
    · exact hxb
  · exact (Finset.card_image_le).trans (by simp)

theorem coverMincard_le_initial_card_mul_image
    {X : Type*} [Nonempty X] (T : X → X) (F : Set X)
    (U : SetRel X X) [U.IsSymm] (s : Finset X)
    (hs : Dynamics.IsDynCoverOf T F U 1 s) (n : ℕ) :
    Dynamics.coverMincard T F (U ○ U) n ≤
      (s.card : ℕ∞) * Dynamics.coverMincard T (T '' F) U n := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [Dynamics.coverMincard_empty]
  rcases eq_top_or_lt_top (Dynamics.coverMincard T (T '' F) U n) with htop | hfin
  · have hcard : (s.card : ℕ∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr (hs.nonempty hF)).ne'
    simp [htop, hcard]
  · obtain ⟨t, ht, hcard⟩ :=
      (Dynamics.coverMincard_finite_iff T (T '' F) U n).mp hfin
    obtain ⟨c, hc, hct⟩ := dynCover_prefix_product T F U n s t hs ht
    calc
      Dynamics.coverMincard T F (U ○ U) n ≤ (c.card : ℕ∞) :=
        (hc.of_le (Nat.le_succ n)).coverMincard_le_card
      _ ≤ (s.card * t.card : ℕ) := by exact_mod_cast hct
      _ = (s.card : ℕ∞) * Dynamics.coverMincard T (T '' F) U n := by
        rw [Nat.cast_mul, hcard]

theorem coverEntropyEntourage_le_image_of_initial_cover
    {X : Type*} [Nonempty X] (T : X → X) (F : Set X)
    (U : SetRel X X) [U.IsSymm] (s : Finset X)
    (hs : Dynamics.IsDynCoverOf T F U 1 s) :
    Dynamics.coverEntropyEntourage T F (U ○ U) ≤
      Dynamics.coverEntropyEntourage T (T '' F) U := by
  apply ExpGrowth.expGrowthSup_le_of_eventually_le (b := (s.card : ℝ≥0∞)) (by simp)
  apply Filter.Eventually.of_forall
  intro n
  simpa only [ENat.toENNReal_mul, ENat.toENNReal_coe] using
    ENat.toENNReal_mono (coverMincard_le_initial_card_mul_image T F U s hs n)

theorem coverEntropy_le_image_of_isCompact
    {X : Type*} [UniformSpace X] [Nonempty X]
    (T : X → X) (F : Set X) (hF : IsCompact F) :
    Dynamics.coverEntropy T F ≤ Dynamics.coverEntropy T (T '' F) := by
  apply iSup₂_le
  intro U hU
  obtain ⟨V, hV, hVsymm, hVU⟩ := comp_symm_mem_uniformity_sets hU
  obtain ⟨s, hs⟩ := Dynamics.exists_isDynCoverOf_of_isCompact_uniformContinuous
    hF uniformContinuous_id hV 1
  have hsT : Dynamics.IsDynCoverOf T F V 1 s := by
    simpa only [Dynamics.IsDynCoverOf, Dynamics.dynEntourage_one] using hs
  exact ((Dynamics.coverEntropyEntourage_antitone T F hVU).trans
    (coverEntropyEntourage_le_image_of_initial_cover T F V s hsT)).trans
    (Dynamics.coverEntropyEntourage_le_coverEntropy T (T '' F) hV)

theorem coverEntropy_univ_eq_zero_of_first_image_factor
    {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    [CompactSpace X] [Nonempty X]
    (T : X → X) (S : Y → Y) (φ : Y → X)
    (hsemi : Function.Semiconj φ S T) (hφ : UniformContinuous φ)
    (himage : Set.range T ⊆ Set.range φ)
    (hS : Dynamics.coverEntropy S (Set.univ : Set Y) = 0) :
    Dynamics.coverEntropy T (Set.univ : Set X) = 0 := by
  apply le_antisymm
  · have h := coverEntropy_le_image_of_isCompact T univ isCompact_univ
    rw [image_univ] at h
    have hfac := Dynamics.coverEntropy_image_le_of_uniformContinuous hsemi hφ univ
    rw [image_univ, hS] at hfac
    exact h.trans ((Dynamics.coverEntropy_monotone T himage).trans hfac)
  · exact Dynamics.coverEntropy_nonneg T Set.univ_nonempty

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapBoundedOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology OnePoint

namespace Problem340.Construction

theorem rawClockLift_liftedOrbit (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) :
    Clock.LiftedOrbit (rawClockLift D x t₀)
      (fun n => D.gate (((rawMap D)^[n] x).2.1)) where
  cutoff_nonneg _ := (hgate _).1
  cutoff_le_one _ := (hgate _).2
  update := rawClockLift_succ D x t₀ h₀

theorem periodicReadout_coe_periodic (i : Fin 3) :
    Function.Periodic (fun t : ℝ => periodicReadout i (t : AddCircle (100 : ℝ))) 100 := by
  intro t
  change periodicReadout i ((t + 100 : ℝ) : AddCircle (100 : ℝ)) = _
  rw [AddCircle.coe_add_period]

theorem periodicReadout_coe_eq_zero_near_fifty (i : Fin 3) {t : ℝ}
    (ht : t ∈ Set.Ioo (48 : ℝ) 52) :
    periodicReadout i (t : AddCircle (100 : ℝ)) = 0 := by
  rw [periodicReadout, AddCircle.liftIco_coe_apply (show t ∈ Set.Ico (0 : ℝ) (0 + 100) by
    constructor <;> linarith [ht.1, ht.2])]
  by_contra hn
  have hs : t ∈ Function.support (readoutCoeff i) := hn
  rw [readoutCoeff_support] at hs
  have hread := readoutInterval_subset i hs
  linarith [ht.2, hread.1]

theorem readout_eq_sum_smul (D : SphereData) (t : AddCircle (100 : ℝ))
    (v : Fin 3 → Sphere) :
    readout D t v = ∑ i : Fin 3, periodicReadout i t • (20 * D.saturation (v i)) := by
  unfold readout
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.real_smul]
  ring

theorem raw_clock_tendsto_of_bounded (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hbounded : BddAbove (Set.range (rawClockLift D x t₀))) :
    Tendsto (fun n => ((rawMap D)^[n] x).1) atTop
      (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) := by
  have hclock := rawClockLift_liftedOrbit D hgate x t₀ h₀
  exact (hclock.bounded_circle_limit hbounded).congr (coe_rawClockLift D x t₀ h₀)

theorem raw_main_tendsto_zero_of_bounded (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (hgate_infty : D.gate ∞ = 1)
    (hgate_large : ∀ w : ℂ, 3 / 4 ≤ ‖w‖ → D.gate (w : Sphere) = 1)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hbounded : BddAbove (Set.range (rawClockLift D x t₀))) :
    Tendsto (fun n => ((rawMap D)^[n] x).2.1) atTop (𝓝 ((0 : ℂ) : Sphere)) := by
  have hclock := rawClockLift_liftedOrbit D hgate x t₀ h₀
  apply hclock.onePoint_main_tendsto_zero_of_readouts hbounded
    (β := fun i t => periodicReadout i (t : AddCircle (100 : ℝ)))
    (u := fun n i => 20 * D.saturation (((rawMap D)^[n] x).2.2 i))
  · intro n hn
    rw [Function.iterate_succ_apply']
    change perturbedSquare _ (((rawMap D)^[n] x).2.1) = ∞
    rw [hn, perturbedSquare_infty]
  · intro n hn
    rw [hn, hgate_infty]
  · intro n w hn hw
    rw [hn]
    exact hgate_large w hw
  · exact periodicReadout_coe_periodic
  · intro i t ht
    exact periodicReadout_coe_eq_zero_near_fifty i ht
  · intro n w hn
    rw [Function.iterate_succ_apply']
    change perturbedSquare _ (((rawMap D)^[n] x).2.1) = _
    rw [hn, perturbedSquare_coe]
    apply OnePoint.coe_injective
    congr 1
    rw [readout_eq_sum_smul]
    simp only [coe_rawClockLift D x t₀ h₀ n]

theorem concrete_bounded_clock_limits (L : ℝ) (hL : 2 < L)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hbounded : BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀))) :
    Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
      (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
    Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
      (𝓝 ((0 : ℂ) : Sphere)) := by
  refine ⟨raw_clock_tendsto_of_bounded _ (concrete_gate_mem_Icc L hL) x t₀ h₀ hbounded, ?_⟩
  apply raw_main_tendsto_zero_of_bounded _ (concrete_gate_mem_Icc L hL)
    (concrete_gate_infty L hL) _ x t₀ h₀ hbounded
  intro w hw
  exact SphereCutoffs.affineClockGate_eq_one hw

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PassagePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.PassagePhase

lemma norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, Complex.norm_real, norm_ne_zero_iff.mpr hz]

lemma norm_mul_phase (z : ℂ) : (‖z‖ : ℂ) * phase z = z := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    dsimp [phase]
    field_simp

lemma gain_nonneg {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (w : ℕ → ℝ) (β : ℕ → κ → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (n : ℕ) : 0 ≤ gain I J w β n := by
  apply mul_nonneg
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun l _ => sq_nonneg (β n l))
  · exact Finset.sum_nonneg hw

end Problem340.PassagePhase

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PassagePhaseInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.PassagePhase

theorem prediction_phase_power_from (θ : ℂ) (s i n : ℕ) (hsi : s ≤ i) (hin : i ≤ n) :
    (θ ^ (2 ^ (i - s))) ^ (2 ^ (n - i + 1)) = θ ^ (2 ^ (n - s + 1)) := by
  rw [← pow_mul, ← pow_add]
  congr 2
  omega

theorem delayed_readout_sum_from
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : κ → ℝ) (v : κ → ℂ)
    (θ : ℂ) (s n : ℕ)
    (hI : ∀ i ∈ I, s ≤ i ∧ i ≤ n)
    (hp : ∀ i ∈ I, phase (z i) = θ ^ (2 ^ (i - s)))
    (hv : ∀ l ∈ J, β l ≠ 0 → v l = ((β l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1))) :
    (20 : ℂ) * (∑ l ∈ J, (β l : ℂ) * v l) =
      ((2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, w i) : ℝ) : ℂ) *
        θ ^ (2 ^ (n - s + 1)) := by
  let v' : κ → ℂ := fun l => ((β l / 10 : ℝ) : ℂ) *
    ∑ i ∈ I, (w i : ℂ) * θ ^ (2 ^ (n - s + 1))
  have hs : (∑ l ∈ J, (β l : ℂ) * v l) =
      ∑ l ∈ J, (β l : ℂ) * v' l := by
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hb : β l = 0
    · simp [hb]
    · rw [hv l hl hb]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      rw [hp i hi, prediction_phase_power_from θ s i n (hI i hi).1 (hI i hi).2]
  rw [hs]
  exact aligned_readout_sum I J w β v' (θ ^ (2 ^ (n - s + 1))) (fun _ _ => rfl)

theorem readout_sum_of_preparation_phases_from
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : κ → ℝ) (v : κ → ℂ)
    (θ : ℂ) (s K n : ℕ) (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : n < K → ∀ l ∈ J, β l = 0)
    (hp : ∀ i ∈ I, i ≤ n → phase (z i) = θ ^ (2 ^ (i - s)))
    (hv : ∀ l ∈ J, β l ≠ 0 → v l = ((β l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1))) :
    (20 : ℂ) * (∑ l ∈ J, (β l : ℂ) * v l) =
      ((2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, w i) : ℝ) : ℂ) *
        θ ^ (2 ^ (n - s + 1)) := by
  by_cases hnK : n < K
  · have hb : ∀ l ∈ J, β l = 0 := hearly hnK
    have hs : (∑ l ∈ J, (β l : ℂ) * v l) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      simp [hb l hl]
    have hb2 : (∑ l ∈ J, β l ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      simp [hb l hl]
    simp [hs, hb2]
  · have hin : ∀ i ∈ I, s ≤ i ∧ i ≤ n := by
      intro i hi
      have := hI i hi
      omega
    exact delayed_readout_sum_from I J z w β v θ s n hin
      (fun i hi => hp i hi (hin i hi).2) hv

theorem passage_phase_interval
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l)) :
    ∀ n, s ≤ n → n ≤ N →
      z n ≠ 0 ∧ phase (z n) = phase (z s) ^ (2 ^ (n - s)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hsn hnN
      have haligned : ∀ m, m < n - s → z (s + (m + 1)) = z (s + m) ^ 2 +
          (gain I J w β (s + m) : ℂ) * phase (z s) ^ (2 ^ (m + 1)) := by
        intro m hm
        have hsm : s ≤ s + m := by omega
        have hmn : s + m < n := by omega
        have hs := readout_sum_of_preparation_phases_from I J z w (β (s + m))
          (v (s + m)) (phase (z s)) s K (s + m) hI (hearly (s + m) hsm)
          (fun i hi him => (ih i (by omega) (hI i hi).1 (by omega)).2)
          (hv (s + m) hsm (by omega))
        rw [show s + (m + 1) = s + m + 1 by omega, hrec (s + m) hsm (by omega)]
        congr 1
        simpa only [gain, Nat.add_sub_cancel_left] using hs
      have hresult := aligned_orbit_phase_until (fun m => z (s + m))
        (fun m => gain I J w β (s + m)) (phase (z s)) (n - s)
        (norm_phase hzs) (fun m => gain_nonneg I J w β hw (s + m))
        (by simpa using (norm_mul_phase (z s)).symm) (by simpa using hzs)
        haligned (n - s) le_rfl
      have hr : z n ≠ 0 ∧ z n = (‖z n‖ : ℂ) * phase (z s) ^ (2 ^ (n - s)) := by
        simpa only [Nat.add_sub_of_le hsn] using hresult
      refine ⟨hr.1, ?_⟩
      have hn : (‖z n‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr.1)
      apply mul_left_cancel₀ hn
      exact (norm_mul_phase (z n)).trans hr.2

theorem passage_radial_step_interval
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l)) :
    ∀ n, s ≤ n → n < N → ‖z (n + 1)‖ = ‖z n‖ ^ 2 + gain I J w β n := by
  intro n hsn hn
  have hp := passage_phase_interval I J z w β v s K N hzs hI hw hearly hv hrec
  have hs := readout_sum_of_preparation_phases_from I J z w (β n) (v n)
    (phase (z s)) s K n hI (hearly n hsn)
    (fun i hi hin => (hp i (hI i hi).1 (by omega)).2) (hv n hsn hn)
  have hu : ‖phase (z s) ^ (2 ^ (n - s))‖ = 1 := by
    rw [norm_pow, norm_phase hzs, one_pow]
  have hz : z n = (‖z n‖ : ℂ) * phase (z s) ^ (2 ^ (n - s)) := by
    rw [← (hp n hsn hn.le).2]
    exact (norm_mul_phase (z n)).symm
  have hpow : phase (z s) ^ (2 ^ (n - s + 1)) = (phase (z s) ^ (2 ^ (n - s))) ^ 2 := by
    rw [pow_succ, pow_mul]
  rw [hrec n hsn hn, hs, hpow]
  exact aligned_square_norm _ _ _ _ hu hz (norm_nonneg _) (gain_nonneg I J w β hw n)

theorem passage_square_le_interval
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l)) :
    ∀ n, s ≤ n → n < N → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖ := by
  intro n hsn hn
  rw [passage_radial_step_interval I J z w β v s K N hzs hI hw hearly hv hrec n hsn hn]
  exact le_add_of_nonneg_right (gain_nonneg I J w β hw n)

theorem passage_contains_large_radius_interval
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l))
    (hprep : ∃ i ∈ I, w i = 1)
    (hread : ∃ j, s ≤ j ∧ j < N ∧ ∃ l ∈ J, β j l = 1) :
    ∃ n, s ≤ n ∧ n ≤ N ∧ 1 < ‖z n‖ := by
  obtain ⟨j, hsj, hj, hl⟩ := hread
  refine ⟨j + 1, by omega, by omega, ?_⟩
  rw [passage_radial_step_interval I J z w β v s K N hzs hI hw hearly hv hrec j hsj hj]
  have hg : 2 ≤ gain I J w β j := readout_gain_ge_two I J w (β j) hw hprep hl
  nlinarith [sq_nonneg ‖z j‖]

theorem passage_escape_of_preparation_plateau
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l))
    (a : ℕ → ℝ) (χ : ℂ → ℝ) (hKN : K ≤ N)
    (hweight : ∀ i ∈ I, w i = a i * χ (z i))
    (hhalf : ∀ i ∈ I, (1 / 2 : ℝ) < ‖z i‖)
    (hcutoff : ∀ u : ℂ, (1 / 2 : ℝ) ≤ ‖u‖ → ‖u‖ ≤ 1 → χ u = 1)
    (hprep : ∃ i ∈ I, a i = 1)
    (hread : ∃ j, s ≤ j ∧ j < N ∧ ∃ l ∈ J, β j l = 1) :
    ∃ n, s ≤ n ∧ n ≤ N ∧ 1 < ‖z n‖ := by
  obtain ⟨i, hi, hai⟩ := hprep
  by_cases hlarge : 1 < ‖z i‖
  · exact ⟨i, (hI i hi).1, le_trans (hI i hi).2.le hKN, hlarge⟩
  · have hwi : w i = 1 := by
      rw [hweight i hi, hai, hcutoff (z i) (hhalf i hi).le (le_of_not_gt hlarge)]
      simp
    exact passage_contains_large_radius_interval I J z w β v s K N hzs hI hw
      hearly hv hrec ⟨i, hi, hwi⟩ hread

end Problem340.PassagePhase

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapPassagePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem finite_main_step_of_rawMap (D : SphereData)
    {x y : RawManifold} {z w : ℂ}
    (hstep : y = rawMap D x)
    (hz : (z : Sphere) = x.2.1) (hw : (w : Sphere) = y.2.1) :
    w = z ^ 2 + readout D x.1 x.2.2 := by
  apply OnePoint.coe_injective
  calc
    (w : Sphere) = y.2.1 := hw
    _ = (rawMap D x).2.1 := congrArg (fun p : RawManifold => p.2.1) hstep
    _ = perturbedSquare (readout D x.1 x.2.2) x.2.1 := rfl
    _ = ((z ^ 2 + readout D x.1 x.2.2 : ℂ) : Sphere) := by rw [← hz]; rfl

lemma passageWeight_nonneg (D : SphereData) (hχ : ∀ z, 0 ≤ D.cutoff z)
    (t : ℕ → ℝ) (z : ℕ → ℂ) (i : ℕ) : 0 ≤ passageWeight D t z i :=
  mul_nonneg (preparationCoeff_nonneg _) (hχ _)

theorem rawMap_passage_square_le
    (D : SphereData) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hχ : ∀ z, 0 ≤ D.cutoff z) (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister D x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = rawMap D (x n)) :
    ∀ n, s ≤ n → n < N → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖ := by
  apply PassagePhase.passage_square_le_interval I Finset.univ z (passageWeight D t z)
    (orbitReadoutCoeff x) (orbitSaturatedRegister D x) s K N hzs hI
  · intro i _
    exact passageWeight_nonneg D hχ t z i
  · intro n hsn hn l _
    exact hearly n hsn hn l
  · intro n hsn hn l _ hb
    exact hregister n hsn hn l hb
  · intro n hsn hn
    exact finite_main_step_of_rawMap D (hstep n hsn hn)
      (hz n hsn hn.le) (hz (n + 1) (by omega) (by omega))

theorem rawMap_passage_escape
    (D : SphereData) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hχ : ∀ z, 0 ≤ D.cutoff z) (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister D x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = rawMap D (x n))
    (hKN : K ≤ N)
    (hhalf : ∀ i ∈ I, (1 / 2 : ℝ) < ‖z i‖)
    (hcutoff : ∀ u : ℂ, (1 / 2 : ℝ) ≤ ‖u‖ → ‖u‖ ≤ 1 → D.cutoff (u : Sphere) = 1)
    (hprep : ∃ i ∈ I, preparationCoeff (t i) = 1)
    (hread : ∃ j, s ≤ j ∧ j < N ∧ ∃ l : Fin 3, orbitReadoutCoeff x j l = 1) :
    ∃ n, s ≤ n ∧ n ≤ N ∧ 1 < ‖z n‖ := by
  refine PassagePhase.passage_escape_of_preparation_plateau I Finset.univ z
    (passageWeight D t z) (orbitReadoutCoeff x) (orbitSaturatedRegister D x)
    s K N hzs hI ?_ ?_ ?_ ?_ (fun i => preparationCoeff (t i))
    (fun u => D.cutoff (u : Sphere)) hKN ?_ hhalf hcutoff hprep ?_
  · intro i _
    exact passageWeight_nonneg D hχ t z i
  · intro n hsn hn l _
    exact hearly n hsn hn l
  · intro n hsn hn l _ hb
    exact hregister n hsn hn l hb
  · intro n hsn hn
    exact finite_main_step_of_rawMap D (hstep n hsn hn)
      (hz n hsn hn.le) (hz (n + 1) (by omega) (by omega))
  · intro i _
    rfl
  · obtain ⟨j, hsj, hj, l, hl⟩ := hread
    exact ⟨j, hsj, hj, l, Finset.mem_univ _, hl⟩

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapConcretePassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem concreteMap_passage_square_le
    (L : ℝ) (hL : 2 < L) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister (concreteData L hL) x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight (concreteData L hL) t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = concreteMap L hL (x n)) :
    ∀ n, s ≤ n → n < N → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖ := by
  exact rawMap_passage_square_le (concreteData L hL) x t z I s K N
    (fun u => (concrete_cutoff_mem_Icc L hL u).1) hzs hz hI hearly hregister hstep

theorem concreteMap_passage_escape
    (L : ℝ) (hL : 2 < L) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister (concreteData L hL) x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight (concreteData L hL) t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = concreteMap L hL (x n))
    (hKN : K ≤ N)
    (hhalf : ∀ i ∈ I, (1 / 2 : ℝ) < ‖z i‖)
    (hprep : ∃ i ∈ I, preparationCoeff (t i) = 1)
    (hread : ∃ j, s ≤ j ∧ j < N ∧ ∃ l : Fin 3, orbitReadoutCoeff x j l = 1) :
    ∃ n, s ≤ n ∧ n ≤ N ∧ 1 < ‖z n‖ := by
  apply rawMap_passage_escape (concreteData L hL) x t z I s K N
    (fun u => (concrete_cutoff_mem_Icc L hL u).1) hzs hz hI hearly hregister hstep
    hKN hhalf _ hprep hread
  intro u hlo hhi
  exact SphereCutoffs.affinePreparationCutoff_eq_one hlo hhi

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapFiniteOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped OnePoint
namespace Problem340.Construction

theorem rawMap_main_ne_infty_iff (D : SphereData) (x : RawManifold) :
    (rawMap D x).2.1 ≠ ∞ ↔ x.2.1 ≠ ∞ := by
  rcases x with ⟨t, z, v⟩
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp [rawMap]

theorem raw_iterate_main_ne_infty_iff (D : SphereData) (x : RawManifold) (n : ℕ) :
    ((rawMap D)^[n] x).2.1 ≠ ∞ ↔ x.2.1 ≠ ∞ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', rawMap_main_ne_infty_iff, ih]

theorem exists_finiteMainOrbit (D : SphereData) (x : RawManifold) (hx : x.2.1 ≠ ∞) :
    ∃ z : ℕ → ℂ,
      (∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1) ∧
      ∀ n, z (n + 1) = z n ^ 2 +
        readout D ((rawMap D)^[n] x).1 ((rawMap D)^[n] x).2.2 := by
  classical
  have hex : ∀ n, ∃ z : ℂ, (z : Sphere) = ((rawMap D)^[n] x).2.1 := by
    intro n
    exact OnePoint.ne_infty_iff_exists.mp ((raw_iterate_main_ne_infty_iff D x n).mpr hx)
  choose z hz using hex
  refine ⟨z, hz, ?_⟩
  intro n
  apply OnePoint.coe_injective
  rw [hz (n + 1), Function.iterate_succ_apply']
  change perturbedSquare (readout D ((rawMap D)^[n] x).1
    ((rawMap D)^[n] x).2.2) (((rawMap D)^[n] x).2.1) = _
  rw [← hz n]
  rfl

theorem finiteMainOrbit_recurrence (D : SphereData) (x : RawManifold) (z : ℕ → ℂ)
    (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1) (n : ℕ) :
    z (n + 1) = z n ^ 2 +
      readout D ((rawMap D)^[n] x).1 ((rawMap D)^[n] x).2.2 := by
  apply OnePoint.coe_injective
  rw [hz (n + 1), Function.iterate_succ_apply']
  change perturbedSquare (readout D ((rawMap D)^[n] x).1
    ((rawMap D)^[n] x).2.2) (((rawMap D)^[n] x).2.1) = _
  rw [← hz n]
  rfl

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RawInvariantInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340

theorem isCompact_rawInfinitySet (q : ℕ) : IsCompact (rawInfinitySet q) := by
  let : Fact (0 < (100 : ℝ)) := ⟨by norm_num⟩
  exact isCompact_range (continuous_rawInfinityPoint q)

theorem mem_rawInfinitySet_iff {q : ℕ} (x : RawState q) :
    x ∈ rawInfinitySet q ↔ x.2.1 = ∞ ∧ ∀ i, x.2.2 i = ((0 : ℂ) : OnePoint ℂ) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨hz, hv⟩
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hz.symm
      · funext i
        exact (hv i).symm

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem concreteMap_infinity_semiconj (L : ℝ) (hL : 2 < L) :
    Function.Semiconj (rawInfinityPoint 3) ClockAtInfinity.step (concreteMap L hL) := by
  intro t
  exact (concreteMap_infty_zero L hL t).symm

theorem concreteMap_mapsTo_infinitySet (L : ℝ) (hL : 2 < L) :
    Set.MapsTo (concreteMap L hL) (rawInfinitySet 3) (rawInfinitySet 3) := by
  rintro x ⟨t, rfl⟩
  exact ⟨ClockAtInfinity.step t, concreteMap_infinity_semiconj L hL t⟩

theorem coverEntropy_concreteInfinity_image (L : ℝ) (hL : 2 < L)
    {X : Type*} [UniformSpace X] {T : X → X}
    {φ : RawManifold → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (concreteMap L hL) T) :
    Dynamics.coverEntropy T (φ '' rawInfinitySet 3) = 0 := by
  rw [rawInfinitySet, ← Set.range_comp]
  apply ClockAtInfinity.coverEntropy_clockImage
    (hφ.comp (continuous_rawInfinityPoint 3))
  intro t
  exact (congrArg φ (concreteMap_infinity_semiconj L hL t)).trans
    (hsem (rawInfinityPoint 3 t))

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RawInvariantSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.RawInvariantSets

theorem isCompact_zeroSet (q : ℕ) (t₀ : AddCircle (100 : ℝ)) :
    IsCompact (zeroSet q t₀) :=
  isCompact_range (continuous_zeroSlice t₀)

theorem zeroSet_nonempty (q : ℕ) (t₀ : AddCircle (100 : ℝ)) :
    (zeroSet q t₀).Nonempty := Set.range_nonempty _

theorem mem_zeroSet_iff {q : ℕ} (t₀ : AddCircle (100 : ℝ)) (x : RawState q) :
    x ∈ zeroSet q t₀ ↔ x.1 = t₀ ∧ x.2.1 = ((0 : ℂ) : OnePoint ℂ) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨ht, hz⟩
    exact ⟨x.2.2, Prod.ext ht.symm (Prod.ext hz.symm rfl)⟩

end Problem340.RawInvariantSets

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.OrderedIntervalLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem abs_sub_lt_of_floor_div_eq {r s ε : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hε : 0 < ε)
    (heq : Nat.floor (r / ε) = Nat.floor (s / ε)) : |r - s| < ε := by
  have hrlo : (Nat.floor (r / ε) : ℝ) * ε ≤ r :=
    (le_div_iff₀ hε).mp (Nat.floor_le (div_nonneg hr hε.le))
  have hrhi : r < ((Nat.floor (r / ε) : ℝ) + 1) * ε :=
    (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (r / ε))
  have hslo : (Nat.floor (s / ε) : ℝ) * ε ≤ s :=
    (le_div_iff₀ hε).mp (Nat.floor_le (div_nonneg hs hε.le))
  have hshi : s < ((Nat.floor (s / ε) : ℝ) + 1) * ε :=
    (div_lt_iff₀ hε).mp (Nat.lt_floor_add_one (s / ε))
  rw [heq] at hrlo hrhi
  rw [abs_sub_lt_iff]
  constructor <;> nlinarith

theorem monotone_orderedIntervalLabel (A ε : ℝ) (hε : 0 < ε) :
    Monotone (orderedIntervalLabel A ε hε) := by
  intro r s hrs
  exact Nat.floor_le_floor (div_le_div_of_nonneg_right hrs hε.le)

theorem orderedIntervalLabel_small_fiber (A ε : ℝ) (hε : 0 < ε)
    {r s : Set.Icc (0 : ℝ) A}
    (heq : orderedIntervalLabel A ε hε r = orderedIntervalLabel A ε hε s) :
    |(r : ℝ) - (s : ℝ)| < ε := by
  exact abs_sub_lt_of_floor_div_eq r.property.1 s.property.1 hε (congrArg Fin.val heq)

theorem exists_monotone_interval_labels (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, ∃ b : Set.Icc (0 : ℝ) A → Fin (H + 1),
      Monotone b ∧ ∀ r s, b r = b s → |(r : ℝ) - (s : ℝ)| < ε := by
  exact ⟨Nat.floor (A / ε), orderedIntervalLabel A ε hε,
    monotone_orderedIntervalLabel A ε hε,
    fun _ _ heq => orderedIntervalLabel_small_fiber A ε hε heq⟩

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MonotoneItineraries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340
namespace MonotoneItineraries

open Finset

lemma labelSum_le {N H : ℕ} (v : Fin N → Fin H) :
    labelSum v ≤ N * (H - 1) := by
  calc
    labelSum v ≤ ∑ _i : Fin N, (H - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.le_sub_one_of_lt (v i).is_lt
    _ = N * (H - 1) := by simp

lemma eq_of_le_of_labelSum_eq {N H : ℕ} {v w : Fin N → Fin H}
    (hvw : v ≤ w) (hsum : labelSum v = labelSum w) : v = w := by
  funext i
  apply Fin.ext
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => show (v j).val ≤ (w j).val from hvw j)).mp hsum i (Finset.mem_univ i)

theorem card_range_le {α : Type*} [LinearOrder α] {N H : ℕ}
    (c : α → Fin N → Fin H) (hc : Monotone c) :
    Nat.card (Set.range c) ≤ 1 + N * (H - 1) := by
  classical
  let := Fintype.ofFinite (Set.range c)
  let rank : Set.range c → Fin (N * (H - 1) + 1) :=
    fun v => ⟨labelSum v.val, Nat.lt_succ_of_le (labelSum_le v.val)⟩
  have hrank : Function.Injective rank := by
    intro v w heq
    apply Subtype.ext
    have hsum : labelSum v.val = labelSum w.val := congrArg Fin.val heq
    obtain ⟨x, hx⟩ := v.property
    obtain ⟨y, hy⟩ := w.property
    rcases le_total x y with hxy | hyx
    · exact eq_of_le_of_labelSum_eq (hx ▸ hy ▸ hc hxy) hsum
    · exact (eq_of_le_of_labelSum_eq (hy ▸ hx ▸ hc hyx) hsum.symm).symm
  simpa [Nat.card_eq_fintype_card, Nat.add_comm] using
    Fintype.card_le_of_injective rank hrank

lemma itinerary_monotone {α : Type*} [Preorder α] {H : ℕ}
    {R : α → α} {b : α → Fin H} (hR : Monotone R) (hb : Monotone b) (N : ℕ) :
    Monotone (itinerary R b N) := by
  intro x y hxy i
  exact hb ((hR.iterate i.val) hxy)

theorem card_itinerary_range_le {α : Type*} [LinearOrder α] {H : ℕ}
    {R : α → α} {b : α → Fin H} (hR : Monotone R) (hb : Monotone b) (N : ℕ) :
    Nat.card (Set.range (itinerary R b N)) ≤ 1 + N * (H - 1) :=
  card_range_le _ (itinerary_monotone hR hb N)

end MonotoneItineraries
end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RegisterEntropyCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340
namespace RegisterEntropyCoding

open Dynamics Set
open scoped SetRel

theorem netMaxcard_le_card_code {X β : Type*} [Finite β]
    (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ)
    (code : X → β)
    (hcode : ∀ x ∈ F, ∀ y ∈ F, code x = code y →
      (x, y) ∈ dynEntourage T U n) :
    netMaxcard T F U n ≤ (Nat.card β : ℕ∞) := by
  classical
  unfold netMaxcard
  refine iSup₂_le fun s hs => ?_
  have hinj : Function.Injective (fun x : s => code x.val) := by
    intro x y hxy
    apply Subtype.ext
    exact Set.PairwiseDisjoint.elim_set hs.2 x.property y.property y.val
      (hcode x.val (hs.1 x.property) y.val (hs.1 y.property) hxy)
      (hcode y.val (hs.1 y.property) y.val (hs.1 y.property) rfl)
  have hcard := Nat.card_le_card_of_injective _ hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    (show (Nat.card s : ℕ∞) ≤ Nat.card β by exact_mod_cast hcard)

theorem netMaxcard_le_register_code {X α : Type*} [LinearOrder α]
    {q H K : ℕ} (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ)
    (R : α → α) (b : α → Fin H) (hR : Monotone R) (hb : Monotone b)
    (radius : X → Fin q → α) (angle : X → Fin q → Fin K)
    (hcode : ∀ x ∈ F, ∀ y ∈ F,
      (∀ j, angle x j = angle y j) →
      (∀ j, MonotoneItineraries.itinerary R b n (radius x j) =
        MonotoneItineraries.itinerary R b n (radius y j)) →
      (x, y) ∈ dynEntourage T U n) :
    netMaxcard T F U n ≤ ((K * (1 + n * (H - 1))) ^ q : ℕ) := by
  classical
  let I := Set.range (MonotoneItineraries.itinerary R b n)
  let code : X → Fin q → Fin K × I := fun x j =>
    (angle x j, ⟨MonotoneItineraries.itinerary R b n (radius x j),
      ⟨radius x j, rfl⟩⟩)
  have hbound := netMaxcard_le_card_code T F U n code (by
    intro x hx y hy hxy
    apply hcode x hx y hy
    · intro j
      exact congrArg (fun z => (z j).1) hxy
    · intro j
      exact congrArg (fun z => (z j).2.val) hxy)
  apply hbound.trans
  have hi : Nat.card I ≤ 1 + n * (H - 1) :=
    MonotoneItineraries.card_itinerary_range_le hR hb n
  have hnat : Nat.card (Fin q → Fin K × I) ≤ (K * (1 + n * (H - 1))) ^ q := by
    simp only [Nat.card_fun, Nat.card_prod, Nat.card_fin]
    gcongr
  exact_mod_cast hnat

theorem netMaxcard_le_of_radius_angle {X α : Type*} [LinearOrder α]
    {q H K : ℕ} (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ)
    (R : α → α) (b : α → Fin H) (hR : Monotone R) (hb : Monotone b)
    (radius : X → Fin q → α) (angle : X → Fin q → Fin K)
    (hF : Set.MapsTo T F F)
    (hrad : ∀ j, Function.Semiconj (fun x => radius x j) T R)
    (hang : ∀ x, angle (T x) = angle x)
    (hclose : ∀ x ∈ F, ∀ y ∈ F,
      (∀ j, angle x j = angle y j) →
      (∀ j, b (radius x j) = b (radius y j)) → (x, y) ∈ U) :
    netMaxcard T F U n ≤ ((K * (1 + n * (H - 1))) ^ q : ℕ) := by
  apply netMaxcard_le_register_code T F U n R b hR hb radius angle
  intro x hx y hy hangle hitinerary
  rw [mem_dynEntourage]
  intro k hk
  apply hclose _ (hF.iterate k hx) _ (hF.iterate k hy)
  · have ha : angle ∘ T = angle := funext hang
    have hak := Function.iterate_invariant ha k
    have hax : angle (T^[k] x) = angle x := congrFun hak x
    have hay : angle (T^[k] y) = angle y := congrFun hak y
    intro j
    rw [hax, hay]
    exact hangle j
  · intro j
    have hrx : radius (T^[k] x) j = R^[k] (radius x j) := (hrad j).iterate_right k x
    have hry : radius (T^[k] y) j = R^[k] (radius y j) := (hrad j).iterate_right k y
    rw [hrx, hry]
    exact congrFun (hitinerary j) ⟨k, hk⟩

lemma register_bound_le_polynomial (K H q n : ℕ) :
    (K * (1 + n * (H - 1))) ^ q ≤
      (K * (H + 1)) ^ q * (n + 1) ^ q := by
  have hlinear : 1 + n * (H - 1) ≤ (H + 1) * (n + 1) := by
    nlinarith [Nat.sub_le H 1]
  calc
    (K * (1 + n * (H - 1))) ^ q ≤ (K * ((H + 1) * (n + 1))) ^ q := by
      gcongr
    _ = (K * (H + 1)) ^ q * (n + 1) ^ q := by rw [← mul_assoc, mul_pow]

end RegisterEntropyCoding
end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PolarProductEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340
namespace PolarProductEntropy

open Set Dynamics
open scoped Uniformity

theorem coverEntropy_radialProduct {S : Type*} [PseudoMetricSpace S]
    [CompactSpace S] [Nonempty S] (A : ℝ) (hA : 0 ≤ A)
    (R : Set.Icc (0 : ℝ) A → Set.Icc (0 : ℝ) A) (hR : Monotone R) (q : ℕ) :
    coverEntropy (radialProduct (S := S) R q) Set.univ = 0 := by
  let : Nonempty (Set.Icc (0 : ℝ) A) := ⟨⟨0, le_rfl, hA⟩⟩
  apply coverEntropy_eq_zero_of_polynomial_net_bound _ Set.univ_nonempty
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨H, b, hb, hbdiam⟩ := exists_monotone_interval_labels A hε
  obtain ⟨K, c, hcdiam⟩ := exists_small_fiber_labels (X := S) hε
  refine ⟨(K * (H + 1 + 1)) ^ q, q, fun n => ?_⟩
  have hbound := RegisterEntropyCoding.netMaxcard_le_of_radius_angle
    (radialProduct (S := S) R q) Set.univ U n R b hR hb
    (fun x j => (x j).1) (fun x j => c (x j).2)
    (fun _ _ => Set.mem_univ _) (fun _ _ => rfl) (fun _ => rfl) (by
      intro x _ y _ ha hr
      apply hεU
      rw [dist_pi_lt_iff hε]
      intro j
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · simpa only [Subtype.dist_eq, Real.dist_eq] using hbdiam _ _ (hr j)
      · exact hcdiam _ _ (ha j))
  apply hbound.trans
  exact_mod_cast RegisterEntropyCoding.register_bound_le_polynomial K (H + 1) q n

theorem coverEntropy_polar_first_image {S X : Type*} [PseudoMetricSpace S]
    [CompactSpace S] [Nonempty S] [UniformSpace X] [CompactSpace X] [Nonempty X]
    (A : ℝ) (hA : 0 ≤ A)
    (R : Set.Icc (0 : ℝ) A → Set.Icc (0 : ℝ) A) (hR : Monotone R) (q : ℕ)
    (p : (Fin q → Set.Icc (0 : ℝ) A × S) → X) (hp : Continuous p)
    (T : X → X) (hsem : Function.Semiconj p (radialProduct R q) T)
    (himage : Set.range T ⊆ Set.range p) :
    coverEntropy T Set.univ = 0 :=
  coverEntropy_univ_eq_zero_of_first_image_factor T (radialProduct R q) p hsem
    (CompactSpace.uniformContinuous_of_continuous hp) himage
    (coverEntropy_radialProduct A hA R hR q)

end PolarProductEntropy
end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RadialRegisterEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340
namespace RadialRegisterEntropy

open Set Dynamics

lemma exists_polar_representation (A : ℝ) (z : ℂ) (hz : ‖z‖ ≤ A) :
    ∃ r : Set.Icc (0 : ℝ) A, ∃ u : UnitComplex, (r : ℝ) • (u : ℂ) = z := by
  refine ⟨⟨‖z‖, norm_nonneg z, hz⟩,
    ⟨Complex.exp (z.arg * Complex.I), ?_⟩, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using
      Complex.norm_exp_ofReal_mul_I z.arg
  · exact (Complex.real_smul).trans (Complex.norm_mul_exp_arg_mul_I z)

theorem coverEntropy_coordinatewise_eq_zero {X : Type*} [UniformSpace X]
    [CompactSpace X] [Nonempty X]
    (A : ℝ) (hA : 0 ≤ A)
    (embed : ℂ → X) (hembed : Continuous embed) (T : X → X)
    (R : Set.Icc (0 : ℝ) A → Set.Icc (0 : ℝ) A) (hR : Monotone R)
    (hradial : ∀ r : Set.Icc (0 : ℝ) A, ∀ u : UnitComplex,
      T (embed ((r : ℝ) • (u : ℂ))) = embed ((R r : ℝ) • (u : ℂ)))
    (himage : ∀ x, ∃ z : ℂ, ‖z‖ ≤ A ∧ T x = embed z) (q : ℕ) :
    coverEntropy (coordinatewise T q) Set.univ = 0 := by
  let p : (Fin q → Set.Icc (0 : ℝ) A × UnitComplex) → (Fin q → X) :=
    fun x j => embed (((x j).1 : ℝ) • ((x j).2 : ℂ))
  have hp : Continuous p := by
    dsimp [p]
    fun_prop
  apply PolarProductEntropy.coverEntropy_polar_first_image A hA R hR q p hp
    (coordinatewise T q)
  · intro x
    funext j
    exact (hradial (x j).1 (x j).2).symm
  · rintro _ ⟨x, rfl⟩
    have hx : ∀ j : Fin q, ∃ v : Set.Icc (0 : ℝ) A × UnitComplex,
        embed ((v.1 : ℝ) • (v.2 : ℂ)) = T (x j) := by
      intro j
      obtain ⟨z, hz, hT⟩ := himage (x j)
      obtain ⟨r, u, hru⟩ := exists_polar_representation A z hz
      exact ⟨(r, u), by rw [hru, hT]⟩
    choose v hv using hx
    exact ⟨v, funext hv⟩

end RadialRegisterEntropy
end Problem340

end OAI
end

section
-- module Solutions.OAIQW_Problem340.SaturationEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340
namespace SaturationEntropy

open Set Dynamics

lemma saturation_radial (A : ℝ) (hA : 1 ≤ A) {r : ℝ}
    (hr : 0 ≤ r) {u : ℂ} (hu : ‖u‖ = 1) :
    saturation A hA (r • u) = saturationProfile A hA r • u := by
  by_cases hr0 : r = 0
  · subst r
    simp only [zero_smul, saturation_zero]
    rw [saturationProfile_eq_self A hA (by norm_num), zero_smul]
  · have hnorm : ‖r • u‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hu, mul_one]
    rw [saturation, hnorm, smul_smul, div_mul_cancel₀ _ hr0]

lemma radiusMap_monotone (L : ℝ) (hL : 1 ≤ L) :
    Monotone (radiusMap L hL) := by
  intro r s hrs
  exact mul_le_mul_of_nonneg_left
    (saturationProfile_monotoneOn (3 * L) (by linarith) r.property s.property hrs)
    (by linarith)

theorem coverEntropy_scaled_saturation {X : Type*} [UniformSpace X]
    [CompactSpace X] [Nonempty X]
    (L : ℝ) (hL : 1 ≤ L) (embed : ℂ → X) (hembed : Continuous embed)
    (S : X → ℂ)
    (hSaffine : ∀ z, S (embed z) = saturation (3 * L) (by linarith) z)
    (hSbound : ∀ x, ‖S x‖ ≤ 2) (q : ℕ) :
    coverEntropy (RadialRegisterEntropy.coordinatewise
      (fun x => embed (L • S x)) q) Set.univ = 0 := by
  apply RadialRegisterEntropy.coverEntropy_coordinatewise_eq_zero
    (3 * L) (by linarith) embed hembed (fun x => embed (L • S x))
    (radiusMap L hL) (radiusMap_monotone L hL)
  · intro r u
    rw [hSaffine, saturation_radial _ _ r.property.1]
    · congr 1
      exact smul_smul L (saturationProfile (3 * L) _ r) (u : ℂ)
    · simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  · intro x
    refine ⟨L • S x, ?_, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ L)]
    have hnorm := hSbound x
    nlinarith

section OnePoint

attribute [local instance] OAI.Problem340.SaturationEntropy.instUniformSpaceOnePointComplex_solutions
theorem coverEntropy_onePoint_saturation (L : ℝ) (hL : 1 ≤ L) (q : ℕ) :
    coverEntropy (RadialRegisterEntropy.coordinatewise
      (fun x : OnePoint ℂ => ((L • sphereSaturation (3 * L) (by linarith) x : ℂ) :
        OnePoint ℂ)) q) Set.univ = 0 := by
  apply coverEntropy_scaled_saturation L hL ((↑) : ℂ → OnePoint ℂ)
    OnePoint.continuous_coe (sphereSaturation (3 * L) (by linarith))
  · intro z
    rfl
  · exact norm_sphereSaturation_le_two (3 * L) (by linarith)

end OnePoint

end SaturationEntropy
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapTerminalEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction.TerminalEntropy

open RawInvariantSets

theorem zero_semiconj (L : ℝ) (hL : 2 < L) :
    Function.Semiconj (zeroSlice ((50 : ℝ) : AddCircle (100 : ℝ)))
      (registers L hL) (concreteMap L hL) := by
  intro v
  exact (concreteMap_fifty_zero L hL v).symm

theorem terminalSet_nonempty : terminalSet.Nonempty :=
  (zeroSet_nonempty 3 ((50 : ℝ) : AddCircle (100 : ℝ))).mono Set.subset_union_left

theorem isCompact_terminalSet : IsCompact terminalSet :=
  (isCompact_zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ))).union
    (isCompact_rawInfinitySet 3)

theorem concreteMap_mapsTo_zero (L : ℝ) (hL : 2 < L) :
    Set.MapsTo (concreteMap L hL)
      (zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ)))
      (zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ))) := by
  rintro x ⟨v, rfl⟩
  exact ⟨registers L hL v, zero_semiconj L hL v⟩

theorem concreteMap_mapsTo_terminal (L : ℝ) (hL : 2 < L) :
    Set.MapsTo (concreteMap L hL) terminalSet terminalSet := by
  intro x hx
  rcases hx with hz | hi
  · exact Or.inl (concreteMap_mapsTo_zero L hL hz)
  · exact Or.inr (concreteMap_mapsTo_infinitySet L hL hi)

theorem coverEntropy_zero_image (L : ℝ) (hL : 2 < L)
    {X : Type*} [UniformSpace X] {T : X → X}
    {φ : RawManifold → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (concreteMap L hL) T) :
    Dynamics.coverEntropy T
      (φ '' zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ))) = 0 := by
  let : UniformSpace (OnePoint ℂ) := uniformSpaceOfCompactR1
  have hregisters : Dynamics.coverEntropy (registers L hL) Set.univ = 0 := by
    have h := SaturationEntropy.coverEntropy_onePoint_saturation L (by linarith) 3
    have heq : registers L hL = RadialRegisterEntropy.coordinatewise
        (fun x : OnePoint ℂ => ((L • sphereSaturation (3 * L) (by linarith) x : ℂ) :
          OnePoint ℂ)) 3 := by
      funext v i
      exact congrArg ((↑) : ℂ → OnePoint ℂ) Complex.real_smul.symm
    rw [heq]
    exact h
  let ψ : (Fin 3 → Sphere) → X :=
    φ ∘ zeroSlice ((50 : ℝ) : AddCircle (100 : ℝ))
  have hψ : Continuous ψ := hφ.comp (continuous_zeroSlice _)
  have hs : Function.Semiconj ψ (registers L hL) T := by
    intro v
    exact (congrArg φ (zero_semiconj L hL v)).trans
      (hsem (zeroSlice ((50 : ℝ) : AddCircle (100 : ℝ)) v))
  have hrange : Set.range ψ =
      φ '' zeroSet 3 ((50 : ℝ) : AddCircle (100 : ℝ)) := by
    exact Set.range_comp _ _
  rw [← hrange]
  apply le_antisymm _ (Dynamics.coverEntropy_nonneg T (Set.range_nonempty ψ))
  have h := Dynamics.coverEntropy_image_le_of_uniformContinuous hs
    (CompactSpace.uniformContinuous_of_continuous hψ) Set.univ
  simpa only [Set.image_univ, hregisters] using h

theorem coverEntropy_terminal_image (L : ℝ) (hL : 2 < L)
    {X : Type*} [UniformSpace X] {T : X → X}
    {φ : RawManifold → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (concreteMap L hL) T) :
    Dynamics.coverEntropy T (φ '' terminalSet) = 0 := by
  rw [terminalSet, Set.image_union, Dynamics.coverEntropy_union,
    coverEntropy_zero_image L hL hφ hsem,
    coverEntropy_concreteInfinity_image L hL hφ hsem, max_self]

theorem mapsTo_terminal_image (L : ℝ) (hL : 2 < L)
    {X : Type*} {T : X → X} {φ : RawManifold → X}
    (hsem : Function.Semiconj φ (concreteMap L hL) T) :
    Set.MapsTo T (φ '' terminalSet) (φ '' terminalSet) := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨concreteMap L hL y, concreteMap_mapsTo_terminal L hL hy, hsem y⟩

theorem coverEntropy_eq_zero_of_terminal_attraction (L : ℝ) (hL : 2 < L)
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X] {T : X → X}
    (hT : Continuous T) {φ : RawManifold → X} (hφ : Continuous φ)
    (hsem : Function.Semiconj φ (concreteMap L hL) T)
    (hattract : ∀ x, Filter.Tendsto
      (fun n => Metric.infDist (T^[n] x) (φ '' terminalSet))
      Filter.atTop (nhds 0)) :
    Dynamics.coverEntropy T Set.univ = 0 := by
  exact Problem340.coverEntropy_eq_zero_of_pointwise_attraction hT
    (isCompact_terminalSet.image hφ) (terminalSet_nonempty.image φ)
    (mapsTo_terminal_image L hL hsem)
    (coverEntropy_terminal_image L hL hφ hsem) hattract

end Problem340.Construction.TerminalEntropy

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RealizedConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

attribute [local instance] OAI.Problem340.Construction.instFactLtRealOfNat_solutions_2
theorem realizedMap_semiconj (L : ℝ) (hL : 2 < L) :
    Function.Semiconj modelHomeomorph (concreteMap L hL) (realizedMap L hL) :=
  fun x => (realizedMap_modelHomeomorph L hL x).symm

theorem realizedMap_iterate (L : ℝ) (hL : 2 < L) (n : ℕ) (x : RawManifold) :
    (realizedMap L hL)^[n] (modelHomeomorph x) =
      modelHomeomorph ((concreteMap L hL)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      realizedMap_modelHomeomorph]

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.TopologicalAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set Metric
open scoped Topology

namespace Problem340.TopologicalAttraction

variable {ι X Y Z W : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem tendsto_snd_fiber [CompactSpace X] {l : Filter ι}
    (x : ι → X) {y : ι → Y} {b : Y} (hy : Tendsto y l (𝓝 b)) :
    Tendsto (fun i => (x i, y i)) l (𝓝ˢ {p : X × Y | p.2 = b}) := by
  have hx : Tendsto x l (𝓝ˢ (univ : Set X)) := by simp [nhdsSet_univ]
  have ht : Tendsto (fun i => (x i, y i)) l (𝓝ˢ ((univ : Set X) ×ˢ {b})) := by
    rw [isCompact_univ.nhdsSet_prod_eq isCompact_singleton, nhdsSet_singleton]
    exact hx.prodMk hy
  convert ht using 1
  congr 1
  ext p
  simp

theorem tendsto_fixed_clock_main [CompactSpace Z] {l : Filter ι}
    {x : ι → X} {y : ι → Y} (z : ι → Z) {a : X} {b : Y}
    (hx : Tendsto x l (𝓝 a)) (hy : Tendsto y l (𝓝 b)) :
    Tendsto (fun i => (x i, (y i, z i))) l
      (𝓝ˢ {p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b}) := by
  have hz : Tendsto z l (𝓝ˢ (univ : Set Z)) := by simp [nhdsSet_univ]
  have hyz : Tendsto (fun i => (y i, z i)) l (𝓝ˢ ({b} ×ˢ (univ : Set Z))) := by
    rw [isCompact_singleton.nhdsSet_prod_eq isCompact_univ, nhdsSet_singleton]
    exact hy.prodMk hz
  have ht : Tendsto (fun i => (x i, (y i, z i))) l
      (𝓝ˢ ({a} ×ˢ ({b} ×ˢ (univ : Set Z)))) := by
    rw [isCompact_singleton.nhdsSet_prod_eq (isCompact_singleton.prod isCompact_univ),
      nhdsSet_singleton]
    exact hx.prodMk hyz
  convert ht using 1
  congr 1
  ext p
  simp

theorem tendsto_fixed_main_registers [CompactSpace X] {l : Filter ι}
    (x : ι → X) {y : ι → Y} {z : ι → Z} {b : Y} {c : Z}
    (hy : Tendsto y l (𝓝 b)) (hz : Tendsto z l (𝓝 c)) :
    Tendsto (fun i => (x i, (y i, z i))) l
      (𝓝ˢ {p : X × (Y × Z) | p.2 = (b, c)}) :=
  tendsto_snd_fiber x (hy.prodMk_nhds hz)

theorem tendsto_two_attractors [CompactSpace X] [CompactSpace Z] {l : Filter ι}
    {x : ι → X} {y : ι → Y} {z : ι → Z} {a : X} {b₀ bInf : Y} {c : Z}
    (h : (Tendsto x l (𝓝 a) ∧ Tendsto y l (𝓝 b₀)) ∨
      (Tendsto y l (𝓝 bInf) ∧ Tendsto z l (𝓝 c))) :
    Tendsto (fun i => (x i, (y i, z i))) l
      (𝓝ˢ ({p : X × (Y × Z) | p.1 = a ∧ p.2.1 = b₀} ∪
       {p : X × (Y × Z) | p.2 = (bInf, c)})) := by
  rcases h with ⟨hx, hy⟩ | ⟨hy, hz⟩
  · exact (tendsto_fixed_clock_main z hx hy).mono_right (nhdsSet_mono subset_union_left)
  · exact (tendsto_fixed_main_registers x hy hz).mono_right (nhdsSet_mono subset_union_right)

theorem tendsto_image [TopologicalSpace W] {l : Filter ι} {u : ι → X}
    {s : Set X} {p : X → W} (hp : Continuous p) (h : Tendsto u l (𝓝ˢ s)) :
    Tendsto (fun i => p (u i)) l (𝓝ˢ (p '' s)) :=
  (hp.tendsto_nhdsSet (mapsTo_image p s)).comp h

theorem tendsto_infDist [PseudoMetricSpace W] {l : Filter ι} {u : ι → W}
    {s : Set W} (h : Tendsto u l (𝓝ˢ s)) :
    Tendsto (fun i => infDist (u i) s) l (𝓝 0) := by
  exact ((continuous_infDist_pt s).tendsto_nhdsSet_nhds
    (fun _ hs => infDist_zero_of_mem hs)).comp h

theorem tendsto_infDist_image [PseudoMetricSpace W] {l : Filter ι} {u : ι → X}
    {s : Set X} {p : X → W} (hp : Continuous p) (h : Tendsto u l (𝓝ˢ s)) :
    Tendsto (fun i => infDist (p (u i)) (p '' s)) l (𝓝 0) :=
  tendsto_infDist (tendsto_image hp h)

end Problem340.TopologicalAttraction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology OnePoint

namespace Problem340.Construction

theorem tendsto_terminalSet_of_coordinate_alternatives (p : ℕ → RawManifold)
    (h : (Tendsto (fun n => (p n).1) atTop
          (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
        Tendsto (fun n => (p n).2.1) atTop (𝓝 (((0 : ℂ) : Sphere)))) ∨
      (Tendsto (fun n => (p n).2.1) atTop (𝓝 (∞ : Sphere)) ∧
        ∀ i : Fin 3, ∀ᶠ n in atTop, (p n).2.2 i = ((0 : ℂ) : Sphere))) :
    Tendsto p atTop (𝓝ˢ TerminalEntropy.terminalSet) := by
  have hcoords :
      (Tendsto (fun n => (p n).1) atTop
          (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
        Tendsto (fun n => (p n).2.1) atTop (𝓝 (((0 : ℂ) : Sphere)))) ∨
      (Tendsto (fun n => (p n).2.1) atTop (𝓝 (∞ : Sphere)) ∧
        Tendsto (fun n => (p n).2.2) atTop
          (𝓝 (fun _ : Fin 3 => ((0 : ℂ) : Sphere)))) := by
    rcases h with h | ⟨hmain, hreset⟩
    · exact Or.inl h
    · refine Or.inr ⟨hmain, tendsto_pi_nhds.mpr fun i => ?_⟩
      exact tendsto_const_nhds.congr' (by
        filter_upwards [hreset i] with n hn using hn.symm)
  have htop := TopologicalAttraction.tendsto_two_attractors hcoords
  have hset :
      ({p : RawManifold | p.1 = ((50 : ℝ) : AddCircle (100 : ℝ)) ∧
          p.2.1 = ((0 : ℂ) : Sphere)} ∪
        {p : RawManifold | p.2 = (∞, fun _ => ((0 : ℂ) : Sphere))}) =
      TerminalEntropy.terminalSet := by
    ext x
    simp only [TerminalEntropy.terminalSet, Set.mem_union, Set.mem_ofPred_eq,
      RawInvariantSets.mem_zeroSet_iff, mem_rawInfinitySet_iff]
    rw [show x.2 = (∞, fun _ => ((0 : ℂ) : Sphere)) ↔
        x.2.1 = ∞ ∧ ∀ i, x.2.2 i = ((0 : ℂ) : Sphere) by
      rw [Prod.ext_iff, funext_iff]]
  simpa only [hset] using htop

theorem coverEntropy_realizedMap_eq_zero_of_orbit_alternatives
    (L : ℝ) (hL : 2 < L)
    (horbit : ∀ x : RawManifold,
      (Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
          (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
        Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
          (𝓝 (((0 : ℂ) : Sphere)))) ∨
      (Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop (𝓝 (∞ : Sphere)) ∧
        ∀ i : Fin 3, ∀ᶠ n in atTop,
          ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere))) :
    Dynamics.coverEntropy (realizedMap L hL) Set.univ = 0 := by
  apply TerminalEntropy.coverEntropy_eq_zero_of_terminal_attraction L hL
    (continuous_realizedMap L hL (continuous_concreteMap L hL))
    modelHomeomorph.continuous (realizedMap_semiconj L hL)
  intro y
  obtain ⟨x, rfl⟩ := modelHomeomorph.surjective y
  have h := TopologicalAttraction.tendsto_infDist_image modelHomeomorph.continuous
    (tendsto_terminalSet_of_coordinate_alternatives (fun n => (concreteMap L hL)^[n] x) (horbit x))
  simpa only [realizedMap_iterate] using h

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapGlobalEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Set
open scoped Topology OnePoint

namespace Problem340.Construction

lemma exists_period_representative (t : ℝ) :
    ∃ k : ℤ, t - 100 * (k : ℝ) ∈ Set.Ico (0 : ℝ) 100 := by
  refine ⟨⌊t / 100⌋, ?_⟩
  have hlo := Int.floor_le (t / 100)
  have hhi := Int.lt_floor_add_one (t / 100)
  constructor <;> linarith

theorem rawOrbit_main_square_of_no_readout (D : SphereData)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1) (n : ℕ)
    (hquiet : ∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < rawClockLift D x t₀ n ∧
      rawClockLift D x t₀ n < 100 * (k : ℝ) + 80)) :
    ((rawMap D)^[n + 1] x).2.1 = perturbedSquare 0 (((rawMap D)^[n] x).2.1) := by
  obtain ⟨k, hk⟩ := exists_period_representative (rawClockLift D x t₀ n)
  have hcoeff : ∀ i : Fin 3,
      readoutCoeff i (rawClockLift D x t₀ n - 100 * (k : ℝ)) = 0 := by
    intro i
    by_contra h
    have hs : rawClockLift D x t₀ n - 100 * (k : ℝ) ∈
        Function.support (readoutCoeff i) := h
    rw [readoutCoeff_support] at hs
    have hwindow := readoutInterval_subset i hs
    exact hquiet k ⟨by linarith [hwindow.1], by linarith [hwindow.2]⟩
  simpa only [hcoeff, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero]
    using main_update_at_passage_clock D x t₀ h₀ k n hk

theorem rawOrbit_norm_square_of_no_readout (D : SphereData)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1)
    (n : ℕ)
    (hquiet : ∀ k : ℤ, ¬ (100 * (k : ℝ) + 74 < rawClockLift D x t₀ n ∧
      rawClockLift D x t₀ n < 100 * (k : ℝ) + 80)) :
    ‖z (n + 1)‖ = ‖z n‖ ^ 2 := by
  have heq := rawOrbit_main_square_of_no_readout D x t₀ h₀ n hquiet
  rw [← hz (n + 1), ← hz n, perturbedSquare_coe, add_zero] at heq
  have hzsq : z (n + 1) = z n ^ 2 := OnePoint.coe_injective heq
  rw [hzsq, norm_pow]

theorem rawOrbit_main_tendsto_infty_of_norm (D : SphereData)
    (x : RawManifold) (z : ℕ → ℂ)
    (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1)
    (hescape : Tendsto (fun n => ‖z n‖) atTop atTop) :
    Tendsto (fun n => ((rawMap D)^[n] x).2.1) atTop (𝓝 (∞ : Sphere)) := by
  exact (GlobalEscape.tendsto_coe_infty_of_norm hescape).congr hz

theorem rawOrbit_norm_tendsto_atTop_of_complete_passages (D : SphereData)
    (hgate : ∀ w, D.gate w ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((rawMap D)^[n] x).2.1)
    (hpass : ∀ k : ℤ, t₀ < 100 * (k : ℝ) →
      ∃ s hi : ℕ, 100 * (k : ℝ) ≤ rawClockLift D x t₀ s ∧
        rawClockLift D x t₀ s < 100 * (k : ℝ) + 74 ∧
        100 * (k : ℝ) + 80 ≤ rawClockLift D x t₀ hi ∧
        (∀ n, s ≤ n → n < hi → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖) ∧
        ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < ‖z j‖) :
    Tendsto (fun n => ‖z n‖) atTop atTop := by
  apply GlobalEscape.tendsto_atTop_of_complete_passages
    (rawClockLift D x t₀) (fun n => ‖z n‖)
    (monotone_rawClockLift D hgate x t₀) (fun n => norm_nonneg (z n))
  · intro n hn
    exact (rawOrbit_norm_square_of_no_readout D x t₀ h₀ z hz n hn).ge
  · simpa only [rawClockLift_zero] using hpass

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapInfinityAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped OnePoint

namespace Problem340.ConstructionInfinityAttraction

open Construction ConstructionErasure

local instance instFactLtRealOfNat_solutions_rad4b56_2 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
theorem raw_iterate_main_infty (D : SphereData) (x : RawManifold)
    (hx : x.2.1 = ∞) (n : ℕ) : ((rawMap D)^[n] x).2.1 = ∞ := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change perturbedSquare _ (((rawMap D)^[n] x).2.1) = ∞
      rw [ih]
      rfl

end Problem340.ConstructionInfinityAttraction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem preparation_before_readout {t : ℕ → ℝ} (hmono : Monotone t)
    {i j : ℕ} {l : Fin 3}
    (hi : preparationCoeff (t i) ≠ 0) (hj : readoutCoeff l (t j) ≠ 0) : i < j := by
  have hi' : t i ∈ Set.Ioo 8 12 := by
    rw [← preparationCoeff_support]
    exact hi
  have hj' : t j ∈ readoutInterval l := by
    rw [← readoutCoeff_support]
    exact hj
  have hj'' := readoutInterval_subset l hj'
  by_contra h
  have := hmono (show j ≤ i by omega)
  linarith [hi'.2, hj''.1]

theorem clock_passage_scheduling_at (D : SphereData)
    {t : ℕ → ℝ} {z : ℕ → Sphere}
    (hgate0 : ∀ z, 0 ≤ D.gate z) (hgate1 : ∀ z, D.gate z ≤ 1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (z n)))
    (hunbounded : ¬ BddAbove (Set.range t))
    (k : ℤ) (hstart : t 0 < 100 * (k : ℝ)) :
    HasScheduledPassageAt t k := by
  classical
  have hmono : Monotone t := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hclock n]
    exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate0 _))
  have hstep : ∀ n, t (n + 1) ≤ t n + 1 := by
    intro n
    rw [hclock n]
    exact add_le_add_right (Clock.increment_le_one _ (hgate1 _)) _
  have hreach : ∀ A : ℝ, ∃ n, A ≤ t n := by
    intro A
    obtain ⟨x, ⟨n, rfl⟩, hn⟩ := not_bddAbove_iff.mp hunbounded A
    exact ⟨n, hn.le⟩
  obtain ⟨lo, hi, hlohi, hlo, hlo', hhi, hhi', hinside⟩ :=
    exists_complete_clock_passage hmono hstep hstart hreach
  let s := fun n => t n - 100 * (k : ℝ)
  let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (s i))
  have hmonoS : Monotone s := by
    intro i j hij
    exact sub_le_sub_right (hmono hij) _
  have hstepS : ∀ n, s (n + 1) ≤ s n + 1 := by
    intro n
    dsimp [s]
    linarith [hstep n]
  have hstartS : s lo < 1 := by dsimp [s]; linarith
  have hendS : 100 ≤ s hi := by dsimp [s]; linarith
  have hsupport : ∀ x, 0 < preparationCoeff x → 8 < x ∧ x < 12 := by
    intro x hx
    have hx' : x ∈ Function.support preparationCoeff := ne_of_gt hx
    rwa [preparationCoeff_support] at hx'
  have hunitS : ∀ n, 8 ≤ s n → s n ≤ 12 → s (n + 1) = s n + 1 := by
    intro n hn0 hn1
    have hbarrier : Clock.barrier (s n) = 1 := by
      apply Clock.barrier_plateau (by linarith) (by linarith)
      rw [abs_of_nonpos (by linarith : s n - 50 ≤ 0)]
      linarith
    have hperiod := (Clock.increment_periodic (D.gate (z n))).sub_int_mul_eq
      (x := t n) k
    have hinc : Clock.increment (t n) (D.gate (z n)) = 1 := by
      rw [← hperiod]
      have heq : t n - (k : ℝ) * 100 = s n := by dsimp [s]; ring
      rw [heq]
      exact Clock.increment_eq_one_of_barrier_eq_one hbarrier
    dsimp [s]
    rw [hclock n, hinc]
    ring
  have hprep := preparation_indices_properties hmonoS hstepS hlohi.le hstartS hendS
    hsupport (fun x hx0 hx1 => preparationCoeff_eq_one ⟨hx0, hx1⟩) hunitS
  change I.Nonempty ∧ I.card ≤ 5 ∧ (∃ i ∈ I, preparationCoeff (s i) = 1) at hprep
  obtain ⟨r, hr, hr0, hr1, hrbefore⟩ :=
    exists_reset_before_preparation hmonoS hstepS hlohi.le hstartS hendS
  have hread := exists_readout_plateau hmonoS hstepS hlohi.le hstartS hendS
    (fun x hx0 hx1 => readoutCoeff_cover ⟨hx0, hx1⟩)
  have hlobounds : 0 ≤ s lo ∧ s lo < 1 := by
    dsimp [s]
    constructor <;> linarith
  have hhibounds : 100 ≤ s hi ∧ s hi < 101 := by
    dsimp [s]
    constructor <;> linarith
  refine ⟨lo, hi, hlohi, hlobounds, hhibounds, ?_,
    hprep.1, hprep.2.1, hprep.2.2, ?_, hread⟩
  · intro n hnlo hnhi
    have hn := hinside n hnlo hnhi
    change 0 ≤ s n ∧ s n < 100
    dsimp [s]
    constructor <;> linarith [hn.1, hn.2]
  · refine ⟨r, hr, hr0, hr1, ?_⟩
    intro i hiI
    exact hrbefore i (hsupport _ (Finset.mem_filter.mp hiI).2).1

theorem rawOrbit_hasScheduledPassageAt (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift D x t₀)))
    (k : ℤ) (hstart : t₀ < 100 * (k : ℝ)) :
    HasScheduledPassageAt (rawClockLift D x t₀) k :=
  clock_passage_scheduling_at D
    (fun z => (hgate z).1) (fun z => (hgate z).2)
    (rawClockLift_succ D x t₀ h₀) hunbounded k (by simpa using hstart)

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapSignals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

theorem preparationCoeff_eq_zero_of_outside {t : ℝ} (ht : t ∉ Set.Ioo 8 12) :
    preparationCoeff t = 0 := by
  by_contra h
  have hs : t ∈ Function.support preparationCoeff := h
  rw [preparationCoeff_support] at hs
  exact ht hs

theorem baseInput_eq_zero_of_outside (D : SphereData) (i : Fin 3)
    {t : ℝ} (ht : t ∉ Set.Ioo 8 12) (z : Sphere) : baseInput D i t z = 0 := by
  simp [baseInput, preparationCoeff_eq_zero_of_outside ht]

theorem input_eq_zero_of_coe_outside (D : SphereData) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Set.Ico 0 100) (hout : t ∉ Set.Ioo 8 12) (z : Sphere) :
    input D i (t : AddCircle (100 : ℝ)) z = 0 := by
  rw [input, AddCircle.liftIco_zero_coe_apply ht]
  exact baseInput_eq_zero_of_outside D i hout z

theorem concreteMap_register_reset (L : ℝ) (hL : 2 < L)
    {t : ℝ} (ht : t ∈ Set.Icc 2 5) (z : Sphere) (v : Fin 3 → Sphere) (i : Fin 3) :
    (concreteMap L hL ((t : AddCircle (100 : ℝ)), z, v)).2.2 i = ((0 : ℂ) : Sphere) := by
  have hstrip : t ∈ Set.Ico (0 : ℝ) 100 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hout : t ∉ Set.Ioo (8 : ℝ) 12 := by
    intro h
    linarith [ht.2, h.1]
  have hg : periodicGain (concreteData L hL) (t : AddCircle (100 : ℝ)) = 0 := by
    rw [periodicGain, AddCircle.liftIco_zero_coe_apply hstrip]
    exact gainProfile_eq_zero L ht
  simp [concreteMap, rawMap, hg, input_eq_zero_of_coe_outside _ _ hstrip hout z]

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RegisterReset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem340.Register

variable {X E : Type*} [AddCommGroup E] [Module ℝ E]

theorem register_zero_on_interval
    (x0 : X) (embed : E → X) (hembed : embed 0 = x0) (S : X → E) (hS : S x0 = 0)
    (a : ℕ → ℝ) (input : ℕ → E) (v : ℕ → X)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + input n))
    (s j : ℕ) (hvs : v s = x0)
    (hu : ∀ n, s ≤ n → n < j → input n = 0) :
    ∀ n, s ≤ n → n ≤ j → v n = x0 := by
  intro n hsn
  induction n, hsn using Nat.le_induction with
  | base => exact fun _ => hvs
  | succ n hsn ih =>
      intro hnj
      have hn : n ≤ j := by omega
      have hu' : input n = 0 := hu n hsn (by omega)
      simp [hrec n, ih hn, hS, hu', hembed]

end Problem340.Register

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapPreparationReset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem rawMap_register_zero_on_inactive_interval
    (D : SphereData) (hS : D.saturation ((0 : ℂ) : Sphere) = 0)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (s j : ℕ) (hzero : ∀ i, (x s).2.2 i = ((0 : ℂ) : Sphere))
    (hstrip : ∀ n, s ≤ n → n < j → t n ∈ Set.Ico 0 100)
    (hprep : ∀ n, s ≤ n → n < j → preparationCoeff (t n) = 0) :
    ∀ n, s ≤ n → n ≤ j → ∀ i, (x n).2.2 i = ((0 : ℂ) : Sphere) := by
  intro n hsn hnj i
  apply Register.register_zero_on_interval
    ((0 : ℂ) : Sphere) (fun z : ℂ => (z : Sphere)) rfl D.saturation hS
    (fun m => periodicGain D (x m).1)
    (fun m => input D i (x m).1 (x m).2.1)
    (fun m => (x m).2.2 i) ?_ s j (hzero i) ?_ n hsn hnj
  · intro m
    simp only [horbit m, rawMap, Complex.real_smul]
  · intro m hsm hmj
    rw [← hlift m, input, AddCircle.liftIco_zero_coe_apply (hstrip m hsm hmj)]
    simp [baseInput, hprep m hsm hmj]

theorem concreteMap_register_zero_after_reset_before_preparation
    (L : ℝ) (hL : 2 < L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = concreteMap L hL (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (r s : ℕ) (hrs : r + 1 ≤ s) (hreset : t r ∈ Set.Icc 2 5)
    (hstrip : ∀ n, r + 1 ≤ n → n < s → t n ∈ Set.Ico 0 100)
    (hprep : ∀ n, r + 1 ≤ n → n < s → preparationCoeff (t n) = 0) :
    ∀ i, (x s).2.2 i = ((0 : ℂ) : Sphere) := by
  have hzero : ∀ i, (x (r + 1)).2.2 i = ((0 : ℂ) : Sphere) := by
    intro i
    rw [horbit r]
    change (concreteMap L hL ((x r).1, (x r).2.1, (x r).2.2)).2.2 i = _
    rw [← hlift r]
    exact concreteMap_register_reset L hL hreset _ _ i
  exact rawMap_register_zero_on_inactive_interval (concreteData L hL)
    (concrete_saturation_zero L hL) x horbit t hlift (r + 1) s hzero
    hstrip hprep s hrs le_rfl

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapPassageSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_4 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem preparation_phase_window
    {t : ℕ → ℝ} (hmono : Monotone t) (I : Finset ℕ) (hne : I.Nonempty)
    {lo hi : ℕ} (hI : ∀ i ∈ I, lo ≤ i ∧ i < hi)
    (hprep : ∀ i ∈ I, preparationCoeff (t i) ≠ 0) :
    ∃ s K : ℕ, s ∈ I ∧ lo ≤ s ∧ s < K ∧ K ≤ hi ∧
      (∀ i ∈ I, s ≤ i ∧ i < K) ∧
      (∀ n, s ≤ n → n < K → ∀ l : Fin 3, readoutCoeff l (t n) = 0) ∧
      t s ∈ Set.Ioo 8 12 := by
  classical
  let s := I.min' hne
  let K := I.max' hne + 1
  have hs : s ∈ I := Finset.min'_mem I hne
  have hmax : I.max' hne ∈ I := Finset.max'_mem I hne
  have hsmax : s ≤ I.max' hne := Finset.min'_le_max' I hne
  have hK : K ≤ hi := by
    have := (hI _ hmax).2
    dsimp [K]
    omega
  refine ⟨s, K, hs, (hI _ hs).1, by dsimp [K]; omega, hK, ?_, ?_, ?_⟩
  · intro i hiI
    have hmin : s ≤ i := Finset.min'_le I i hiI
    have hmax' : i ≤ I.max' hne := Finset.le_max' I i hiI
    exact ⟨hmin, by dsimp [K]; omega⟩
  · intro n _ hn l
    by_contra hb
    have hbefore := preparation_before_readout hmono (hprep _ hmax) hb
    dsimp [K] at hn
    omega
  · rw [← preparationCoeff_support]
    exact hprep _ hs

theorem orbitReadoutCoeff_eq_of_clock_lift
    (x : ℕ → RawManifold) (t : ℕ → ℝ)
    (hclock : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (n : ℕ) (hn : t n ∈ Set.Ico (0 : ℝ) 100) (l : Fin 3) :
    orbitReadoutCoeff x n l = readoutCoeff l (t n) := by
  unfold orbitReadoutCoeff
  rw [← hclock n]
  exact AddCircle.liftIco_coe_apply (p := (100 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hn)

theorem complete_passage_phase_window
    (x : ℕ → RawManifold) (t : ℕ → ℝ) (hmono : Monotone t)
    (hclock : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (lo hi : ℕ)
    (hinside : ∀ n, lo ≤ n → n < hi → t n ∈ Set.Ico (0 : ℝ) 100)
    (hne : ((Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i))).Nonempty) :
    let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i))
    ∃ s K : ℕ, s ∈ I ∧ lo ≤ s ∧ s < K ∧ K ≤ hi ∧
      (∀ i ∈ I, s ≤ i ∧ i < K) ∧
      (∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0) ∧
      t s ∈ Set.Ioo 8 12 := by
  classical
  let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i))
  have hI : ∀ i ∈ I, lo ≤ i ∧ i < hi := by
    intro i hiI
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hiI).1
  have hp : ∀ i ∈ I, preparationCoeff (t i) ≠ 0 := by
    intro i hiI
    exact ne_of_gt (Finset.mem_filter.mp hiI).2
  obtain ⟨s, K, hs, hlos, hsK, hKhi, hIK, hearly, hts⟩ :=
    preparation_phase_window hmono I hne hI hp
  refine ⟨s, K, hs, hlos, hsK, hKhi, hIK, ?_, hts⟩
  intro n hsn hnK l
  rw [orbitReadoutCoeff_eq_of_clock_lift x t hclock n
    (hinside n (by omega) (by omega)) l]
  exact hearly n hsn hnK l

theorem complete_passage_register_reset_at_first_preparation
    (L : ℝ) (hL : 2 < L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = concreteMap L hL (x n))
    (t : ℕ → ℝ) (hclock : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (lo hi r s : ℕ) (hlor : lo ≤ r) (hrs : r + 1 ≤ s) (hshi : s < hi)
    (hreset : t r ∈ Set.Icc 2 5)
    (hinside : ∀ n, lo ≤ n → n < hi → t n ∈ Set.Ico (0 : ℝ) 100)
    (hfirst : ∀ i ∈ (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i)),
      s ≤ i) :
    ∀ l : Fin 3, (x s).2.2 l = ((0 : ℂ) : Sphere) := by
  apply concreteMap_register_zero_after_reset_before_preparation
    L hL x horbit t hclock r s hrs hreset
  · intro n hrn hns
    exact hinside n (by omega) (by omega)
  · intro n hrn hns
    by_contra hp
    have hp' : 0 < preparationCoeff (t n) :=
      lt_of_le_of_ne (preparationCoeff_nonneg _) (Ne.symm hp)
    have hnI : n ∈ (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hp'⟩
    have := hfirst n hnI
    omega

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapPreparationRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped OnePoint

namespace Problem340.Construction

theorem periodicReadout_eq_zero_before_readout (i : Fin 3) (t : ℝ) (k : ℤ)
    (hlo : 0 ≤ t - (k : ℝ) * 100) (hhi : t - (k : ℝ) * 100 ≤ 74) :
    periodicReadout i (t : AddCircle (100 : ℝ)) = 0 := by
  have hperiod := (periodicReadout_coe_periodic i).sub_int_mul_eq (x := t) k
  change periodicReadout i ((t - (k : ℝ) * 100 : ℝ) : AddCircle (100 : ℝ)) =
    periodicReadout i (t : AddCircle (100 : ℝ)) at hperiod
  rw [← hperiod, periodicReadout,
    AddCircle.liftIco_coe_apply (show t - (k : ℝ) * 100 ∈ Set.Ico (0 : ℝ) (0 + 100) by
      exact ⟨hlo, by linarith⟩)]
  by_contra hn
  have hs : t - (k : ℝ) * 100 ∈ Function.support (readoutCoeff i) := hn
  rw [readoutCoeff_support] at hs
  have hread := readoutInterval_subset i hs
  linarith [hread.1]

theorem concrete_norm_gt_half_before_barrier (L : ℝ) (hL : 2 < L)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀)))
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1)
    (N : ℕ) (k : ℤ)
    (hstart : 8 ≤ rawClockLift (concreteData L hL) x t₀ N - (k : ℝ) * 100 ∧
      rawClockLift (concreteData L hL) x t₀ N - (k : ℝ) * 100 ≤ 50) :
    1 / 2 < ‖z N‖ := by
  let t := rawClockLift (concreteData L hL) x t₀
  let s : ℕ → ℝ := fun n => t n - (k : ℝ) * 100
  have hmono : Monotone s := by
    intro i j hij
    exact sub_le_sub_right (monotone_rawClockLift _ (concrete_gate_mem_Icc L hL)
      x t₀ hij) _
  have hunbounded' : ¬ BddAbove (Set.range s) := by
    rintro ⟨M, hM⟩
    apply hunbounded
    refine ⟨M + (k : ℝ) * 100, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hn := hM (Set.mem_range_self n)
    dsimp [s, t] at hn
    linarith
  apply ClockDynamics.preparation_norm_gt_half hmono hunbounded' hstart
  intro n _ hlo hhi hsmall
  have hgate : (concreteData L hL).gate (((concreteMap L hL)^[n] x).2.1) = 0 := by
    rw [← hz n]
    exact SphereCutoffs.affineClockGate_eq_zero hsmall
  have hstep := rawClockLift_succ (concreteData L hL) x t₀ h₀ n
  change t (n + 1) = t n + Clock.increment (t n)
    ((concreteData L hL).gate (((concreteMap L hL)^[n] x).2.1)) at hstep
  rw [hgate, Clock.increment_zero] at hstep
  have hbar : Clock.barrier (s n) = Clock.barrier (t n) :=
    Clock.barrier_periodic.sub_int_mul_eq k
  have hstop := Clock.barrier_stops (s n) hhi
  constructor
  · dsimp [s] at hbar hstop ⊢
    linarith
  · have hread : readout (concreteData L hL) (((concreteMap L hL)^[n] x).1)
        (((concreteMap L hL)^[n] x).2.2) = 0 := by
      have hβ : ∀ i, periodicReadout i (((concreteMap L hL)^[n] x).1) = 0 := by
        intro i
        change periodicReadout i (((rawMap (concreteData L hL))^[n] x).1) = 0
        rw [← coe_rawClockLift (concreteData L hL) x t₀ h₀ n]
        apply periodicReadout_eq_zero_before_readout i _ k
        · change 0 ≤ s n
          linarith
        · change s n ≤ 74
          linarith
      simp [readout, hβ]
    rw [finiteMainOrbit_recurrence (concreteData L hL) x z hz n]
    change z n ^ 2 + readout (concreteData L hL) (((concreteMap L hL)^[n] x).1)
      (((concreteMap L hL)^[n] x).2.2) = z n ^ 2
    rw [hread, add_zero]

theorem concrete_preparation_radius (L : ℝ) (hL : 2 < L)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀)))
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1)
    (N : ℕ) (k : ℤ)
    (hprep : rawClockLift (concreteData L hL) x t₀ N - (k : ℝ) * 100 ∈ Set.Ioo 8 12) :
    1 / 2 < ‖z N‖ := by
  apply concrete_norm_gt_half_before_barrier L hL x t₀ h₀ hunbounded z hz N k
  exact ⟨hprep.1.le, by linarith [hprep.2]⟩

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.PredictionSignal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340

theorem prediction_input_eq_delayed_signal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L α βj : ℝ) (B : ℕ → ℝ) (Φ : ℕ → E)
    (i j : ℕ) (hij : i < j)
    (hhit : ∀ m : ℕ, 1 ≤ m → B m = if m = j - i then βj else 0) :
    (α / 10) • (∑' n : ℕ, ((L⁻¹) ^ n * B (n + 1)) • Φ (n + 1)) =
      L ^ (1 + (i : ℤ) - (j : ℤ)) • ((α * βj / 10) • Φ (j - i)) := by
  classical
  have hd : 1 ≤ j - i := by omega
  have hindex : j - i - 1 + 1 = j - i := by omega
  have hsum : (∑' n : ℕ, ((L⁻¹) ^ n * B (n + 1)) • Φ (n + 1)) =
      ((L⁻¹) ^ (j - i - 1) * βj) • Φ (j - i) := by
    rw [tsum_eq_single (j - i - 1)]
    · rw [hindex, hhit (j - i) hd, ite_eq_left rfl]
    · intro n hn
      have hne : n + 1 ≠ j - i := by omega
      rw [hhit (n + 1) (by omega), ite_eq_right hne]
      simp
  have hz : -(↑(j - i - 1) : ℤ) = 1 + (i : ℤ) - (j : ℤ) := by omega
  have hpow : (L⁻¹) ^ (j - i - 1) = L ^ (1 + (i : ℤ) - (j : ℤ)) := by
    rw [← hz, zpow_neg, zpow_natCast, inv_pow]
  rw [hsum, hpow, smul_smul, smul_smul]
  congr 1
  ring

end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapSignal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem baseInput_eq_delayed_signal
    (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere)
    (i j : ℕ) (hij : i < j)
    (hhit : ∀ m : ℕ, 1 ≤ m →
      readoutCoeff ℓ (predictedClock D m ti z) =
        if m = j - i then readoutCoeff ℓ tj else 0) :
    baseInput D ℓ ti z = D.L ^ (1 + (i : ℤ) - (j : ℤ)) •
      scheduledSignal D ℓ ti tj z (j - i) := by
  have h := prediction_input_eq_delayed_signal D.L (preparationCoeff ti)
    (readoutCoeff ℓ tj) (fun m => readoutCoeff ℓ (predictedClock D m ti z))
    (fun m => (D.cutoff z : ℂ) * phase z ^ (2 ^ (m + 1))) i j hij hhit
  simpa only [baseInput, inputTerm, scheduledSignal, Complex.real_smul,
    Complex.ofReal_mul, mul_assoc, Nat.add_assoc] using h

theorem input_eq_baseInput_of_mem_Ico
    (D : SphereData) (ℓ : Fin 3) {t : ℝ} (ht : t ∈ Set.Ico 0 100) (z : Sphere) :
    input D ℓ (t : AddCircle (100 : ℝ)) z = baseInput D ℓ t z := by
  exact AddCircle.liftIco_zero_coe_apply ht

theorem input_eq_delayed_signal
    (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere)
    (hti : ti ∈ Set.Ico 0 100) (i j : ℕ) (hij : i < j)
    (hhit : ∀ m : ℕ, 1 ≤ m →
      readoutCoeff ℓ (predictedClock D m ti z) =
        if m = j - i then readoutCoeff ℓ tj else 0) :
    input D ℓ (ti : AddCircle (100 : ℝ)) z =
      D.L ^ (1 + (i : ℤ) - (j : ℤ)) • scheduledSignal D ℓ ti tj z (j - i) := by
  rw [input_eq_baseInput_of_mem_Ico D ℓ hti z]
  exact baseInput_eq_delayed_signal D ℓ ti tj z i j hij hhit

theorem norm_scheduledSignal_le
    (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere) (delay : ℕ)
    (hχ : D.cutoff z ∈ Set.Icc 0 1) :
    ‖scheduledSignal D ℓ ti tj z delay‖ ≤ (1 / 10 : ℝ) := by
  have hα0 := preparationCoeff_nonneg ti
  have hα1 := preparationCoeff_le_one ti
  have hβ0 := readoutCoeff_nonneg ℓ tj
  have hβ1 := readoutCoeff_le_one ℓ tj
  have hc0 : 0 ≤ preparationCoeff ti * readoutCoeff ℓ tj / 10 := by positivity
  have hc1 : preparationCoeff ti * readoutCoeff ℓ tj / 10 ≤ (1 / 10 : ℝ) := by
    have h := mul_le_mul hα1 hβ1 hβ0 (show (0 : ℝ) ≤ 1 by norm_num)
    nlinarith
  have hphase : ‖phase z‖ ^ (2 ^ (delay + 1)) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_phase_le_one z)
  have hangular : ‖(D.cutoff z : ℂ) * phase z ^ (2 ^ (delay + 1))‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ.1]
    exact (mul_le_mul hχ.2 hphase (by positivity) (by norm_num)).trans_eq (by norm_num)
  rw [scheduledSignal, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  exact (mul_le_mul hc1 hangular (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem predictedClock_succ_eq_increment (D : SphereData) (n : ℕ) (t : ℝ) (z : Sphere) :
    predictedClock D (n + 1) t z = predictedClock D n t z +
      Clock.increment (predictedClock D n t z)
        (D.gate (((prediction D)^[n] (t, z)).2)) := by
  rw [predictedClock, Function.iterate_succ_apply']
  rfl

theorem predictedClock_monotone_of_gate_nonneg (D : SphereData)
    (hgate : ∀ z, 0 ≤ D.gate z) (t : ℝ) (z : Sphere) :
    Monotone (fun n => predictedClock D n t z) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [predictedClock_succ_eq_increment]
  exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate _))

theorem barrier_eq_one_of_readoutCoeff_ne_zero (ℓ : Fin 3) {t : ℝ}
    (ht : readoutCoeff ℓ t ≠ 0) : Clock.barrier t = 1 := by
  have hmem : t ∈ readoutInterval ℓ := by
    rwa [← readoutCoeff_support, Function.mem_support]
  have hbounds := readoutInterval_subset ℓ hmem
  apply Clock.barrier_plateau (by linarith [hbounds.1]) (by linarith [hbounds.2])
  rw [abs_of_nonneg (by linarith [hbounds.1])]
  linarith [hbounds.1]

theorem predictedClock_unit_step_at_readout
    (D : SphereData) (ℓ : Fin 3) (t : ℝ) (z : Sphere) (n : ℕ)
    (hn : readoutCoeff ℓ (predictedClock D n t z) ≠ 0) :
    predictedClock D (n + 1) t z = predictedClock D n t z + 1 := by
  rw [predictedClock_succ_eq_increment,
    Clock.increment_eq_one_of_barrier_eq_one (barrier_eq_one_of_readoutCoeff_ne_zero ℓ hn)]

theorem predicted_readout_single_hit
    (D : SphereData) (hgate : ∀ z, 0 ≤ D.gate z)
    (ℓ : Fin 3) (t : ℝ) (z : Sphere) {d : ℕ}
    (hd : readoutCoeff ℓ (predictedClock D d t z) ≠ 0) (n : ℕ) :
    readoutCoeff ℓ (predictedClock D n t z) =
      if n = d then readoutCoeff ℓ (predictedClock D d t z) else 0 := by
  classical
  by_cases hnd : n = d
  · simp [hnd]
  · rw [ite_eq_right hnd]
    by_contra hn
    apply hnd
    apply clock_readout_unique (predictedClock_monotone_of_gate_nonneg D hgate t z)
      (readoutInterval_length ℓ) ?_
      (predictedClock_unit_step_at_readout D ℓ t z) hn hd
    intro x hx
    change x ∈ readoutInterval ℓ
    rwa [← readoutCoeff_support, Function.mem_support]

theorem input_eq_delayed_signal_of_predicted_hit
    (D : SphereData) (hgate : ∀ z, 0 ≤ D.gate z)
    (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere)
    (hti : ti ∈ Set.Ico 0 100) (i j : ℕ) (hij : i < j)
    (hclock : predictedClock D (j - i) ti z = tj) (hread : readoutCoeff ℓ tj ≠ 0) :
    input D ℓ (ti : AddCircle (100 : ℝ)) z =
      D.L ^ (1 + (i : ℤ) - (j : ℤ)) • scheduledSignal D ℓ ti tj z (j - i) := by
  apply input_eq_delayed_signal D ℓ ti tj z hti i j hij
  intro m _
  have hd : readoutCoeff ℓ (predictedClock D (j - i) ti z) ≠ 0 := by
    rwa [hclock]
  simpa only [hclock] using predicted_readout_single_hit D hgate ℓ ti z hd m

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem readout_eq_zero_before_region
    (D : SphereData) {t : ℝ} (ht0 : 0 ≤ t) (ht74 : t < 74)
    (v : Fin 3 → Sphere) :
    readout D (t : AddCircle (100 : ℝ)) v = 0 := by
  have hstrip : t ∈ Set.Ico 0 100 := ⟨ht0, by linarith⟩
  have hβ : ∀ ℓ : Fin 3, readoutCoeff ℓ t = 0 := by
    intro ℓ
    by_contra h
    have hmem : t ∈ readoutInterval ℓ := by
      rwa [← readoutCoeff_support, Function.mem_support]
    have hbounds := readoutInterval_subset ℓ hmem
    linarith [hbounds.1]
  simp only [readout, periodicReadout, AddCircle.liftIco_zero_coe_apply hstrip,
    hβ, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem increment_eq_one_on_readout_band {t e : ℝ}
    (ht : t ∈ Set.Icc 70 82) : Clock.increment t e = 1 := by
  apply Clock.increment_eq_one_of_barrier_eq_one
  apply Clock.barrier_plateau (by linarith [ht.1]) (by linarith [ht.2])
  rw [abs_of_nonneg (by linarith [ht.1])]
  linarith [ht.1]

theorem rawMap_predictedClock_at_readout
    (D : SphereData)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (ht : Monotone t)
    (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (ℓ : Fin 3) (i j : ℕ) (hij : i ≤ j) (hti : 0 ≤ t i)
    (hread : readoutCoeff ℓ (t j) ≠ 0) :
    predictedClock D (j - i) (t i) (x i).2.1 = t j := by
  have hmem : t j ∈ readoutInterval ℓ := by
    rwa [← readoutCoeff_support, Function.mem_support]
  have hjbounds := readoutInterval_subset ℓ hmem
  let A : ℕ → ℝ × Sphere := fun n => (t (i + n), (x (i + n)).2.1)
  let P : ℕ → ℝ × Sphere := fun n => (prediction D)^[n] (t i, (x i).2.1)
  have hAstep : ∀ n, (A n).1 < 70 → A (n + 1) = prediction D (A n) := by
    intro n hn
    have htn0 : 0 ≤ t (i + n) := hti.trans (ht (by omega))
    have hzero : readout D (x (i + n)).1 (x (i + n)).2.2 = 0 := by
      rw [← hlift (i + n)]
      exact readout_eq_zero_before_region D htn0 (by change t (i + n) < 70 at hn; linarith) _
    apply Prod.ext
    · change t (i + (n + 1)) = t (i + n) +
        Clock.increment (t (i + n)) (D.gate (x (i + n)).2.1)
      simpa only [Nat.add_assoc] using hclock (i + n)
    · change (x (i + (n + 1))).2.1 = perturbedSquare 0 (x (i + n)).2.1
      rw [← Nat.add_assoc, horbit (i + n)]
      change perturbedSquare (readout D (x (i + n)).1 (x (i + n)).2.2)
        (x (i + n)).2.1 = _
      rw [hzero]
  have hPstep : ∀ n, P (n + 1) = prediction D (P n) := by
    intro n
    exact Function.iterate_succ_apply' (prediction D) n _
  have hagree : ∀ n ≤ j - i, (A n).1 = (P n).1 := by
    apply clock_prediction_agreement (clock := Prod.fst) (a := 70) (b := 82)
    · simp [A, P]
    · intro n _ heq hn
      rw [hAstep n hn, hPstep n, heq]
    · intro n _ hn0 hn1
      change t (i + (n + 1)) = t (i + n) + 1
      rw [← Nat.add_assoc, hclock (i + n),
        increment_eq_one_on_readout_band ⟨hn0, hn1⟩]
    · intro n _ hn0 hn1
      rw [hPstep n]
      change (P n).1 + Clock.increment (P n).1 (D.gate (P n).2) = (P n).1 + 1
      rw [increment_eq_one_on_readout_band ⟨hn0, hn1⟩]
    · intro n hn
      have hnt : t (i + n) ≤ t j := ht (by omega)
      change t (i + n) ≤ 82
      linarith [hjbounds.2]
  have hfinal := (hagree (j - i) le_rfl).symm
  simpa only [A, P, predictedClock, Nat.add_sub_of_le hij] using hfinal

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RegisterLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340
namespace Register

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem delayedCandidate_succ (L : ℝ) (hL : L ≠ 0) (j : ℕ)
    (c : ℕ → E) (n : ℕ) :
    delayedCandidate L j c (n + 1) =
      L • delayedCandidate L j c n +
        L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n := by
  have hp : L ^ (((n + 1 : ℕ) : ℤ) - (j : ℤ)) =
      L * L ^ ((n : ℤ) - (j : ℤ)) := by
    rw [show (((n + 1 : ℕ) : ℤ) - (j : ℤ)) =
      1 + ((n : ℤ) - (j : ℤ)) by omega, zpow_add₀ hL]
    simp
  unfold delayedCandidate
  rw [Finset.sum_range_succ, smul_add, hp, mul_smul]
  congr 1
  rw [← hp]
  congr 2

theorem norm_delayedCandidate_le (L : ℝ) (hL : 1 ≤ L) (j : ℕ)
    (c : ℕ → E) {R : ℝ}
    (hc : (∑ i ∈ Finset.range j, ‖c i‖) ≤ R)
    {n : ℕ} (hn : n ≤ j) :
    ‖delayedCandidate L j c n‖ ≤ R := by
  have hpow_nonneg : 0 ≤ L ^ ((n : ℤ) - (j : ℤ)) :=
    zpow_nonneg (by linarith) _
  have hpow_le : L ^ ((n : ℤ) - (j : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ hL (by omega)
  have hsum : (∑ i ∈ Finset.range n, ‖c i‖) ≤
      ∑ i ∈ Finset.range j, ‖c i‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun i _ _ => norm_nonneg (c i))
  calc
    ‖delayedCandidate L j c n‖ =
        L ^ ((n : ℤ) - (j : ℤ)) * ‖∑ i ∈ Finset.range n, c i‖ := by
      rw [delayedCandidate, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hpow_nonneg]
    _ ≤ 1 * ‖∑ i ∈ Finset.range n, c i‖ :=
      mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)
    _ = ‖∑ i ∈ Finset.range n, c i‖ := one_mul _
    _ ≤ ∑ i ∈ Finset.range n, ‖c i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range j, ‖c i‖ := hsum
    _ ≤ R := hc

omit [NormedSpace ℝ E] in

theorem coefficient_norm_sum_le_half {ι : Type*} (I : Finset ι) (c : ι → E)
    (hcard : I.card ≤ 5) (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ)) :
    (∑ i ∈ I, ‖c i‖) ≤ (1 / 2 : ℝ) := by
  calc
    (∑ i ∈ I, ‖c i‖) ≤ I.card • (1 / 10 : ℝ) :=
      Finset.sum_le_card_nsmul I (fun i => ‖c i‖) _ hc
    _ ≤ (1 / 2 : ℝ) := by
      simp only [nsmul_eq_mul]
      have : (I.card : ℝ) ≤ 5 := by exact_mod_cast hcard
      linarith

end Register
end Problem340

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.RegisterEmbedded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Register

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem embedded_delayed_register_linearity
    (L : ℝ) (hL : 1 ≤ L) (j : ℕ) (c : ℕ → E)
    (embed : E → X) (S : X → E) (v : ℕ → X)
    (hc : (∑ i ∈ Finset.range j, ‖c i‖) ≤ (1 / 2 : ℝ))
    (hS : ∀ z : E, ‖z‖ ≤ 1 → S (embed z) = z)
    (hv0 : v 0 = embed 0)
    (hstep : ∀ n < j, v (n + 1) = embed (L • S (v n) +
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n)) :
    (∀ n ≤ j, v n = embed (delayedCandidate L j c n)) ∧
      v j = embed (∑ i ∈ Finset.range j, c i) ∧
      S (v j) = ∑ i ∈ Finset.range j, c i ∧
      ‖S (v j)‖ ≤ (1 / 2 : ℝ) := by
  have hL0 : L ≠ 0 := by linarith
  have hmain : ∀ n ≤ j, v n = embed (delayedCandidate L j c n) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa using hv0
    | succ n ih =>
        intro hn
        have hn' : n ≤ j := by omega
        have hsmall : ‖delayedCandidate L j c n‖ ≤ 1 :=
          (norm_delayedCandidate_le L hL j c hc hn').trans (by norm_num)
        rw [hstep n (by omega), ih hn', hS _ hsmall]
        exact congrArg embed (delayedCandidate_succ L hL0 j c n).symm
  have hread : v j = embed (∑ i ∈ Finset.range j, c i) := by
    simpa using hmain j le_rfl
  have hbound : ‖∑ i ∈ Finset.range j, c i‖ ≤ (1 / 2 : ℝ) := by
    simpa using norm_delayedCandidate_le L hL j c hc (n := j) le_rfl
  have hsat : S (v j) = ∑ i ∈ Finset.range j, c i := by
    rw [hread]
    exact hS _ (hbound.trans (by norm_num))
  exact ⟨hmain, hread, hsat, hsat ▸ hbound⟩

theorem embedded_delayed_register_linearity_Ico
    (L : ℝ) (hL : 1 ≤ L) (s j : ℕ) (hsj : s ≤ j) (c : ℕ → E)
    (embed : E → X) (S : X → E) (v : ℕ → X)
    (hc : (∑ i ∈ Finset.Ico s j, ‖c i‖) ≤ (1 / 2 : ℝ))
    (hS : ∀ z : E, ‖z‖ ≤ 1 → S (embed z) = z)
    (hvs : v s = embed 0)
    (hstep : ∀ n, s ≤ n → n < j → v (n + 1) = embed (L • S (v n) +
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n)) :
    (∀ n, s ≤ n → n ≤ j → v n = embed
      (L ^ ((n : ℤ) - (j : ℤ)) • ∑ i ∈ Finset.Ico s n, c i)) ∧
      v j = embed (∑ i ∈ Finset.Ico s j, c i) ∧
      S (v j) = ∑ i ∈ Finset.Ico s j, c i ∧
      ‖S (v j)‖ ≤ (1 / 2 : ℝ) := by
  have hc' : (∑ i ∈ Finset.range (j - s), ‖c (s + i)‖) ≤ (1 / 2 : ℝ) := by
    simpa [Finset.sum_Ico_eq_sum_range, Nat.add_comm] using hc
  have hstep' : ∀ n < j - s,
      v (s + (n + 1)) = embed (L • S (v (s + n)) +
        L ^ ((n : ℤ) + 1 - ((j - s : ℕ) : ℤ)) • c (s + n)) := by
    intro n hn
    have he : (((s + n : ℕ) : ℤ) + 1 - (j : ℤ)) =
        ((n : ℤ) + 1 - ((j - s : ℕ) : ℤ)) := by omega
    simpa only [Nat.add_assoc, he] using hstep (s + n) (by omega) (by omega)
  obtain ⟨hmain, hread, hsat, hbound⟩ := embedded_delayed_register_linearity L hL
    (j - s) (fun n => c (s + n)) embed S (fun n => v (s + n)) hc' hS
    (by simpa using hvs) hstep'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hsn hnj
    have hn : n - s ≤ j - s := by omega
    have he : (((n - s : ℕ) : ℤ) - ((j - s : ℕ) : ℤ)) =
        ((n : ℤ) - (j : ℤ)) := by omega
    have hn' : s + (n - s) = n := Nat.add_sub_of_le hsn
    simpa only [hn', delayedCandidate, he, Finset.sum_Ico_eq_sum_range,
        Nat.add_comm] using hmain (n - s) hn
  · simpa [Nat.add_sub_of_le hsj, Finset.sum_Ico_eq_sum_range, Nat.add_comm] using hread
  · simpa [Nat.add_sub_of_le hsj, Finset.sum_Ico_eq_sum_range, Nat.add_comm] using hsat
  · simpa [Nat.add_sub_of_le hsj] using hbound

theorem embedded_register_readout_of_identified_inputs
    (L : ℝ) (hL : 1 ≤ L) (s j : ℕ) (hsj : s ≤ j)
    (a : ℕ → ℝ) (input c : ℕ → E) (v : ℕ → X)
    (embed : E → X) (S : X → E)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + input n))
    (hgain : ∀ n, s ≤ n → n < j → a n = L)
    (hinput : ∀ n, s ≤ n → n < j → input n =
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico s j) (hcard : I.card ≤ 5)
    (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ))
    (hsupport : ∀ i ∈ Finset.Ico s j, i ∉ I → c i = 0)
    (hS : ∀ z : E, ‖z‖ ≤ 1 → S (embed z) = z) (hvs : v s = embed 0) :
    (∀ n, s ≤ n → n ≤ j → v n = embed
      (L ^ ((n : ℤ) - (j : ℤ)) • ∑ i ∈ Finset.Ico s n, c i)) ∧
      v j = embed (∑ i ∈ I, c i) ∧
      S (v j) = ∑ i ∈ I, c i ∧ ‖S (v j)‖ ≤ (1 / 2 : ℝ) := by
  have hnormsum : (∑ i ∈ I, ‖c i‖) = ∑ i ∈ Finset.Ico s j, ‖c i‖ := by
    apply Finset.sum_subset hI
    intro i hi hnot
    simp [hsupport i hi hnot]
  have hsum : (∑ i ∈ I, c i) = ∑ i ∈ Finset.Ico s j, c i :=
    Finset.sum_subset hI hsupport
  have htotal : (∑ i ∈ Finset.Ico s j, ‖c i‖) ≤ (1 / 2 : ℝ) := by
    rw [← hnormsum]
    exact coefficient_norm_sum_le_half I c hcard hc
  have hstep : ∀ n, s ≤ n → n < j → v (n + 1) =
      embed (L • S (v n) + L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n) := by
    intro n hsn hnj
    rw [hrec n, hgain n hsn hnj, hinput n hsn hnj]
  obtain ⟨hmain, hread, hsat, hbound⟩ := embedded_delayed_register_linearity_Ico L hL
    s j hsj c embed S v htotal hS hvs hstep
  exact ⟨hmain, hread.trans (congrArg embed hsum.symm), hsat.trans hsum.symm, hbound⟩

end Problem340.Register

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem rawMap_register_readout
    (D : SphereData) (hL : 1 ≤ D.L)
    (hgate : ∀ z, 0 ≤ D.gate z) (hχ : ∀ z, D.cutoff z ∈ Set.Icc 0 1)
    (hS : ∀ z : ℂ, ‖z‖ ≤ 1 → D.saturation (z : Sphere) = z)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (ℓ : Fin 3) (s j : ℕ) (hsj : s ≤ j)
    (hstrip : ∀ n, s ≤ n → n < j → t n ∈ Set.Ico 0 100)
    (hgain : ∀ n, s ≤ n → n < j → D.gain (t n) = D.L)
    (hreset : (x s).2.2 ℓ = ((0 : ℂ) : Sphere))
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico s j) (hcard : I.card ≤ 5)
    (hprep : ∀ n ∈ Finset.Ico s j, n ∉ I → preparationCoeff (t n) = 0)
    (hread : readoutCoeff ℓ (t j) ≠ 0)
    (hpredict : ∀ n ∈ I,
      predictedClock D (j - n) (t n) (x n).2.1 = t j) :
    D.saturation ((x j).2.2 ℓ) =
        ∑ n ∈ I, scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) ∧
      ‖D.saturation ((x j).2.2 ℓ)‖ ≤ (1 / 2 : ℝ) ∧
      (x j).2.2 ℓ =
        ((∑ n ∈ I, scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) : ℂ) : Sphere) := by
  classical
  let c : ℕ → ℂ := fun n =>
    if n ∈ I then scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) else 0
  let a : ℕ → ℝ := fun n => periodicGain D (x n).1
  let u : ℕ → ℂ := fun n => input D ℓ (x n).1 (x n).2.1
  let v : ℕ → Sphere := fun n => (x n).2.2 ℓ
  have hrec : ∀ n, v (n + 1) =
      ((a n • D.saturation (v n) + u n : ℂ) : Sphere) := by
    intro n
    simp only [v, a, u, horbit n, rawMap, Complex.real_smul]
  have hagain : ∀ n, s ≤ n → n < j → a n = D.L := by
    intro n hsn hnj
    change AddCircle.liftIco 100 0 D.gain (x n).1 = D.L
    rw [← hlift n, AddCircle.liftIco_zero_coe_apply (hstrip n hsn hnj)]
    exact hgain n hsn hnj
  have hu : ∀ n, s ≤ n → n < j →
      u n = D.L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n := by
    intro n hsn hnj
    by_cases hnI : n ∈ I
    · have hsignal := input_eq_delayed_signal_of_predicted_hit D hgate ℓ
        (t n) (t j) (x n).2.1 (hstrip n hsn hnj) n j hnj (hpredict n hnI) hread
      simpa only [u, hlift n, c, ite_eq_left hnI, add_comm (1 : ℤ) (n : ℤ)] using hsignal
    · have hα := hprep n (Finset.mem_Ico.mpr ⟨hsn, hnj⟩) hnI
      change input D ℓ (x n).1 (x n).2.1 = _
      rw [← hlift n, input_eq_baseInput_of_mem_Ico D ℓ (hstrip n hsn hnj)]
      simp [baseInput, hα, c, hnI]
  have hc : ∀ n ∈ I, ‖c n‖ ≤ (1 / 10 : ℝ) := by
    intro n hn
    simp only [c, ite_eq_left hn]
    exact norm_scheduledSignal_le D ℓ (t n) (t j) (x n).2.1 (j - n) (hχ _)
  have hsupp : ∀ n ∈ Finset.Ico s j, n ∉ I → c n = 0 := by
    intro n _ hn
    simp [c, hn]
  obtain ⟨_, hv, hsat, hnorm⟩ := Register.embedded_register_readout_of_identified_inputs
    D.L hL s j hsj a u c v (fun z : ℂ => (z : Sphere)) D.saturation
    hrec hagain hu I hI hcard hc hsupp hS hreset
  have hsum : (∑ n ∈ I, c n) =
      ∑ n ∈ I, scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [c, hn]
  exact ⟨hsat.trans hsum, hnorm, hv.trans (congrArg (fun z : ℂ => (z : Sphere)) hsum)⟩

theorem rawMap_register_readout_of_gain_profile
    (D : SphereData) (hL : 1 ≤ D.L)
    (hgate : ∀ z, 0 ≤ D.gate z) (hχ : ∀ z, D.cutoff z ∈ Set.Icc 0 1)
    (hS : ∀ z : ℂ, ‖z‖ ≤ 1 → D.saturation (z : Sphere) = z)
    (hgain : ∀ r ∈ Set.Icc 7 90, D.gain r = D.L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (ℓ : Fin 3) (s j : ℕ) (hsj : s ≤ j) (hs : 7 ≤ t s)
    (hreset : (x s).2.2 ℓ = ((0 : ℂ) : Sphere))
    (hread : readoutCoeff ℓ (t j) ≠ 0) :
    D.saturation ((x j).2.2 ℓ) =
        ∑ n ∈ passagePreparationIndices t s j,
          scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) ∧
      ‖D.saturation ((x j).2.2 ℓ)‖ ≤ (1 / 2 : ℝ) ∧
      (x j).2.2 ℓ =
        ((∑ n ∈ passagePreparationIndices t s j,
          scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) : ℂ) : Sphere) := by
  classical
  let I := passagePreparationIndices t s j
  have ht : Monotone t := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hclock n]
    exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate _))
  have hjmem : t j ∈ readoutInterval ℓ := by
    rwa [← readoutCoeff_support, Function.mem_support]
  have hjbounds := readoutInterval_subset ℓ hjmem
  have hstrip : ∀ n, s ≤ n → n < j → t n ∈ Set.Ico 0 100 := by
    intro n hsn hnj
    have hlow := hs.trans (ht hsn)
    have hupp := ht hnj.le
    exact ⟨by linarith, by linarith [hjbounds.2]⟩
  have hgain' : ∀ n, s ≤ n → n < j → D.gain (t n) = D.L := by
    intro n hsn hnj
    apply hgain
    exact ⟨hs.trans (ht hsn), by have hupp := ht hnj.le; linarith [hjbounds.2]⟩
  have hI : I ⊆ Finset.Ico s j := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hcard : I.card ≤ 5 := by
    apply clock_preparation_card_le_five ht
    · intro n hn8 hn12
      rw [hclock n]
      have hb : Clock.barrier (t n) = 1 := by
        apply Clock.barrier_plateau (by linarith) (by linarith)
        rw [abs_of_nonpos (by linarith)]
        linarith
      rw [Clock.increment_eq_one_of_barrier_eq_one hb]
    · intro n hn
      have hn' := (Finset.mem_filter.mp hn).2
      change t n ∈ Set.Ioo 8 12
      rwa [← preparationCoeff_support, Function.mem_support]
  have hprep : ∀ n ∈ Finset.Ico s j, n ∉ I → preparationCoeff (t n) = 0 := by
    intro n hn hnot
    by_contra hα
    exact hnot (Finset.mem_filter.mpr ⟨hn, hα⟩)
  have hpredict : ∀ n ∈ I, predictedClock D (j - n) (t n) (x n).2.1 = t j := by
    intro n hn
    obtain ⟨hsn, hnj⟩ := Finset.mem_Ico.mp (hI hn)
    exact rawMap_predictedClock_at_readout D x horbit t ht hlift hclock ℓ n j hnj.le
      (hstrip n hsn hnj).1 hread
  exact rawMap_register_readout D hL hgate hχ hS x horbit t hlift ℓ s j hsj hstrip
    hgain' hreset I hI hcard hprep hread hpredict

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapRecoveredReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem scheduledSignal_eq_passageWeight
    (D : SphereData) (l : Fin 3) (t : ℕ → ℝ) (z : ℕ → ℂ) (i j : ℕ) :
    scheduledSignal D l (t i) (t j) (z i : Sphere) (j - i) =
      ((readoutCoeff l (t j) / 10 : ℝ) : ℂ) *
        ((passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (j - i + 1))) := by
  simp only [scheduledSignal, passageWeight, phase_coe, PassagePhase.phase,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem sum_scheduledSignal_eq_passageWeight
    (D : SphereData) (l : Fin 3) (x : ℕ → RawManifold)
    (t : ℕ → ℝ) (z : ℕ → ℂ) (I : Finset ℕ) (j : ℕ)
    (hz : ∀ i ∈ I, (z i : Sphere) = (x i).2.1) :
    (∑ i ∈ I, scheduledSignal D l (t i) (t j) (x i).2.1 (j - i)) =
      ((readoutCoeff l (t j) / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (j - i + 1)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hz i hi]
  exact scheduledSignal_eq_passageWeight D l t z i j

theorem orbitReadoutCoeff_eq_of_mem_Ico
    (x : ℕ → RawManifold) (t : ℕ → ℝ) (j : ℕ) (l : Fin 3)
    (hlift : (t j : AddCircle (100 : ℝ)) = (x j).1)
    (hj : t j ∈ Set.Ico 0 100) :
    orbitReadoutCoeff x j l = readoutCoeff l (t j) := by
  change AddCircle.liftIco 100 0 (readoutCoeff l) (x j).1 = _
  rw [← hlift, AddCircle.liftIco_zero_coe_apply hj]

theorem rawMap_recovered_readout_of_gain_profile
    (D : SphereData) (hL : 1 ≤ D.L)
    (hgate : ∀ u, 0 ≤ D.gate u) (hχ : ∀ u, D.cutoff u ∈ Set.Icc 0 1)
    (hS : ∀ u : ℂ, ‖u‖ ≤ 1 → D.saturation (u : Sphere) = u)
    (hgain : ∀ r ∈ Set.Icc 7 90, D.gain r = D.L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (z : ℕ → ℂ) (I : Finset ℕ) (l : Fin 3) (s j : ℕ)
    (hsj : s ≤ j) (hs : 7 ≤ t s)
    (hreset : (x s).2.2 l = ((0 : ℂ) : Sphere))
    (hI : passagePreparationIndices t s j = I)
    (hz : ∀ i ∈ I, (z i : Sphere) = (x i).2.1)
    (hj : t j ∈ Set.Ico 0 100)
    (hread : orbitReadoutCoeff x j l ≠ 0) :
    orbitSaturatedRegister D x j l = ((orbitReadoutCoeff x j l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (passageWeight D t z i : ℂ) *
        PassagePhase.phase (z i) ^ (2 ^ (j - i + 1)) := by
  have hcoeff := orbitReadoutCoeff_eq_of_mem_Ico x t j l (hlift j) hj
  have hread' : readoutCoeff l (t j) ≠ 0 := by rwa [hcoeff] at hread
  have h := (rawMap_register_readout_of_gain_profile D hL hgate hχ hS hgain
    x horbit t hlift hclock l s j hsj hs hreset hread').1
  rw [hI] at h
  change D.saturation ((x j).2.2 l) = _
  rw [h, hcoeff]
  exact sum_scheduledSignal_eq_passageWeight D l x t z I j hz

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapLocalEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_5_rad4b56_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
theorem concrete_unbounded_clock_local_escape
    (L : ℝ) (hL : 2 < L) (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀)))
    (z : ℕ → ℂ)
    (hz : ∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1)
    (k : ℤ) (hk : t₀ < 100 * (k : ℝ)) :
    ∃ s hi : ℕ, 100 * (k : ℝ) ≤ rawClockLift (concreteData L hL) x t₀ s ∧
      rawClockLift (concreteData L hL) x t₀ s < 100 * (k : ℝ) + 74 ∧
      100 * (k : ℝ) + 80 ≤ rawClockLift (concreteData L hL) x t₀ hi ∧
      (∀ n, s ≤ n → n < hi → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖) ∧
      ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < ‖z j‖ := by
  classical
  let D := concreteData L hL
  let y : ℕ → RawManifold := fun n => (concreteMap L hL)^[n] x
  let t : ℕ → ℝ := rawClockLift D x t₀
  let u : ℕ → ℝ := fun n => t n - 100 * (k : ℝ)
  have hy : ∀ n, y (n + 1) = concreteMap L hL (y n) := by
    intro n
    exact Function.iterate_succ_apply' (concreteMap L hL) n x
  have hmono : Monotone u := by
    intro a b hab
    exact sub_le_sub_right (monotone_rawClockLift D
      (concrete_gate_mem_Icc L hL) x t₀ hab) _
  have hlift : ∀ n, (u n : AddCircle (100 : ℝ)) = (y n).1 :=
    coe_rawClockLift_sub_period D x t₀ h₀ k
  have hclock : ∀ n, u (n + 1) = u n + Clock.increment (u n) (D.gate (y n).2.1) :=
    rawClockLift_sub_period_succ D x t₀ h₀ k
  have hscheduled := rawOrbit_hasScheduledPassageAt D
    (concrete_gate_mem_Icc L hL) x t₀ h₀ hunbounded k hk
  rcases hscheduled with
    ⟨lo, hi, hlohi, hlo, hhi, hinside, hne, hcard, hprep,
      ⟨r, hr, hr0, hr1, hrbefore⟩, ⟨j, hj, hj0, hj1, l, hl⟩⟩
  let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (u i))
  change I.Nonempty at hne
  have hinside' : ∀ n, lo ≤ n → n < hi → u n ∈ Set.Ico (0 : ℝ) 100 := hinside
  obtain ⟨s, K, hsI, hlos, hsK, hKhi, hIK, hearly, hus⟩ :=
    complete_passage_phase_window y u hmono hlift lo hi hinside' hne
  have hsI' : s ∈ I := hsI
  have hshi : s < hi := hsK.trans_le hKhi
  have hreset : ∀ l : Fin 3, (y s).2.2 l = ((0 : ℂ) : Sphere) := by
    apply complete_passage_register_reset_at_first_preparation L hL y hy u hlift
      lo hi r s (Finset.mem_Ico.mp hr).1 (hrbefore s hsI') hshi
      (show u r ∈ Set.Icc 2 5 from ⟨hr0, by linarith⟩) hinside'
    intro i hiI
    exact (hIK i hiI).1
  have hhalf : ∀ i ∈ I, (1 / 2 : ℝ) < ‖z i‖ := by
    intro i hiI
    have hiprep : preparationCoeff (u i) ≠ 0 := ne_of_gt (Finset.mem_filter.mp hiI).2
    have hisupport : u i ∈ Set.Ioo 8 12 := by
      rwa [← preparationCoeff_support, Function.mem_support]
    apply concrete_preparation_radius L hL x t₀ h₀ hunbounded z hz i k
    simpa only [u, t, mul_comm (100 : ℝ) (k : ℝ)] using hisupport
  have hzs : z s ≠ 0 := by
    intro hzero
    have hh := hhalf s hsI'
    rw [hzero, norm_zero] at hh
    norm_num at hh
  have hregister : ∀ n, s ≤ n → n < hi → ∀ l : Fin 3,
      orbitReadoutCoeff y n l ≠ 0 →
      orbitSaturatedRegister D y n l = ((orbitReadoutCoeff y n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D u z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)) := by
    intro n hsn hnhi l hnread
    have hnstrip := hinside' n (hlos.trans hsn) hnhi
    have hcoeff := orbitReadoutCoeff_eq_of_clock_lift y u hlift n hnstrip l
    have hread : readoutCoeff l (u n) ≠ 0 := by rwa [hcoeff] at hnread
    have hset : passagePreparationIndices u s n = I := by
      ext i
      constructor
      · intro hiI
        obtain ⟨hist, hip⟩ := Finset.mem_filter.mp hiI
        obtain ⟨hsi, hin⟩ := Finset.mem_Ico.mp hist
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
          ⟨hlos.trans hsi, hin.trans hnhi⟩,
          lt_of_le_of_ne (preparationCoeff_nonneg _) (Ne.symm hip)⟩
      · intro hiI
        have hip : preparationCoeff (u i) ≠ 0 := ne_of_gt (Finset.mem_filter.mp hiI).2
        have hin := preparation_before_readout hmono hip hread
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨(hIK i hiI).1, hin⟩, hip⟩
    apply rawMap_recovered_readout_of_gain_profile D (by change 1 ≤ L; linarith)
      (fun w => (concrete_gate_mem_Icc L hL w).1) (concrete_cutoff_mem_Icc L hL)
      ?_ ?_ y hy u hlift hclock z I l s n hsn (by linarith [hus.1])
      (hreset l) hset (fun i _ => hz i) hnstrip hnread
    · intro w hw
      exact saturation_eq_self (3 * L) (by linarith) hw
    · intro a ha
      exact gainProfile_eq_gain L ha
  have hz' : ∀ n, s ≤ n → n ≤ hi → (z n : Sphere) = (y n).2.1 :=
    fun n _ _ => hz n
  have hstep : ∀ n, s ≤ n → n < hi → y (n + 1) = concreteMap L hL (y n) :=
    fun n _ _ => hy n
  have hread : ∃ n, s ≤ n ∧ n < hi ∧ ∃ l : Fin 3, orbitReadoutCoeff y n l = 1 := by
    have hjstrip := hinside' j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
    have hcoeff := orbitReadoutCoeff_eq_of_clock_lift y u hlift j hjstrip l
    have hprepS : preparationCoeff (u s) ≠ 0 := ne_of_gt (Finset.mem_filter.mp hsI').2
    have hsltj := preparation_before_readout hmono hprepS
      (show readoutCoeff l (u j) ≠ 0 by rw [hl]; norm_num)
    exact ⟨j, hsltj.le, (Finset.mem_Ico.mp hj).2, l, hcoeff.trans hl⟩
  have hsquare := concreteMap_passage_square_le L hL y u z I s K hi
    hzs hz' hIK hearly hregister hstep
  have hlarge := concreteMap_passage_escape L hL y u z I s K hi
    hzs hz' hIK hearly hregister hstep hKhi hhalf hprep hread
  refine ⟨s, hi, ?_, ?_, ?_, hsquare, hlarge⟩
  · change 100 * (k : ℝ) ≤ t s
    have hu := hus.1
    change 8 < t s - 100 * (k : ℝ) at hu
    linarith
  · change t s < 100 * (k : ℝ) + 74
    have hu := hus.2
    change t s - 100 * (k : ℝ) < 12 at hu
    linarith
  · change 100 * (k : ℝ) + 80 ≤ t hi
    have hu := hhi.1
    change 100 ≤ t hi - 100 * (k : ℝ) at hu
    linarith

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapOrbitAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology OnePoint

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_6_rad4b56_1 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
theorem concrete_orbit_alternatives_of_complete_passages
    (L : ℝ) (hL : 2 < L)
    (hlocal : ∀ (x : RawManifold) (t₀ : ℝ),
      (t₀ : AddCircle (100 : ℝ)) = x.1 →
      ¬ BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀)) →
      ∀ z : ℕ → ℂ,
      (∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1) →
      CompletePassageEstimates (concreteData L hL) x t₀ z)
    (x : RawManifold) :
    (Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
        (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
      Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 ((0 : ℂ) : Sphere))) ∨
    (Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 (∞ : Sphere)) ∧
      ∀ i : Fin 3, ∀ᶠ n in atTop,
        ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere)) := by
  rcases x with ⟨t, z₀, v⟩
  by_cases hinfty : z₀ = ∞
  · subst z₀
    right
    have hterminal := ConcreteErasure.concreteMap_infty_eventually_zero L hL t v
    refine ⟨?_, fun i => hterminal.mono (fun n hn => hn.2 i)⟩
    apply tendsto_const_nhds.congr
    intro n
    exact (ConstructionInfinityAttraction.raw_iterate_main_infty
      (concreteData L hL) (t, ∞, v) rfl n).symm
  · obtain ⟨t₀, ht₀⟩ := QuotientAddGroup.mk_surjective t
    by_cases hbounded : BddAbove
        (Set.range (rawClockLift (concreteData L hL) (t, z₀, v) t₀))
    · exact Or.inl (concrete_bounded_clock_limits L hL (t, z₀, v) t₀ ht₀ hbounded)
    · obtain ⟨z, hz, _⟩ := exists_finiteMainOrbit (concreteData L hL) (t, z₀, v) hinfty
      have hescape := rawOrbit_norm_tendsto_atTop_of_complete_passages
        (concreteData L hL) (concrete_gate_mem_Icc L hL) (t, z₀, v) t₀ ht₀ z hz
        (hlocal (t, z₀, v) t₀ ht₀ hbounded z hz)
      refine Or.inr ⟨rawOrbit_main_tendsto_infty_of_norm
        (concreteData L hL) (t, z₀, v) z hz hescape, ?_⟩
      intro i
      exact (ConcreteErasure.concreteMap_registers_eventually_zero_of_escape
        L hL (t, z₀, v) z hz hescape).mono (fun n hn => hn i)

theorem concrete_orbit_alternatives (L : ℝ) (hL : 2 < L) (x : RawManifold) :
    (Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
        (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
      Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 ((0 : ℂ) : Sphere))) ∨
    (Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 (∞ : Sphere)) ∧
      ∀ i : Fin 3, ∀ᶠ n in atTop,
        ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere)) := by
  apply concrete_orbit_alternatives_of_complete_passages L hL _ x
  intro y t₀ h₀ hunbounded z hz k hk
  exact concrete_unbounded_clock_local_escape L hL y t₀ h₀ hunbounded z hz k hk

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapEntropyComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem coverEntropy_realizedMap_eq_zero_oai (L : ℝ) (hL : 2 < L) :
    Dynamics.coverEntropy (realizedMap L hL)
      (Set.univ : Set (CounterexampleManifold 3)) = (0 : EReal) :=
  coverEntropy_realizedMap_eq_zero_of_orbit_alternatives L hL
    (concrete_orbit_alternatives L hL)

end Problem340.Construction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem340.MapMainRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Topology ContDiff

namespace Problem340.Construction

local instance instFactLtRealOfNat_solutions_3 : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

end Problem340.Construction

end

end OAI
end

theorem solution : type_of% @OAI.Problem340.Construction.coverEntropy_realizedMap_eq_zero_oai := @OAI.Problem340.Construction.coverEntropy_realizedMap_eq_zero_oai
