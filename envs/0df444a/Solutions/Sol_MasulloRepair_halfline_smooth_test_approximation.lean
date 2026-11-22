-- Prove2me | solution 1 for MasulloRepair.halfline_smooth_test_approximation
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T15:05:16.722801+00:00
-- url     : https://prove2.me/submissions/2f1c5935-864c-4c68-a561-dab83e688b1e

import Definitions.Def_MasulloRepair_LogWindows
import Theorems.Thm_MasulloRepair_simultaneous_smooth_L2_approximation
import Theorems.Thm_MasulloRepair_log_window_measure_transport
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal ContDiff

private lemma log_window_regular (a s : ℝ) :
    (∀ n, Continuous (logWindowWeight a s n)) ∧
    (∀ n x, 0 < logWindowWeight a s n x) ∧
    (∀ n, IsLocallyFiniteMeasure (logWindowMeasure a s n)) ∧
    Monotone (logWindowMeasure a s) := by
  have hc (n : ℕ) : Continuous (logWindowWeight a s n) := by
    unfold logWindowWeight
    apply Continuous.mul (by fun_prop)
    exact (by fun_prop : Continuous (fun x : ℝ => 1+x^2)).rpow_const
      (fun x => Or.inl (by positivity))
  refine ⟨hc, ?_, fun n => IsLocallyFiniteMeasure.withDensity_ofReal (hc n), ?_⟩
  · intro n x
    unfold logWindowWeight
    positivity
  · intro n m hnm
    apply withDensity_mono
    apply Eventually.of_forall
    intro x
    apply ENNReal.ofReal_le_ofReal
    unfold logWindowWeight
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    by_cases hx : 0 ≤ x
    · apply max_le_max_left
      apply Real.exp_le_exp.mpr
      have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact mul_le_mul_of_nonneg_right (by linarith) hx
    · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      have hleft (k : ℕ) : Real.exp (2*(a+(k : ℝ))*x) ≤ Real.exp (2*a*x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by
          have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith) hx')
      rw [max_eq_left (hleft n), max_eq_left (hleft m)]


private lemma positive_log_test (g : ℝ → ℂ) (hg : HasCompactSupport g) (hd : ContDiff ℝ ∞ g) :
    HasCompactSupport (positiveLogLift g) ∧
    tsupport (positiveLogLift g) ⊆ Ioi (0 : ℝ) ∧
    ContDiff ℝ ∞ (positiveLogLift g) ∧
    (∀ x : ℝ, positiveLogLift g (Real.exp x) = g x) := by
  have hK : IsCompact (Real.exp '' tsupport g) := hg.image Real.continuous_exp
  have hs : Function.support (positiveLogLift g) ⊆ Real.exp '' tsupport g := by
    intro t ht
    have ht0 : 0 < t := by
      by_contra h
      exact ht (by simp [positiveLogLift, h])
    refine ⟨Real.log t, ?_, Real.exp_log ht0⟩
    apply subset_tsupport g
    simpa [Function.mem_support, positiveLogLift, ht0] using ht
  have hts : tsupport (positiveLogLift g) ⊆ Real.exp '' tsupport g :=
    closure_minimal hs hK.isClosed
  have hpos : tsupport (positiveLogLift g) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    rcases hts ht with ⟨x, hx, rfl⟩
    exact Real.exp_pos x
  refine ⟨hK.of_isClosed_subset isClosed_closure hts, hpos, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : 0 < t
    · have heq : positiveLogLift g =ᶠ[𝓝 t] (fun y => g (Real.log y)) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with y hy
        simp [positiveLogLift, show 0 < y from hy]
      exact ((hd.contDiffAt).comp t (Real.contDiffAt_log.mpr ht.ne')).congr_of_eventuallyEq heq
    · have heq : positiveLogLift g =ᶠ[𝓝 t] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => ht (hpos h))
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · intro x
    simp [positiveLogLift, Real.exp_pos]


theorem solution (a s : ℝ) (f : ℝ → ℂ)
    (hf : ∀ n : ℕ, MemLp f 2 (windowMeasure (halflineBaseMeasure a s) n)) :
    ∃ g : ℕ → ℝ → ℂ,
      (∀ k, HasCompactSupport (g k) ∧
        tsupport (g k) ⊆ Ioi (0 : ℝ) ∧ ContDiff ℝ ∞ (g k)) ∧
      (∀ n k, MemLp (g k) 2 (windowMeasure (halflineBaseMeasure a s) n)) ∧
      ∀ n, Tendsto (fun k => eLpNorm (f - g k) 2
        (windowMeasure (halflineBaseMeasure a s) n)) atTop (𝓝 0) := by
  have hr := log_window_regular a s
  letI : ∀ n, IsLocallyFiniteMeasure (logWindowMeasure a s n) := hr.2.2.1
  letI : ∀ n, IsFiniteMeasureOnCompacts (logWindowMeasure a s n) := fun n => by
    infer_instance
  have hlog (n : ℕ) : MemLp (fun x => f (Real.exp x)) 2 (logWindowMeasure a s n) :=
    ((MasulloRepair.log_window_measure_transport a s n).2 f).1.mp (hf n)
  obtain ⟨h, hs, hm, ht⟩ := MasulloRepair.simultaneous_smooth_L2_approximation
    (logWindowMeasure a s) hr.2.2.2 (fun x => f (Real.exp x)) hlog
  refine ⟨fun k => positiveLogLift (h k), ?_, ?_, ?_⟩
  · intro k
    have hk := positive_log_test (h k) (hs k).1 (hs k).2
    exact ⟨hk.1, hk.2.1, hk.2.2.1⟩
  · intro n k
    apply ((MasulloRepair.log_window_measure_transport a s n).2 _).1.mpr
    simpa only [positiveLogLift, Real.exp_pos, if_pos, Real.log_exp] using hm n k
  · intro n
    have heq (k : ℕ) :
        eLpNorm (f - positiveLogLift (h k)) 2 (windowMeasure (halflineBaseMeasure a s) n) =
          eLpNorm ((fun x => f (Real.exp x)) - h k) 2 (logWindowMeasure a s n) := by
      simpa only [Pi.sub_def, positiveLogLift, Real.exp_pos, if_pos, Real.log_exp] using
        ((MasulloRepair.log_window_measure_transport a s n).2
          (f - positiveLogLift (h k))).2
    simpa only [heq] using ht n

#print axioms solution
