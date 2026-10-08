-- Prove2me | solution 1 for Helfgott.variable_radius_minor_arc_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T08:57:26.499759+00:00
-- url     : https://prove2.me/submissions/ee64849d-23cd-4554-8675-c3b9800cc39c

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Definitions.Def_Helfgott_ArcCounting

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Finset
open scoped BigOperators Classical

namespace Helfgott

theorem weighted_sum_by_parts (f g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range (N+1), f n*g n) =
      (∑ n ∈ range (N+1), f n)*g N +
        ∑ n ∈ range N, (∑ k ∈ range (n+1), f k)*(g n-g (n+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun n => f n*g n) (N+1), ih,
      sum_range_succ f (N+1),
      sum_range_succ (fun n => (∑ k ∈ range (n+1), f k)*(g n-g (n+1))) N]
    ring

theorem weighted_majorant_by_parts (F g : ℕ → ℝ) (N : ℕ) :
    F N*g N + ∑ n ∈ range N, F n*(g n-g (n+1)) =
      F 0*g 0 + ∑ n ∈ range N, g (n+1)*(F (n+1)-F n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ]
    calc
      _ = (F N*g N+∑ n ∈ range N, F n*(g n-g (n+1))) +
          g (N+1)*(F (N+1)-F N) := by ring
      _ = _ := by rw [ih]; ring

theorem weighted_cumulative_bound (f g F : ℕ → ℝ) (N : ℕ)
    (hF : ∀ n ≤ N, (∑ k ∈ range (n+1), f k) ≤ F n)
    (hg : 0 ≤ g N) (hmono : ∀ n < N, g (n+1) ≤ g n) :
    (∑ n ∈ range (N+1), f n*g n) ≤
      F 0*g 0 + ∑ n ∈ range N, g (n+1)*(F (n+1)-F n) := by
  rw [weighted_sum_by_parts, ← weighted_majorant_by_parts]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (hF N le_rfl) hg
  · apply sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (hF n (Nat.le_of_lt (mem_range.mp hn)))
      (sub_nonneg.mpr (hmono n (mem_range.mp hn)))


theorem weighted_majorant_increments_integral_bound (g F D : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hg : AntitoneOn g (Set.Icc a (a+N)))
    (hD : ∀ u ∈ Set.Icc a (a+N), 0 ≤ D u)
    (hderiv : ∀ u ∈ Set.Icc a (a+N), HasDerivAt F (D u) u)
    (hiD : IntervalIntegrable D volume a (a+N))
    (higD : IntervalIntegrable (fun u => g u*D u) volume a (a+N)) :
    (∑ n ∈ range N, g (a+(n+1 : ℕ))*(F (a+(n+1 : ℕ))-F (a+n))) ≤
      ∫ u in a..(a+N), g u*D u := by
  have hab : a ≤ a+(N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hnodes (n : ℕ) (hn : n ≤ N) : a+(n : ℝ) ∈ Set.Icc a (a+N) := by
    constructor
    · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · exact add_le_add le_rfl (show (n : ℝ) ≤ N by exact_mod_cast hn)
  calc
    _ ≤ ∑ n ∈ range N, ∫ u in (a+n)..(a+(n+1 : ℕ)), g u*D u := by
      apply sum_le_sum
      intro n hn
      have hnN : n+1 ≤ N := mem_range.mp hn
      have hnle : a+(n : ℝ) ≤ a+((n+1 : ℕ) : ℝ) := by norm_num
      have hsub : Set.uIcc (a+(n : ℝ)) (a+((n+1 : ℕ) : ℝ)) ⊆ Set.Icc a (a+N) := by
        rw [Set.uIcc_of_le hnle]
        exact Set.Icc_subset_Icc (hnodes n (Nat.le_of_lt hnN)).1 (hnodes (n+1) hnN).2
      have hiDn := hiD.mono_set (by simpa only [Set.uIcc_of_le hab] using hsub)
      have higDn := higD.mono_set (by simpa only [Set.uIcc_of_le hab] using hsub)
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => hderiv u (hsub hu)) hiDn
      rw [← he, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hnle (hiDn.const_mul _) higDn
      intro u hu
      have hum := hsub (by simpa only [Set.uIcc_of_le hnle] using hu)
      exact mul_le_mul_of_nonneg_right
        (hg hum (hnodes (n+1) hnN) hu.2) (hD u hum)
    _ = _ := intervalIntegral.sum_integral_adjacent_intervals (a := fun n => a+(n : ℝ))
      (fun n hn => higD.mono_set (by
        have hnle : a+(n : ℝ) ≤ a+((n+1 : ℕ) : ℝ) := by norm_num
        rw [Set.uIcc_of_le hnle, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc (hnodes n (Nat.le_of_lt hn)).1 (hnodes (n+1) hn).2))
    _ = _ := by simp

theorem weighted_cumulative_integral_bound (f : ℕ → ℝ) (g F D : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hF : ∀ n ≤ N, (∑ k ∈ range (n+1), f k) ≤ F (a+n))
    (hg : AntitoneOn g (Set.Icc a (a+N))) (hgN : 0 ≤ g (a+N))
    (hD : ∀ u ∈ Set.Icc a (a+N), 0 ≤ D u)
    (hderiv : ∀ u ∈ Set.Icc a (a+N), HasDerivAt F (D u) u)
    (hiD : IntervalIntegrable D volume a (a+N))
    (higD : IntervalIntegrable (fun u => g u*D u) volume a (a+N)) :
    (∑ n ∈ range (N+1), f n*g (a+n)) ≤
      F a*g a + ∫ u in a..(a+N), g u*D u := by
  have hab : a ≤ a+(N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hnodes (n : ℕ) (hn : n ≤ N) : a+(n : ℝ) ∈ Set.Icc a (a+N) := by
    constructor
    · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · exact add_le_add le_rfl (show (n : ℝ) ≤ N by exact_mod_cast hn)
  have hb := weighted_cumulative_bound f (fun n => g (a+n)) (fun n => F (a+n)) N hF hgN
    (fun n hn => hg (hnodes n (Nat.le_of_lt hn)) (hnodes (n+1) hn)
      (by norm_num))
  simp only [Nat.cast_zero,add_zero] at hb
  apply hb.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ n ∈ range N, ∫ u in (a+n)..(a+(n+1 : ℕ)), g u*D u := by
      apply sum_le_sum
      intro n hn
      have hnN : n+1 ≤ N := mem_range.mp hn
      have hnle : a+(n : ℝ) ≤ a+((n+1 : ℕ) : ℝ) := by norm_num
      have hsub : Set.uIcc (a+(n : ℝ)) (a+((n+1 : ℕ) : ℝ)) ⊆ Set.Icc a (a+N) := by
        rw [Set.uIcc_of_le hnle]
        exact Set.Icc_subset_Icc (hnodes n (Nat.le_of_lt hnN)).1 (hnodes (n+1) hnN).2
      have hiDn := hiD.mono_set (by simpa only [Set.uIcc_of_le hab] using hsub)
      have higDn := higD.mono_set (by simpa only [Set.uIcc_of_le hab] using hsub)
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u hu => hderiv u (hsub hu)) hiDn
      rw [← he, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hnle (hiDn.const_mul _) higDn
      intro u hu
      have hum := hsub (by simpa only [Set.uIcc_of_le hnle] using hu)
      exact mul_le_mul_of_nonneg_right
        (hg hum (hnodes (n+1) hnN) hu.2) (hD u hum)
    _ = _ := intervalIntegral.sum_integral_adjacent_intervals (a := fun n => a+(n : ℝ))
      (fun n hn => higD.mono_set (by
        have hnle : a+(n : ℝ) ≤ a+((n+1 : ℕ) : ℝ) := by norm_num
        rw [Set.uIcc_of_le hnle, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc (hnodes n (Nat.le_of_lt hn)).1 (hnodes (n+1) hn).2))
    _ = _ := by simp

theorem weighted_majorant_increments_integral_bound_right (g F D : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hg : AntitoneOn g (Set.Icc a (a+N)))
    (hD : ∀ u ∈ Set.Icc a (a+N), 0 ≤ D u)
    (hcont : ContinuousOn F (Set.Icc a (a+N)))
    (hderiv : ∀ u ∈ Set.Ioo a (a+N), HasDerivWithinAt F (D u) (Set.Ioi u) u)
    (hiD : IntervalIntegrable D volume a (a+N))
    (higD : IntervalIntegrable (fun u => g u*D u) volume a (a+N)) :
    (∑ n ∈ range N, g (a+(n+1 : ℕ))*(F (a+(n+1 : ℕ))-F (a+n))) ≤
      ∫ u in a..(a+N), g u*D u := by
  have hab : a ≤ a+(N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hnodes (n : ℕ) (hn : n ≤ N) : a+(n : ℝ) ∈ Set.Icc a (a+N) := by
    constructor
    · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · exact add_le_add le_rfl (show (n : ℝ) ≤ N by exact_mod_cast hn)
  calc
    _ ≤ ∑ n ∈ range N, ∫ u in (a+n)..(a+(n+1 : ℕ)), g u*D u := by
      apply sum_le_sum
      intro n hn
      have hnN : n+1 ≤ N := mem_range.mp hn
      have hnle : a+(n : ℝ) ≤ a+((n+1 : ℕ) : ℝ) := by norm_num
      have hsub : Set.uIcc (a+(n : ℝ)) (a+((n+1 : ℕ) : ℝ)) ⊆ Set.Icc a (a+N) := by
        rw [Set.uIcc_of_le hnle]
        exact Set.Icc_subset_Icc (hnodes n (Nat.le_of_lt hnN)).1 (hnodes (n+1) hnN).2
      have hiDn := hiD.mono_set (by simpa only [Set.uIcc_of_le hab] using hsub)
      have higDn := higD.mono_set (by simpa only [Set.uIcc_of_le hab] using hsub)
      have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hnle
        (hcont.mono (by simpa only [Set.uIcc_of_le hnle] using hsub))
        (fun u hu => hderiv u ⟨lt_of_le_of_lt (hnodes n (Nat.le_of_lt hnN)).1 hu.1,
          lt_of_lt_of_le hu.2 (hnodes (n+1) hnN).2⟩) hiDn
      rw [← he, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hnle (hiDn.const_mul _) higDn
      intro u hu
      have hum := hsub (by simpa only [Set.uIcc_of_le hnle] using hu)
      exact mul_le_mul_of_nonneg_right
        (hg hum (hnodes (n+1) hnN) hu.2) (hD u hum)
    _ = _ := intervalIntegral.sum_integral_adjacent_intervals (a := fun n => a+(n : ℝ))
      (fun n hn => higD.mono_set (by
        have hnle : a+(n : ℝ) ≤ a+((n+1 : ℕ) : ℝ) := by norm_num
        rw [Set.uIcc_of_le hnle, Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc (hnodes n (Nat.le_of_lt hn)).1 (hnodes (n+1) hn).2))
    _ = _ := by simp

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Finset
open scoped BigOperators Classical

namespace Helfgott

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

lemma nested_shell_integrals (M : ℕ → Set Ω) (hM : Monotone M)
    (hmeas : ∀ n, MeasurableSet (M n)) (f : Ω → ℝ) (hf : Integrable f μ) (N : ℕ) :
    (∑ n ∈ range N, ∫ ω in M (n+1) \ M n, f ω ∂μ) =
      (∫ ω in M N, f ω ∂μ) - (∫ ω in M 0, f ω ∂μ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, setIntegral_sdiff (hmeas N) hf.integrableOn (hM (by omega))]
    ring

lemma nested_complement_integrals (M : ℕ → Set Ω) (hM : Monotone M)
    (hmeas : ∀ n, MeasurableSet (M n)) (f : Ω → ℝ) (hf : Integrable f μ) (N : ℕ) :
    (∫ ω in (M 0)ᶜ, f ω ∂μ) =
      (∑ n ∈ range N, ∫ ω in M (n+1) \ M n, f ω ∂μ) +
        (∫ ω in (M N)ᶜ, f ω ∂μ) := by
  rw [nested_shell_integrals μ M hM hmeas f hf]
  linarith [integral_add_compl (hmeas 0) hf, integral_add_compl (hmeas N) hf]

theorem nested_minor_weighted_discrete_bound (M : ℕ → Set Ω) (hM : Monotone M)
    (hmeas : ∀ n, MeasurableSet (M n)) (f v : Ω → ℝ)
    (hf : Integrable f μ) (hfv : Integrable (fun ω => f ω*v ω) μ)
    (hfpos : ∀ ω, 0 ≤ f ω) (g H : ℕ → ℝ) (N : ℕ)
    (hg : ∀ n < N, g (n+1) ≤ g n) (hgN : 0 ≤ g N)
    (hv : ∀ n ≤ N, ∀ ω ∈ (M n)ᶜ, v ω ≤ g n)
    (hH : ∀ n < N, (∫ ω in M (n+1), f ω ∂μ) ≤ H n)
    (hHN : H N = ∫ ω, f ω ∂μ) :
    (∫ ω in (M 0)ᶜ, f ω*v ω ∂μ) ≤
      g 0*(H 0-(∫ ω in M 0, f ω ∂μ)) +
        ∑ n ∈ range N, g (n+1)*(H (n+1)-H n) := by
  classical
  let I₀ : ℝ := ∫ ω in M 0, f ω ∂μ
  let F (n : ℕ) : ℝ := if n < N then
    ∫ ω in M (n+1) \ M n, f ω ∂μ else ∫ ω in (M N)ᶜ, f ω ∂μ
  have hprefix (n : ℕ) (hn : n ≤ N) :
      (∑ k ∈ range (n+1), F k) ≤ H n-I₀ := by
    by_cases he : n = N
    · subst n
      rw [sum_range_succ]
      have hh : (∑ k ∈ range N, F k) =
          ∑ k ∈ range N, ∫ ω in M (k+1) \ M k, f ω ∂μ := by
        apply sum_congr rfl
        intro k hk
        exact if_pos (mem_range.mp hk)
      rw [hh]
      have heF : F N = ∫ ω in (M N)ᶜ, f ω ∂μ := if_neg (lt_irrefl N)
      rw [heF, nested_shell_integrals μ M hM hmeas f hf, hHN]
      have heq := integral_add_compl (hmeas N) hf
      dsimp [I₀]
      linarith
    · have hnlt : n < N := lt_of_le_of_ne hn he
      have hh : (∑ k ∈ range (n+1), F k) =
          ∑ k ∈ range (n+1), ∫ ω in M (k+1) \ M k, f ω ∂μ := by
        apply sum_congr rfl
        intro k hk
        exact if_pos (lt_of_le_of_lt (Nat.le_of_lt_succ (mem_range.mp hk)) hnlt)
      rw [hh,nested_shell_integrals μ M hM hmeas f hf]
      exact sub_le_sub_right (hH n hnlt) I₀
  have hweighted : (∫ ω in (M 0)ᶜ, f ω*v ω ∂μ) ≤ ∑ n ∈ range (N+1), F n*g n := by
    rw [nested_complement_integrals μ M hM hmeas _ hfv N, sum_range_succ]
    apply add_le_add
    · apply sum_le_sum
      intro n hn
      have hnlt := mem_range.mp hn
      have heF : F n = ∫ ω in M (n+1) \ M n, f ω ∂μ := if_pos hnlt
      rw [heF, ← integral_mul_const]
      apply setIntegral_mono_on hfv.integrableOn (hf.mul_const _).integrableOn
        ((hmeas (n+1)).diff (hmeas n))
      intro ω hω
      exact mul_le_mul_of_nonneg_left (hv n (Nat.le_of_lt hnlt) ω hω.2) (hfpos ω)
    · have heF : F N = ∫ ω in (M N)ᶜ, f ω ∂μ := if_neg (lt_irrefl N)
      rw [heF, ← integral_mul_const]
      apply setIntegral_mono_on hfv.integrableOn (hf.mul_const _).integrableOn (hmeas N).compl
      intro ω hω
      exact mul_le_mul_of_nonneg_left (hv N le_rfl ω hω) (hfpos ω)
  apply hweighted.trans
  have hb := weighted_cumulative_bound F g (fun n => H n-I₀) N hprefix hgN hg
  simpa only [sub_sub_sub_cancel_right, mul_comm] using hb


theorem nested_minor_weighted_integral_bound (M : ℕ → Set Ω) (hM : Monotone M)
    (hmeas : ∀ n, MeasurableSet (M n)) (f v : Ω → ℝ)
    (hf : Integrable f μ) (hfv : Integrable (fun ω => f ω*v ω) μ)
    (hfpos : ∀ ω, 0 ≤ f ω) (g H D : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hg : AntitoneOn g (Set.Icc a (a+N))) (hgN : 0 ≤ g (a+N))
    (hv : ∀ n ≤ N, ∀ ω ∈ (M n)ᶜ, v ω ≤ g (a+n))
    (hH : ∀ n < N, (∫ ω in M (n+1), f ω ∂μ) ≤ H (a+n))
    (hHN : H (a+N) = ∫ ω, f ω ∂μ)
    (hD : ∀ u ∈ Set.Icc a (a+N), 0 ≤ D u)
    (hderiv : ∀ u ∈ Set.Icc a (a+N), HasDerivAt H (D u) u)
    (hiD : IntervalIntegrable D volume a (a+N))
    (higD : IntervalIntegrable (fun u => g u*D u) volume a (a+N)) :
    (∫ ω in (M 0)ᶜ, f ω*v ω ∂μ) ≤
      g a*(H a-(∫ ω in M 0, f ω ∂μ)) + ∫ u in a..(a+N), g u*D u := by
  have hnodes (n : ℕ) (hn : n ≤ N) : a+(n : ℝ) ∈ Set.Icc a (a+N) := by
    constructor
    · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · exact add_le_add le_rfl (show (n : ℝ) ≤ N by exact_mod_cast hn)
  have hb := nested_minor_weighted_discrete_bound μ M hM hmeas f v hf hfv hfpos
    (fun n => g (a+n)) (fun n => H (a+n)) N
    (fun n hn => hg (hnodes n (Nat.le_of_lt hn)) (hnodes (n+1) hn) (by norm_num))
    hgN hv hH hHN
  simp only [Nat.cast_zero,add_zero] at hb
  exact hb.trans (add_le_add le_rfl
    (weighted_majorant_increments_integral_bound g H D a N hg hD hderiv hiD higD))

theorem nested_minor_weighted_integral_bound_right (M : ℕ → Set Ω) (hM : Monotone M)
    (hmeas : ∀ n, MeasurableSet (M n)) (f v : Ω → ℝ)
    (hf : Integrable f μ) (hfv : Integrable (fun ω => f ω*v ω) μ)
    (hfpos : ∀ ω, 0 ≤ f ω) (g H D : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hg : AntitoneOn g (Set.Icc a (a+N))) (hgN : 0 ≤ g (a+N))
    (hv : ∀ n ≤ N, ∀ ω ∈ (M n)ᶜ, v ω ≤ g (a+n))
    (hH : ∀ n < N, (∫ ω in M (n+1), f ω ∂μ) ≤ H (a+n))
    (hHN : H (a+N) = ∫ ω, f ω ∂μ)
    (hD : ∀ u ∈ Set.Icc a (a+N), 0 ≤ D u)
    (hcont : ContinuousOn H (Set.Icc a (a+N)))
    (hderiv : ∀ u ∈ Set.Ioo a (a+N), HasDerivWithinAt H (D u) (Set.Ioi u) u)
    (hiD : IntervalIntegrable D volume a (a+N))
    (higD : IntervalIntegrable (fun u => g u*D u) volume a (a+N)) :
    (∫ ω in (M 0)ᶜ, f ω*v ω ∂μ) ≤
      g a*(H a-(∫ ω in M 0, f ω ∂μ)) + ∫ u in a..(a+N), g u*D u := by
  have hnodes (n : ℕ) (hn : n ≤ N) : a+(n : ℝ) ∈ Set.Icc a (a+N) := by
    constructor
    · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · exact add_le_add le_rfl (show (n : ℝ) ≤ N by exact_mod_cast hn)
  have hb := nested_minor_weighted_discrete_bound μ M hM hmeas f v hf hfv hfpos
    (fun n => g (a+n)) (fun n => H (a+n)) N
    (fun n hn => hg (hnodes n (Nat.le_of_lt hn)) (hnodes (n+1) hn) (by norm_num))
    hgN hv hH hHN
  simp only [Nat.cast_zero,add_zero] at hb
  exact hb.trans (add_le_add le_rfl
    (weighted_majorant_increments_integral_bound_right g H D a N hg hD hcont hderiv hiD higD))

end Helfgott
end

section
/-!
The absolutely convergent weighted ternary counting identity. This is the
analytic-to-arithmetic interface in H. A. Helfgott, arXiv:1312.7748v2,
equations (1.3) and (7.49). The series are not truncated: the formulation
retains the tails of the Gaussian-based smoothing functions.

Written by Codex. The proof uses Mathlib's Fourier orthogonality and
dominated convergence for absolutely summable series.
-/

open MeasureTheory
open scoped BigOperators

namespace Helfgott

lemma mem_tripleIndices (t : (ℕ × ℕ) × ℕ) (N : ℕ) :
    t ∈ tripleIndices N ↔ t.1.1 + t.1.2 + t.2 = N := by
  simp only [tripleIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, h⟩

lemma integral_character (k : ℤ) :
    (∫ α : AddCircle (1 : ℝ), fourier k α ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

lemma norm_term (d : ℂ) (k : ℤ) (α : AddCircle (1 : ℝ)) :
    ‖d * fourier k α‖ = ‖d‖ := by
  simp [fourier_apply, Circle.norm_coe]

lemma summable_twisted (a : ℕ → ℂ) (ha : Summable a) (α : AddCircle (1 : ℝ)) :
    Summable (fun n => ‖a n * fourier (n : ℤ) α‖) := by
  simpa only [norm_term] using ha.norm

lemma expand_triple (a b c : ℕ → ℂ) (ha : Summable a) (hb : Summable b)
    (hc : Summable c) (N : ℕ) (α : AddCircle (1 : ℝ)) :
    expSum a α * expSum b α * expSum c α * fourier (-(N : ℤ)) α =
      ∑' t : (ℕ × ℕ) × ℕ,
        (a t.1.1 * b t.1.2 * c t.2) *
          fourier ((t.1.1 : ℤ) + (t.1.2 : ℤ) + (t.2 : ℤ) - (N : ℤ)) α := by
  have ha' := summable_twisted a ha α
  have hb' := summable_twisted b hb α
  have hc' := summable_twisted c hc α
  have hab' := ha'.mul_norm hb'
  have habc' := hab'.mul_norm hc'
  unfold expSum
  rw [tsum_mul_tsum_of_summable_norm ha' hb',
    tsum_mul_tsum_of_summable_norm hab' hc', ← habc'.of_norm.tsum_mul_right]
  apply tsum_congr
  intro t
  simp only [sub_eq_add_neg, fourier_add]
  ring

theorem weighted_ternary_counting (a b c : ℕ → ℂ) (ha : Summable a)
    (hb : Summable b) (hc : Summable c) (N : ℕ) :
    (∫ α : AddCircle (1 : ℝ),
      expSum a α * expSum b α * expSum c α * fourier (-(N : ℤ)) α
        ∂AddCircle.haarAddCircle) = tripleCount a b c N := by
  classical
  let coeff : (ℕ × ℕ) × ℕ → ℂ := fun t => a t.1.1 * b t.1.2 * c t.2
  let freq : (ℕ × ℕ) × ℕ → ℤ :=
    fun t => (t.1.1 : ℤ) + (t.1.2 : ℤ) + (t.2 : ℤ) - (N : ℤ)
  let F : ((ℕ × ℕ) × ℕ) → AddCircle (1 : ℝ) → ℂ :=
    fun t α => coeff t * fourier (freq t) α
  have hs : Summable (fun t => ‖coeff t‖) := (ha.norm.mul_norm hb.norm).mul_norm hc.norm
  have hi : ∀ t, Integrable (F t) AddCircle.haarAddCircle := by
    intro t
    simpa only [F, smul_eq_mul, mul_comm] using
      (integrable_const (coeff t)).fourier_smul (freq t)
  have hns : Summable (fun t => ∫ α : AddCircle (1 : ℝ), ‖F t α‖
      ∂AddCircle.haarAddCircle) := by
    simp_rw [F, norm_term, integral_const]
    simpa [Measure.real] using hs
  have hterm (t : (ℕ × ℕ) × ℕ) :
      (∫ α : AddCircle (1 : ℝ), F t α ∂AddCircle.haarAddCircle) =
        if t.1.1 + t.1.2 + t.2 = N then coeff t else 0 := by
    rw [show F t = (fun α => coeff t * fourier (freq t) α) from rfl,
      integral_const_mul, integral_character]
    have heq : freq t = 0 ↔ t.1.1 + t.1.2 + t.2 = N := by
      dsimp [freq]
      omega
    simp [heq]
  calc
    _ = ∫ α : AddCircle (1 : ℝ), ∑' t, F t α ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (expand_triple a b c ha hb hc N)
    _ = ∑' t, ∫ α : AddCircle (1 : ℝ), F t α ∂AddCircle.haarAddCircle :=
      (integral_tsum_of_summable_integral_norm hi hns).symm
    _ = ∑ t ∈ tripleIndices N, coeff t := by
      simp_rw [hterm]
      rw [tsum_eq_sum (s := tripleIndices N)]
      · apply Finset.sum_congr rfl
        intro t ht
        simp [(mem_tripleIndices t N).mp ht]
      · intro t ht
        simp [show t.1.1 + t.1.2 + t.2 ≠ N from fun h => ht ((mem_tripleIndices t N).mpr h)]
    _ = tripleCount a b c N := rfl

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Finset
open scoped BigOperators Classical

namespace Helfgott

theorem expSum_continuous_for_sieve (c : ℕ → ℂ) (hc : Summable c) :
    Continuous (expSum c) := by
  unfold expSum
  apply continuous_tsum (f := fun (n : ℕ) (α : AddCircle (1 : ℝ)) => c n*fourier (n : ℤ) α)
    (fun n => continuous_const.mul (map_continuous (fourier (n : ℤ)))) hc.norm
  intro n α
  rw [norm_term]

theorem expSum_square_energy_parseval (c : ℕ → ℂ) (hc : Summable c) :
    (∫ α : AddCircle (1 : ℝ), ‖expSum c α‖^2 ∂AddCircle.haarAddCircle) =
      ∑' n : ℕ, ‖c n‖^2 := by
  classical
  let C (p : ℕ × ℕ) : ℂ := c p.1 * star (c p.2)
  let F (p : ℕ × ℕ) (α : AddCircle (1 : ℝ)) : ℂ :=
    C p * fourier ((p.1 : ℤ)-(p.2 : ℤ)) α
  have hC : Summable (fun p : ℕ × ℕ => ‖C p‖) := by
    simpa only [C, norm_mul, norm_star] using hc.norm.mul_norm hc.norm
  have hi (p : ℕ × ℕ) : Integrable (F p) AddCircle.haarAddCircle := by
    simpa only [F, smul_eq_mul, mul_comm] using
      (integrable_const (C p)).fourier_smul ((p.1 : ℤ)-(p.2 : ℤ))
  have hn : Summable (fun p : ℕ × ℕ =>
      ∫ α : AddCircle (1 : ℝ), ‖F p α‖ ∂AddCircle.haarAddCircle) := by
    simp_rw [F, norm_term, integral_const]
    simpa [Measure.real] using hC
  have he (α : AddCircle (1 : ℝ)) :
      expSum c α * star (expSum c α) = ∑' p : ℕ × ℕ, F p α := by
    have hstar : star (expSum c α) =
        ∑' m : ℕ, star (c m)*fourier (-(m : ℤ)) α := by
      rw [expSum, tsum_star]
      apply tsum_congr
      intro m
      rw [star_mul, mul_comm]
      change star (c m)*(starRingEnd ℂ) (fourier (m : ℤ) α) = _
      rw [← fourier_neg]
    have hs1 : Summable (fun n : ℕ => ‖c n * fourier (n : ℤ) α‖) := summable_twisted c hc α
    have hs2 : Summable (fun m : ℕ => ‖star (c m)*fourier (-(m : ℤ)) α‖) := by
      simpa only [norm_term, norm_star] using hc.norm
    rw [hstar, expSum, tsum_mul_tsum_of_summable_norm hs1 hs2]
    apply tsum_congr
    intro p
    simp only [F, C, sub_eq_add_neg, fourier_add]
    ring
  have hterm (p : ℕ × ℕ) :
      (∫ α : AddCircle (1 : ℝ), F p α ∂AddCircle.haarAddCircle) =
        if p.1=p.2 then C p else 0 := by
    rw [show F p = (fun α => C p*fourier ((p.1 : ℤ)-(p.2 : ℤ)) α) from rfl,
      integral_const_mul, integral_character]
    have hzero : (p.1 : ℤ)-(p.2 : ℤ)=0 ↔ p.1=p.2 := by omega
    simp [hzero]
  have hd : Summable (fun p : ℕ × ℕ => if p.1=p.2 then C p else 0) := by
    refine hC.of_norm_bounded ?_
    intro p
    split_ifs <;> simp [norm_nonneg]
  have hcomplex :
      (∫ α : AddCircle (1 : ℝ), expSum c α*star (expSum c α) ∂AddCircle.haarAddCircle) =
        ∑' n : ℕ, c n*star (c n) := by
    calc
      _ = ∫ α : AddCircle (1 : ℝ), ∑' p : ℕ × ℕ, F p α ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall he
      _ = ∑' p : ℕ × ℕ, ∫ α : AddCircle (1 : ℝ), F p α ∂AddCircle.haarAddCircle :=
        (integral_tsum_of_summable_integral_norm hi hn).symm
      _ = ∑' n : ℕ, c n*star (c n) := by
        simp_rw [hterm]
        rw [hd.tsum_prod]
        simp [C]
  change (∫ α : AddCircle (1 : ℝ), expSum c α*(starRingEnd ℂ) (expSum c α)
      ∂AddCircle.haarAddCircle) = ∑' n : ℕ, c n*(starRingEnd ℂ) (c n) at hcomplex
  simp_rw [Complex.mul_conj'] at hcomplex
  simp_rw [← Complex.ofReal_pow] at hcomplex
  rw [integral_complex_ofReal, ← Complex.ofReal_tsum] at hcomplex
  exact Complex.ofReal_injective hcomplex

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Finset
open scoped BigOperators Classical

namespace Helfgott

lemma majorArcs_isOpen_for_weighted (δ : ℝ) (r : ℕ) (x : ℝ) : IsOpen (majorArcs δ r x) := by
  apply isOpen_iff_mem_nhds.mpr
  intro α hα
  rcases hα with ⟨q,a,hq,ha,hcop,hodd | heven⟩
  · have ho : IsOpen {β : AddCircle (1 : ℝ) |
        dist β ((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ)) < δ*r/(2*q*x)} :=
      isOpen_lt (continuous_id.dist continuous_const) continuous_const
    apply Filter.mem_of_superset (ho.mem_nhds hodd.2.2)
    intro β hβ
    exact ⟨q,a,hq,ha,hcop,Or.inl ⟨hodd.1,hodd.2.1,hβ⟩⟩
  · have he : IsOpen {β : AddCircle (1 : ℝ) |
        dist β ((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ)) < δ*r/(q*x)} :=
      isOpen_lt (continuous_id.dist continuous_const) continuous_const
    apply Filter.mem_of_superset (he.mem_nhds heven.2.2)
    intro β hβ
    exact ⟨q,a,hq,ha,hcop,Or.inr ⟨heven.1,heven.2.1,hβ⟩⟩

lemma majorArcs_mono_for_weighted (δ x : ℝ) (hδ : 0 ≤ δ) (hx : 0 < x) :
    Monotone (fun r : ℕ => majorArcs δ r x) := by
  intro r s hrs α hα
  rcases hα with ⟨q,a,hq,ha,hcop,ho | he⟩
  have hδrs : δ*(r : ℝ) ≤ δ*(s : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) hδ
  · refine ⟨q,a,hq,ha,hcop,Or.inl ⟨ho.1,ho.2.1.trans hrs,?_⟩⟩
    exact ho.2.2.trans_le (div_le_div_of_nonneg_right hδrs (by positivity))
  have hδrs : δ*(r : ℝ) ≤ δ*(s : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) hδ
  · refine ⟨q,a,hq,ha,hcop,Or.inr ⟨he.1,he.2.1.trans (Nat.mul_le_mul_left 2 hrs),?_⟩⟩
    exact he.2.2.trans_le (div_le_div_of_nonneg_right hδrs (by positivity))

theorem variable_radius_minor_arc_bound_complete (c : ℕ → ℂ) (hc : Summable c)
    (S₂ : AddCircle (1 : ℝ) → ℂ) (hS₂ : Continuous S₂)
    (δ x : ℝ) (r₀ N : ℕ) (hδ : 0 ≤ δ) (hx : 0 < x)
    (g H D : ℝ → ℝ)
    (hg : AntitoneOn g (Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)))
    (hgN : 0 ≤ g ((r₀+N : ℕ) : ℝ))
    (hminor : ∀ n ≤ N, ∀ α ∈ (majorArcs δ (r₀+n) x)ᶜ,
      ‖S₂ α‖ ≤ g ((r₀+n : ℕ) : ℝ))
    (hmajor : ∀ n < N,
      (∫ α in majorArcs δ (r₀+n+1) x, ‖expSum c α‖^2 ∂AddCircle.haarAddCircle) ≤
        H ((r₀+n : ℕ) : ℝ))
    (hHlast : H ((r₀+N : ℕ) : ℝ) = ∑' n : ℕ, ‖c n‖^2)
    (hD : ∀ u ∈ Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ), 0 ≤ D u)
    (hcontH : ContinuousOn H (Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)))
    (hderiv : ∀ u ∈ Set.Ioo (r₀ : ℝ) ((r₀+N : ℕ) : ℝ),
      HasDerivWithinAt H (D u) (Set.Ioi u) u)
    (hiD : IntervalIntegrable D volume (r₀ : ℝ) ((r₀+N : ℕ) : ℝ))
    (higD : IntervalIntegrable (fun u => g u*D u) volume (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)) :
    (∫ α in (majorArcs δ r₀ x)ᶜ, ‖expSum c α‖^2*‖S₂ α‖ ∂AddCircle.haarAddCircle) ≤
      g r₀*(H r₀-(∫ α in majorArcs δ r₀ x, ‖expSum c α‖^2 ∂AddCircle.haarAddCircle)) +
        ∫ u in (r₀ : ℝ)..((r₀+N : ℕ) : ℝ), g u*D u := by
  have hcont : Continuous (fun α => ‖expSum c α‖^2) :=
    (expSum_continuous_for_sieve c hc).norm.pow 2
  have hf : Integrable (fun α => ‖expSum c α‖^2) AddCircle.haarAddCircle :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_univ (by simp))
  have hfv : Integrable (fun α => ‖expSum c α‖^2*‖S₂ α‖) AddCircle.haarAddCircle :=
    (hcont.mul hS₂.norm).integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_univ (by simp))
  have hM : Monotone (fun n : ℕ => majorArcs δ (r₀+n) x) :=
    (majorArcs_mono_for_weighted δ x hδ hx).comp (monotone_const.add monotone_id)
  have hb := nested_minor_weighted_integral_bound_right AddCircle.haarAddCircle
    (fun n => majorArcs δ (r₀+n) x) hM
    (fun n => (majorArcs_isOpen_for_weighted δ (r₀+n) x).measurableSet)
    (fun α => ‖expSum c α‖^2) (fun α => ‖S₂ α‖) hf hfv (fun α => sq_nonneg _)
    g H D (r₀ : ℝ) N
    (by simpa only [Nat.cast_add] using hg) (by simpa only [Nat.cast_add] using hgN)
    (by simpa only [Nat.cast_add] using hminor)
    (by simpa only [Nat.cast_add,Nat.add_assoc] using hmajor)
    (by rw [expSum_square_energy_parseval c hc]; simpa only [Nat.cast_add] using hHlast)
    (by simpa only [Nat.cast_add] using hD)
    (by simpa only [Nat.cast_add] using hcontH)
    (by simpa only [Nat.cast_add] using hderiv)
    (by simpa only [Nat.cast_add] using hiD)
    (by simpa only [Nat.cast_add] using higD)
  simpa only [Nat.add_zero,Nat.cast_add] using hb

end Helfgott
end

open MeasureTheory Finset Helfgott
open scoped BigOperators Classical

theorem solution (c : ℕ → ℂ) (hc : Summable c)
    (S₂ : AddCircle (1 : ℝ) → ℂ) (hS₂ : Continuous S₂)
    (δ x : ℝ) (r₀ N : ℕ) (hδ : 0 ≤ δ) (hx : 0 < x)
    (g H D : ℝ → ℝ)
    (hg : AntitoneOn g (Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)))
    (hgN : 0 ≤ g ((r₀+N : ℕ) : ℝ))
    (hminor : ∀ n ≤ N, ∀ α ∈ (majorArcs δ (r₀+n) x)ᶜ,
      ‖S₂ α‖ ≤ g ((r₀+n : ℕ) : ℝ))
    (hmajor : ∀ n < N,
      (∫ α in majorArcs δ (r₀+n+1) x, ‖expSum c α‖^2 ∂AddCircle.haarAddCircle) ≤
        H ((r₀+n : ℕ) : ℝ))
    (hHlast : H ((r₀+N : ℕ) : ℝ) = ∑' n : ℕ, ‖c n‖^2)
    (hD : ∀ u ∈ Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ), 0 ≤ D u)
    (hcontH : ContinuousOn H (Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)))
    (hderiv : ∀ u ∈ Set.Ioo (r₀ : ℝ) ((r₀+N : ℕ) : ℝ),
      HasDerivWithinAt H (D u) (Set.Ioi u) u)
    (hiD : IntervalIntegrable D volume (r₀ : ℝ) ((r₀+N : ℕ) : ℝ))
    (higD : IntervalIntegrable (fun u => g u*D u) volume (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)) :
    (∫ α in (majorArcs δ r₀ x)ᶜ, ‖expSum c α‖^2*‖S₂ α‖ ∂AddCircle.haarAddCircle) ≤
      g r₀*(H r₀-(∫ α in majorArcs δ r₀ x, ‖expSum c α‖^2 ∂AddCircle.haarAddCircle)) +
        ∫ u in (r₀ : ℝ)..((r₀+N : ℕ) : ℝ), g u*D u := Helfgott.variable_radius_minor_arc_bound_complete c hc S₂ hS₂ δ x r₀ N hδ hx g H D hg hgN hminor hmajor hHlast hD hcontH hderiv hiD higD

#print axioms solution
