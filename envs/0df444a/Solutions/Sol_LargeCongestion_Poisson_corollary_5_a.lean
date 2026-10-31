-- Prove2me | solution 1 for LargeCongestion.Poisson.corollary_5_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:39:36.992287+00:00
-- url     : https://prove2.me/submissions/db09095c-fd73-4346-9a31-ca0bbd0251ff

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Theorems.Thm_LargeCongestion_Poisson_proposition_5_b
import Theorems.Thm_LargeCongestion_Poisson_proposition_6_b

open MeasureTheory ProbabilityTheory LargeCongestion.Poisson Filter Set
open scoped Topology

namespace LCPCor5aAux

lemma pmf_nonneg (x : ℝ) (k : ℕ) : 0 ≤ poissonPmf x k := measureReal_nonneg

lemma pmf_le (x d : ℝ) (hx : 0 ≤ x) (hxd : x ≤ d) (k : ℕ) :
    poissonPmf x k ≤ Real.exp (d - x) * poissonPmf d k := by
  rw [poissonPmf_eq hx, poissonPmf_eq (hx.trans hxd)]
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have : Real.exp (d - x) * (Real.exp (-d) * d ^ k / k.factorial) =
      Real.exp (-x) * d ^ k / k.factorial := by
    rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add]; ring_nf
  rw [this]
  apply div_le_div_of_nonneg_right _ hk.le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxd k) (Real.exp_pos _).le

lemma summable_of_moment (g : ℕ → ℝ) (x : ℝ) (j : ℕ)
    (hm : Summable (fun k : ℕ => (k : ℝ) ^ j * |g k| * poissonPmf x k)) :
    Summable (fun k : ℕ => |g k| * poissonPmf x k) := by
  rw [← summable_nat_add_iff 1]
  have hm' := (summable_nat_add_iff 1).2 hm
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _))
    (fun k => ?_) hm'
  have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ j :=
    one_le_pow₀ (by push_cast; linarith [k.cast_nonneg (α := ℝ)])
  have h2 : 0 ≤ |g (k + 1)| * poissonPmf x (k + 1) := mul_nonneg (abs_nonneg _) (pmf_nonneg _ _)
  calc |g (k + 1)| * poissonPmf x (k + 1) ≤
      ((k + 1 : ℕ) : ℝ) ^ j * (|g (k + 1)| * poissonPmf x (k + 1)) := le_mul_of_one_le_left h2 h1
    _ = ((k + 1 : ℕ) : ℝ) ^ j * |g (k + 1)| * poissonPmf x (k + 1) := by ring

lemma poissonMean_zero (g : ℕ → ℝ) : poissonMean g 0 = g 0 := by
  unfold poissonMean
  rw [tsum_eq_single 0]
  · rw [poissonPmf_eq le_rfl]; simp
  · intro k hk
    rw [poissonPmf_eq le_rfl, zero_pow hk]; simp

end LCPCor5aAux

open LCPCor5aAux in
theorem solution (h : ℕ → ℝ) (dmax ν : ℝ) (hd : 0 < dmax)
    (hint : Summable (fun k : ℕ => |deltaPow 2 h k| * poissonPmf dmax k))
    (hν : ∑' k : ℕ, |deltaPow 2 h k| * poissonPmf dmax k ≤ ν) :
    ∀ x ∈ Set.Icc 0 dmax,
      |derivWithin (poissonMean h) (Set.Icc 0 dmax) x| ≤
        (Real.exp dmax - 1) * ν + |h 1 - h 0| := by
  set I := Icc (0 : ℝ) dmax with hI
  -- integrability of `Δh(V)`
  have hint' : Summable (fun k : ℕ => |deltaPow 1 (delta h) k| * poissonPmf dmax k) := hint
  have hmom := ((proposition_5_b (delta h) dmax hd.le 1 le_rfl).1.trans
    (proposition_5_b (delta h) dmax hd.le 1 le_rfl).2).1 hint'
  have hint1 : Summable (fun k : ℕ => |deltaPow 1 h k| * poissonPmf dmax k) :=
    summable_of_moment (delta h) dmax 1 hmom
  have hint1' : Summable (fun k : ℕ => |deltaPow 1 (delta h) k| * poissonPmf dmax k) := hint
  -- `h̆' = (Δh)˘` and `(Δh)˘' = (Δ²h)˘` on `[0, d_max]`
  have P1 := proposition_6_b h dmax hd 1 hint1
  have P2 := proposition_6_b (delta h) dmax hd 1 hint1'
  set g : ℝ → ℝ := poissonMean (delta h) with hg
  set q : ℝ → ℝ := poissonMean (deltaPow 2 h) with hq
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hd
  have hfg : ∀ x ∈ I, derivWithin (poissonMean h) I x = g x := by
    intro x hx
    have := P1.2 x hx
    rw [iteratedDerivWithin_one] at this
    rw [this]; rfl
  have hgcont : ContinuousOn g I := P2.1.continuousOn
  have hgdiff : DifferentiableOn ℝ g I := P2.1.differentiableOn (by norm_num)
  have hgq : ∀ x ∈ I, derivWithin g I x = q x := by
    intro x hx
    have := P2.2 x hx
    rw [iteratedDerivWithin_one] at this
    rw [this]; rfl
  -- derivative on the interior
  have hint_deriv : ∀ x ∈ interior I, HasDerivAt g (q x) x := by
    intro x hx
    rw [interior_Icc] at hx
    have hmem : I ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have hw := (hgdiff x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
    rw [hgq x (Ioo_subset_Icc_self hx)] at hw
    exact hw.hasDerivAt hmem
  -- `|q x| ≤ e^{d_max - x} ν`
  have hqb : ∀ x ∈ I, |q x| ≤ Real.exp (dmax - x) * ν := by
    intro x hx
    have hb : ∀ k, |deltaPow 2 h k * poissonPmf x k| ≤
        Real.exp (dmax - x) * (|deltaPow 2 h k| * poissonPmf dmax k) := by
      intro k
      rw [abs_mul, abs_of_nonneg (pmf_nonneg _ _)]
      calc |deltaPow 2 h k| * poissonPmf x k ≤
          |deltaPow 2 h k| * (Real.exp (dmax - x) * poissonPmf dmax k) :=
            mul_le_mul_of_nonneg_left (pmf_le x dmax hx.1 hx.2 k) (abs_nonneg _)
        _ = _ := by ring
    have hs2 : Summable (fun k => Real.exp (dmax - x) * (|deltaPow 2 h k| * poissonPmf dmax k)) :=
      hint.mul_left _
    have hsn : Summable (fun k => ‖deltaPow 2 h k * poissonPmf x k‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hb k) hs2
    calc |q x| = ‖∑' k, deltaPow 2 h k * poissonPmf x k‖ := rfl
      _ ≤ ∑' k, ‖deltaPow 2 h k * poissonPmf x k‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, Real.exp (dmax - x) * (|deltaPow 2 h k| * poissonPmf dmax k) :=
          hsn.tsum_le_tsum (fun k => hb k) hs2
      _ = Real.exp (dmax - x) * ∑' k, |deltaPow 2 h k| * poissonPmf dmax k := tsum_mul_left
      _ ≤ Real.exp (dmax - x) * ν := mul_le_mul_of_nonneg_left hν (Real.exp_pos _).le
  have hexp_d : ∀ x, HasDerivAt (fun t => Real.exp (dmax - t)) (-Real.exp (dmax - x)) x := by
    intro x
    exact (((hasDerivAt_id x).const_sub dmax).exp).congr_deriv (by simp)
  -- monotonicity arguments
  have hanti : AntitoneOn (fun t => g t + ν * Real.exp (dmax - t)) I := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 dmax)
    · exact hgcont.add (by fun_prop)
    · intro x hx
      exact ((hint_deriv x hx).add ((hexp_d x).const_mul ν)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hD : HasDerivAt (fun t => g t + ν * Real.exp (dmax - t))
          (q x + ν * -Real.exp (dmax - x)) x := (hint_deriv x hx).add ((hexp_d x).const_mul ν)
      rw [hD.deriv]
      have hxI : x ∈ I := interior_subset hx
      have := (abs_le.1 (hqb x hxI)).2
      linarith
  have hmono : MonotoneOn (fun t => g t - ν * Real.exp (dmax - t)) I := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 dmax)
    · exact hgcont.sub (by fun_prop)
    · intro x hx
      exact ((hint_deriv x hx).sub ((hexp_d x).const_mul ν)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hD : HasDerivAt (fun t => g t - ν * Real.exp (dmax - t))
          (q x - ν * -Real.exp (dmax - x)) x := (hint_deriv x hx).sub ((hexp_d x).const_mul ν)
      rw [hD.deriv]
      have hxI : x ∈ I := interior_subset hx
      have := (abs_le.1 (hqb x hxI)).1
      linarith
  intro x hx
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, hd.le⟩
  have hν0 : 0 ≤ ν := le_trans (tsum_nonneg (fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _))) hν
  have a1 := hanti h0I hx hx.1
  have a2 := hmono h0I hx hx.1
  simp only [sub_zero] at a1 a2
  have hg0 : g 0 = h 1 - h 0 := by rw [hg, poissonMean_zero]; rfl
  have he1 : 1 ≤ Real.exp (dmax - x) := Real.one_le_exp (by linarith [hx.2])
  rw [hfg x hx]
  have hb : |g x - g 0| ≤ (Real.exp dmax - 1) * ν := by
    rw [abs_le]; constructor <;> nlinarith
  calc |g x| = |(g x - g 0) + g 0| := by ring_nf
    _ ≤ |g x - g 0| + |g 0| := abs_add_le _ _
    _ ≤ (Real.exp dmax - 1) * ν + |h 1 - h 0| := by rw [hg0] at *; linarith
