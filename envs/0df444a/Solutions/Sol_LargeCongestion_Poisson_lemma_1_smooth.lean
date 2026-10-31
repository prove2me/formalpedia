-- Prove2me | solution 1 for LargeCongestion.Poisson.lemma_1_smooth
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:28:35.036004+00:00
-- url     : https://prove2.me/submissions/110b1287-4ef7-4c81-8e82-3a11a51c2ccb

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game
import Theorems.Thm_LargeCongestion_Poisson_proposition_5_b
import Theorems.Thm_LargeCongestion_Poisson_proposition_6_b
import Theorems.Thm_LargeCongestion_Poisson_corollary_5_a

open MeasureTheory ProbabilityTheory LargeCongestion.Poisson

namespace LCPSmoothAux

lemma pmf_nonneg (x : ℝ) (k : ℕ) : 0 ≤ poissonPmf x k := measureReal_nonneg

/-- If `∑ k^j |g k| P(k)` converges with `j ≥ 1`, then so does `∑ |g k| P(k)`. -/
lemma summable_of_moment (g : ℕ → ℝ) (x : ℝ) (j : ℕ)
    (hm : Summable (fun k : ℕ => (k : ℝ) ^ j * |g k| * poissonPmf x k)) :
    Summable (fun k : ℕ => |g k| * poissonPmf x k) := by
  rw [← summable_nat_add_iff 1]
  have hm' := (summable_nat_add_iff 1).2 hm
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _))
    (fun k => ?_) hm'
  have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ j := one_le_pow₀ (by push_cast; linarith [k.cast_nonneg (α := ℝ)])
  have h2 : 0 ≤ |g (k + 1)| * poissonPmf x (k + 1) := mul_nonneg (abs_nonneg _) (pmf_nonneg _ _)
  calc |g (k + 1)| * poissonPmf x (k + 1) ≤
      ((k + 1 : ℕ) : ℝ) ^ j * (|g (k + 1)| * poissonPmf x (k + 1)) := le_mul_of_one_le_left h2 h1
    _ = ((k + 1 : ℕ) : ℝ) ^ j * |g (k + 1)| * poissonPmf x (k + 1) := by ring

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

end LCPSmoothAux

open LCPSmoothAux in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] (c : E → ℕ → ℝ)
    (hc : IsCostFamily c) (ν dmax : ℝ) (hd : 0 < dmax) (hM : MomentBound c ν dmax) (e : E) :
    (∀ x ∈ Set.Icc 0 dmax, Summable (fun k : ℕ => c e (1 + k) * poissonPmf x k)) ∧
      ContDiffOn ℝ 2 (cBreve c e) (Set.Icc 0 dmax) ∧
      ∀ x ∈ Set.Icc 0 dmax,
        0 ≤ derivWithin (cBreve c e) (Set.Icc 0 dmax) x ∧
          derivWithin (cBreve c e) (Set.Icc 0 dmax) x ≤ zeta c ν dmax := by
  set h : ℕ → ℝ := fun k => c e (1 + k) with hh
  have hcB : cBreve c e = poissonMean h := rfl
  have hΔ2 : ∀ k, deltaPow 2 h k = deltaPow 2 (c e) (1 + k) := by
    intro k
    rw [deltaPow_two, deltaPow_two]
    simp only [hh, add_assoc]
  have hint : Summable (fun k : ℕ => |deltaPow 2 h k| * poissonPmf dmax k) := by
    simpa only [hΔ2] using (hM e).1
  have hν : ∑' k : ℕ, |deltaPow 2 h k| * poissonPmf dmax k ≤ ν := by
    simpa only [hΔ2] using (hM e).2
  -- summability of `|h(V)|`, `V ∼ Poisson(d_max)`
  have hmom2 := ((proposition_5_b h dmax hd.le 2 (by norm_num)).1.trans
    (proposition_5_b h dmax hd.le 2 (by norm_num)).2).1 hint
  have hsumd : Summable (fun k : ℕ => |h k| * poissonPmf dmax k) := summable_of_moment h dmax 2 hmom2
  -- summability of `|Δh(V)|`
  have hint1' : Summable (fun k : ℕ => |deltaPow 1 (delta h) k| * poissonPmf dmax k) := by
    have : deltaPow 1 (delta h) = deltaPow 2 h := rfl
    rw [this]; exact hint
  have hmom1 := ((proposition_5_b (delta h) dmax hd.le 1 le_rfl).1.trans
    (proposition_5_b (delta h) dmax hd.le 1 le_rfl).2).1 hint1'
  have hint1 : Summable (fun k : ℕ => |deltaPow 1 h k| * poissonPmf dmax k) :=
    summable_of_moment (delta h) dmax 1 hmom1
  have h6b2 := proposition_6_b h dmax hd 2 hint
  have h6b1 := proposition_6_b h dmax hd 1 hint1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    refine Summable.of_norm_bounded (g := fun k => Real.exp (dmax - x) * (|h k| * poissonPmf dmax k))
      (hsumd.mul_left _) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pmf_nonneg _ _)]
    calc |h k| * poissonPmf x k ≤ |h k| * (Real.exp (dmax - x) * poissonPmf dmax k) :=
          mul_le_mul_of_nonneg_left (pmf_le x dmax hx.1 hx.2 k) (abs_nonneg _)
      _ = Real.exp (dmax - x) * (|h k| * poissonPmf dmax k) := by ring
  · rw [hcB]; exact_mod_cast h6b2.1
  · intro x hx
    have hder : derivWithin (cBreve c e) (Set.Icc 0 dmax) x = poissonMean (deltaPow 1 h) x := by
      rw [hcB, ← h6b1.2 x hx, iteratedDerivWithin_one]
    constructor
    · rw [hder]
      unfold poissonMean
      refine tsum_nonneg (fun k => mul_nonneg ?_ (pmf_nonneg _ _))
      simp only [deltaPow, Function.iterate_one, delta, hh]
      have := hc.2 e (show (1 + k : ℕ) ∈ Set.Ici 1 by simp) (show 1 + (k + 1) ∈ Set.Ici 1 by simp)
        (by omega)
      linarith
    · have hcor := corollary_5_a h dmax ν hd hint hν x hx
      rw [← hcB] at hcor
      have hmono : c e 1 ≤ c e 2 := hc.2 e (show (1 : ℕ) ∈ Set.Ici 1 by simp)
        (show (2 : ℕ) ∈ Set.Ici 1 by simp) (by norm_num)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c e 2 - c e 1)] at hcor
      have hsup : c e 2 - c e 1 ≤ ⨆ e', (c e' 2 - c e' 1) :=
        le_ciSup (f := fun e' => c e' 2 - c e' 1) (Set.finite_range _).bddAbove e
      unfold zeta
      linarith [le_abs_self (derivWithin (cBreve c e) (Set.Icc 0 dmax) x)]
