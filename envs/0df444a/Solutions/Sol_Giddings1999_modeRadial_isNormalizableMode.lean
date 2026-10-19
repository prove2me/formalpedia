-- Prove2me | solution 1 for Giddings1999.modeRadial_isNormalizableMode
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:55:04.250062+00:00
-- url     : https://prove2.me/submissions/f087196d-924c-437f-8008-9d56d28d7327

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Finset Filter Topology MeasureTheory
open Giddings1999

namespace GDJac

noncomputable def mm (s t : ℕ) (x : ℝ) : ℝ := ((x-1)/2)^s * ((x+1)/2)^t

lemma hasDerivAt_mm (s t : ℕ) (x : ℝ) :
    HasDerivAt (mm s t) ((s * mm (s-1) t x + t * mm s (t-1) x)/2) x := by
  have h1 : HasDerivAt (fun x:ℝ => ((x-1)/2)^s) (s * ((x-1)/2)^(s-1) * (1/2)) x := by
    have := (((hasDerivAt_id x).sub_const 1).div_const 2).fun_pow s
    simpa using this
  have h2 : HasDerivAt (fun x:ℝ => ((x+1)/2)^t) (t * ((x+1)/2)^(t-1) * (1/2)) x := by
    have := (((hasDerivAt_id x).add_const 1).div_const 2).fun_pow t
    simpa using this
  have := h1.fun_mul h2
  unfold mm
  refine this.congr_deriv ?_
  ring

lemma hu (k t : ℕ) (x : ℝ) : (x-1)/2 * ((k:ℝ) * mm (k-1) t x) = k * mm k t x := by
  cases k with
  | zero => simp
  | succ j => simp only [mm, Nat.add_sub_cancel]; ring

lemma hv (s k : ℕ) (x : ℝ) : (x+1)/2 * ((k:ℝ) * mm s (k-1) x) = k * mm s k x := by
  cases k with
  | zero => simp
  | succ j => simp only [mm, Nat.add_sub_cancel]; ring

/-- second derivative of a monomial (as an explicit expression) -/
noncomputable def D2 (s t : ℕ) (x : ℝ) : ℝ :=
  (s * ((↑(s-1) * mm (s-1-1) t x + t * mm (s-1) (t-1) x)/2)
    + t * ((s * mm (s-1) (t-1) x + ↑(t-1) * mm s (t-1-1) x)/2))/2

noncomputable def D1 (s t : ℕ) (x : ℝ) : ℝ := (s * mm (s-1) t x + t * mm s (t-1) x)/2

lemma hasDerivAt_D1 (s t : ℕ) (x : ℝ) : HasDerivAt (D1 s t) (D2 s t x) x := by
  have := (((hasDerivAt_mm (s-1) t x).const_mul (s:ℝ)).fun_add
    ((hasDerivAt_mm s (t-1) x).const_mul (t:ℝ))).div_const 2
  unfold D1 D2
  convert this using 1

lemma mono (α β : ℝ) (s t : ℕ) (x : ℝ) :
    (1 - x^2) * D2 s t x + (β - α - (α+β+2)*x) * D1 s t x
      + ((s+t:ℕ):ℝ) * ((s+t:ℕ) + α + β + 1) * mm s t x
    = - (s * (s + α)) * mm (s-1) (t+1) x - (t * (t + β)) * mm (s+1) (t-1) x
      + (((s+t:ℕ):ℝ) * ((s+t:ℕ) + α + β + 1) - 2*s*t - (α+1)*t - (β+1)*s) * mm s t x := by
  unfold D1 D2
  rcases s with _ | _ | k <;> rcases t with _ | _ | j <;>
    simp only [mm, Nat.add_sub_cancel, Nat.zero_sub, Nat.sub_self] <;> push_cast <;> ring

lemma gbinom_succ (a : ℝ) (k : ℕ) : gbinom a (k+1) * (k+1) = gbinom a k * (a - k) := by
  unfold gbinom
  rw [descPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  field_simp

noncomputable def A (n : ℕ) (α β : ℝ) (s : ℕ) : ℝ := gbinom (n+α) (n-s) * gbinom (n+β) s

lemma A_rec (n : ℕ) (α β : ℝ) (j : ℕ) (hj : j < n) :
    ((j:ℝ)+1) * ((j:ℝ)+1+α) * A n α β (j+1) = ((n:ℝ)-j) * ((n:ℝ)-j+β) * A n α β j := by
  unfold A
  have h1 := gbinom_succ (n+β) j
  have h2 := gbinom_succ (n+α) (n-j-1)
  have e : n - j - 1 + 1 = n - j := by omega
  have e' : n - (j+1) = n - j - 1 := by omega
  rw [e] at h2
  rw [e']
  have c : ((n-j-1 : ℕ):ℝ) = n - j - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hj.le]; simp
  rw [c] at h2
  linear_combination ((↑j + 1 + α) * gbinom (↑n + α) (n - j - 1)) * h1
    - (gbinom (↑n + β) j * (↑n + β - ↑j)) * h2

noncomputable def P (n : ℕ) (α β x : ℝ) : ℝ := ∑ s ∈ range (n+1), A n α β s * mm s (n-s) x
noncomputable def P1 (n : ℕ) (α β x : ℝ) : ℝ := ∑ s ∈ range (n+1), A n α β s * D1 s (n-s) x
noncomputable def P2 (n : ℕ) (α β x : ℝ) : ℝ := ∑ s ∈ range (n+1), A n α β s * D2 s (n-s) x

lemma P_eq (n : ℕ) (α β x : ℝ) : P n α β x = jacobiP n α β x := by
  unfold P jacobiP A mm
  refine sum_congr rfl fun s _ => by ring

lemma hasDerivAt_P (n : ℕ) (α β x : ℝ) : HasDerivAt (P n α β) (P1 n α β x) x := by
  unfold P P1
  have := HasDerivAt.fun_sum (u := range (n+1)) (A := fun s y => A n α β s * mm s (n-s) y)
    (A' := fun s => A n α β s * D1 s (n-s) x) (x := x)
    (fun s _ => (hasDerivAt_mm s (n-s) x).const_mul _)
  exact this

lemma hasDerivAt_P1 (n : ℕ) (α β x : ℝ) : HasDerivAt (P1 n α β) (P2 n α β x) x := by
  unfold P1 P2
  exact HasDerivAt.fun_sum (u := range (n+1)) (A := fun s y => A n α β s * D1 s (n-s) y)
    (A' := fun s => A n α β s * D2 s (n-s) x) (x := x)
    (fun s _ => (hasDerivAt_D1 s (n-s) x).const_mul _)

lemma jacobi_ode (n : ℕ) (α β x : ℝ) :
    (1 - x^2) * P2 n α β x + (β - α - (α+β+2)*x) * P1 n α β x
      + (n:ℝ) * (n + α + β + 1) * P n α β x = 0 := by
  unfold P P1 P2
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  have hm : ∀ s ∈ range (n+1), (1 - x^2) * (A n α β s * D2 s (n-s) x)
      + (β - α - (α+β+2)*x) * (A n α β s * D1 s (n-s) x)
      + (n:ℝ) * (n + α + β + 1) * (A n α β s * mm s (n-s) x)
      = A n α β s * (- (s * (s + α)) * mm (s-1) (n-s+1) x
          - (((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * mm (s+1) (n-s-1) x)
        + A n α β s * (((n:ℝ) * (n + α + β + 1) - 2*s*(n-s:ℕ) - (α+1)*(n-s:ℕ) - (β+1)*s)
          * mm s (n-s) x) := by
    intro s hs
    have hsn : s + (n - s) = n := by have := mem_range.1 hs; omega
    have := mono α β s (n-s) x
    rw [hsn] at this
    linear_combination (A n α β s) * this
  rw [sum_congr rfl hm, sum_add_distrib]
  -- first part: reindex
  have S1 : ∑ s ∈ range (n+1), A n α β s * (- (s * (s + α)) * mm (s-1) (n-s+1) x)
      = - ∑ s ∈ range (n+1), (((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * A n α β s * mm s (n-s) x := by
    rw [sum_range_succ', sum_range_succ]
    simp only [Nat.cast_zero, zero_mul, neg_zero, mul_zero, add_zero, Nat.sub_self, zero_add]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have e : n - (j+1) + 1 = n - j := by omega
    rw [Nat.add_sub_cancel, e]
    have := A_rec n α β j hj'
    have c : ((n - j : ℕ):ℝ) = n - j := by rw [Nat.cast_sub hj'.le]
    rw [c]; push_cast
    linear_combination (-mm j (n-j) x) * this
  have S3 : ∑ s ∈ range (n+1), A n α β s * (-(((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * mm (s+1) (n-s-1) x)
      = - ∑ s ∈ range (n+1), ((s:ℝ) * (s + α)) * A n α β s * mm s (n-s) x := by
    rw [sum_range_succ, sum_range_succ']
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, neg_zero, mul_zero, add_zero, zero_add]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have e : n - j - 1 = n - (j+1) := by omega
    rw [e]
    have := A_rec n α β j hj'
    have c : ((n - j : ℕ):ℝ) = n - j := by rw [Nat.cast_sub hj'.le]
    rw [c]; push_cast
    linear_combination (mm (j+1) (n-(j+1)) x) * this
  have split : ∀ s ∈ range (n+1), A n α β s * (- (s * (s + α)) * mm (s-1) (n-s+1) x
          - (((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * mm (s+1) (n-s-1) x)
      = A n α β s * (- (s * (s + α)) * mm (s-1) (n-s+1) x)
        + A n α β s * (-(((n-s:ℕ):ℝ) * ((n-s:ℕ) + β)) * mm (s+1) (n-s-1) x) := by
    intro s _; ring
  rw [sum_congr rfl split, sum_add_distrib, S1, S3, ← sum_neg_distrib, ← sum_neg_distrib,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_eq_zero fun s hs => ?_
  have hs' := mem_range.1 hs
  have c : ((n - s : ℕ):ℝ) = n - s := by rw [Nat.cast_sub (by omega)]
  rw [c]; ring

end GDJac


namespace GDRad
open GDJac

lemma pow_pred_mul (l : ℕ) (s : ℝ) : (l:ℝ) * s^(l-1) * s = l * s^l := by
  cases l with
  | zero => simp
  | succ k => simp [pow_succ]; ring

/-- first derivative of the mode -/
lemma hasDerivAt_chi (n l : ℕ) (b α β r : ℝ) (hs : 0 < sin r) (hc : 0 < cos r) :
    HasDerivAt (fun r => sin r ^ l * cos r ^ b * P n α β (cos (2 * r)))
      (sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P n α β (cos (2*r))
        + (-4 * sin r * cos r) * P1 n α β (cos (2*r)))) r := by
  have h1 : HasDerivAt (fun r => sin r ^ l) (l * sin r ^ (l-1) * cos r) r :=
    (hasDerivAt_sin r).fun_pow l
  have h2 : HasDerivAt (fun r => cos r ^ b) (b * cos r ^ (b - 1) * (-sin r)) r := by
    have := (hasDerivAt_cos r).rpow_const (p := b) (Or.inl hc.ne')
    refine this.congr_deriv ?_; ring
  have h3 : HasDerivAt (fun r => P n α β (cos (2 * r)))
      (P1 n α β (cos (2*r)) * (-sin (2*r) * 2)) r := by
    have hc2 : HasDerivAt (fun r => cos (2 * r)) (-sin (2*r) * 2) r := by
      have := ((hasDerivAt_id r).const_mul 2).cos
      simpa using this
    exact (hasDerivAt_P n α β _).comp r hc2
  have := (h1.fun_mul h2).fun_mul h3
  refine this.congr_deriv ?_
  rw [rpow_sub_one hc.ne', sin_two_mul]
  have e := pow_pred_mul l (sin r)
  field_simp
  linear_combination (cos r ^ 2 * P n α β (cos (2 * r))) * e

lemma hasDerivAt_D (n l : ℕ) (b α β r : ℝ) (hs : 0 < sin r) (hc : 0 < cos r) :
    HasDerivAt (fun r => sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P n α β (cos (2*r))
        + (-4 * sin r * cos r) * P1 n α β (cos (2*r))))
      (sin r ^ l * cos r ^ b * (((l * cos r / sin r - b * sin r / cos r)^2 + (-l / sin r^2 - b / cos r^2))
          * P n α β (cos (2*r))
        + (2 * (l * cos r / sin r - b * sin r / cos r) * (-4 * sin r * cos r) + (-4 * (cos r^2 - sin r^2)))
          * P1 n α β (cos (2*r))
        + (-4 * sin r * cos r)^2 * P2 n α β (cos (2*r)))) r := by
  have h1 : HasDerivAt (fun r => sin r ^ l) (l * sin r ^ (l-1) * cos r) r :=
    (hasDerivAt_sin r).fun_pow l
  have h2 : HasDerivAt (fun r => cos r ^ b) (b * cos r ^ (b - 1) * (-sin r)) r := by
    have := (hasDerivAt_cos r).rpow_const (p := b) (Or.inl hc.ne')
    refine this.congr_deriv ?_; ring
  have hX : HasDerivAt (fun r => cos (2 * r)) (-4 * sin r * cos r) r := by
    have := ((hasDerivAt_id r).const_mul 2).cos
    refine (by simpa using this : HasDerivAt (fun r => cos (2 * r)) (-sin (2*r) * 2) r).congr_deriv ?_
    rw [sin_two_mul]; ring
  have hPX := (hasDerivAt_P n α β _).comp r hX
  have hP1X := (hasDerivAt_P1 n α β _).comp r hX
  have hg : HasDerivAt (fun r => l * cos r / sin r - b * sin r / cos r) (-l / sin r^2 - b / cos r^2) r := by
    have := (((hasDerivAt_cos r).const_mul (l:ℝ)).div (hasDerivAt_sin r) hs.ne').fun_sub
      (((hasDerivAt_sin r).const_mul b).div (hasDerivAt_cos r) hc.ne')
    refine this.congr_deriv ?_
    have py := sin_sq_add_cos_sq r
    field_simp
    linear_combination (-(l:ℝ) * cos r ^ 2 - b * sin r ^ 2) * py
  have hh : HasDerivAt (fun r => -4 * sin r * cos r) (-4 * (cos r^2 - sin r^2)) r := by
    have := ((hasDerivAt_sin r).const_mul (-4:ℝ)).fun_mul (hasDerivAt_cos r)
    refine this.congr_deriv ?_; ring
  have h0 : HasDerivAt (fun r => sin r ^ l * cos r ^ b)
      (sin r ^ l * cos r ^ b * (l * cos r / sin r - b * sin r / cos r)) r := by
    have := h1.fun_mul h2
    refine this.congr_deriv ?_
    rw [rpow_sub_one hc.ne']
    have e := pow_pred_mul l (sin r)
    field_simp
    linear_combination (cos r ^ 2) * e
  have := h0.fun_mul ((hg.fun_mul hPX).fun_add (hh.fun_mul hP1X))
  refine this.congr_deriv ?_
  simp only [Function.comp]
  ring

lemma P_contDiff (n : ℕ) (α β : ℝ) : ContDiff ℝ 2 (P n α β) := by
  unfold P mm; fun_prop

lemma radial (d : ℕ) (m R : ℝ) (n l : ℕ) :
    IsRadialSolution d m R (omegaNL d m R n l) l (modeRadial d m R n l) := by
  set b := twoHPlus d m R with hb
  set ν := nu d m R with hν
  set α : ℝ := (l:ℝ) + (d:ℝ)/2 - 1 with hα
  have hmode : modeRadial d m R n l = fun r => sin r ^ l * cos r ^ b * P n α ν (cos (2*r)) := by
    funext r; simp only [modeRadial, P_eq]; rfl
  have hbν : b = d/2 + ν := rfl
  have hM : m^2 * R^2 = b * (b - d) := by
    have hs : Real.sqrt ((d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2) ^ 2 = (d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2 :=
      Real.sq_sqrt (by positivity)
    simp only [hb, twoHPlus, nu]; nlinarith [hs]
  have hω : omegaNL d m R n l = b + 2*n + l := rfl
  refine ⟨?_, ?_⟩
  · rw [hmode]
    intro r hr
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    apply ContDiffAt.contDiffWithinAt
    refine ((contDiff_sin.pow l).contDiffAt.mul ?_).mul ?_
    · exact (contDiffAt_rpow_const_of_ne hc.ne').comp r contDiff_cos.contDiffAt
    · exact ((P_contDiff n α ν).comp (contDiff_cos.comp (contDiff_const.mul contDiff_id))).contDiffAt
  · intro r hr
    rw [hmode]
    have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr.1 (by linarith [hr.2, pi_pos])
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    have hev : deriv (fun r => sin r ^ l * cos r ^ b * P n α ν (cos (2 * r))) =ᶠ[𝓝 r]
        (fun r => sin r ^ l * cos r ^ b * ((l * cos r / sin r - b * sin r / cos r) * P n α ν (cos (2*r))
          + (-4 * sin r * cos r) * P1 n α ν (cos (2*r)))) := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
      have hs' : 0 < sin r' := sin_pos_of_pos_of_lt_pi hr'.1 (by linarith [hr'.2, pi_pos])
      have hc' : 0 < cos r' := cos_pos_of_mem_Ioo ⟨by linarith [hr'.1, pi_pos], hr'.2⟩
      exact (hasDerivAt_chi n l b α ν r' hs' hc').deriv
    rw [hev.deriv_eq, (hasDerivAt_chi n l b α ν r hs hc).deriv, (hasDerivAt_D n l b α ν r hs hc).deriv]
    have jac := jacobi_ode n α ν (cos (2*r))
    rw [cos_two_mul] at jac
    beta_reduce
    rw [cos_two_mul, hω, hM]
    have py := sin_sq_add_cos_sq r
    set S := sin r
    set C := cos r
    set χ0 := S ^ l * C ^ b
    set Q0 := P n α ν (2 * C ^ 2 - 1)
    set Q1 := P1 n α ν (2 * C ^ 2 - 1)
    set Q2 := P2 n α ν (2 * C ^ 2 - 1)
    have ecP : (l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2) + ((d:ℝ) - 1) / (S * C) * (l * C / S - b * S / C)
        + (b + 2*n + l)^2 - l * (l + d - 2) / S^2 - b * (b - d) / C^2 = 4 * n * (n + α + ν + 1) := by
      rw [hα, hbν]
      field_simp
      linear_combination (4 * (l:ℝ)^2 * C^2 + ((d:ℝ) + 2*ν)^2 * S^2) * py
    have ecP1 : 2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))
        + ((d:ℝ) - 1) / (S * C) * (-4 * S * C) = 4 * (ν - α - (α + ν + 2) * (2 * C ^ 2 - 1)) := by
      rw [hα, hbν]
      field_simp
      linear_combination (2 + 2 * (d:ℝ) + 4 * ν) * py
    have eh : (-4 * S * C)^2 = 4 * (1 - (2 * C ^ 2 - 1) ^ 2) := by
      linear_combination (16 * C^2) * py
    have key : χ0 * (((l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2)) * Q0
          + (2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))) * Q1
          + (-4 * S * C)^2 * Q2)
        + ((d:ℝ) - 1) / (S * C) * (χ0 * ((l * C / S - b * S / C) * Q0 + (-4 * S * C) * Q1))
        + (b + 2*n + l)^2 * (χ0 * Q0) - l * (l + d - 2) / S^2 * (χ0 * Q0) - b * (b - d) / C^2 * (χ0 * Q0)
        = χ0 * (((l * C / S - b * S / C)^2 + (-l / S^2 - b / C^2) + ((d:ℝ) - 1) / (S * C) * (l * C / S - b * S / C)
        + (b + 2*n + l)^2 - l * (l + d - 2) / S^2 - b * (b - d) / C^2) * Q0
          + (2 * (l * C / S - b * S / C) * (-4 * S * C) + (-4 * (C^2 - S^2))
        + ((d:ℝ) - 1) / (S * C) * (-4 * S * C)) * Q1 + (-4 * S * C)^2 * Q2) := by ring
    rw [key, ecP, ecP1, eh]
    linear_combination (4 * χ0) * jac

end GDRad



namespace GDNorm

lemma asym (d : ℕ) (m R : ℝ) (n l : ℕ) :
    ∃ k : ℝ, k ≠ 0 ∧
      Tendsto (fun r => modeRadial d m R n l r / cos r ^ twoHPlus d m R) (𝓝[<] (π / 2)) (𝓝 k) := by
  set α : ℝ := (l : ℝ) + (d : ℝ) / 2 - 1
  set ν := nu d m R
  have hν : 0 ≤ ν := by simp only [ν, nu]; positivity
  have hP : jacobiP n α ν (-1) = gbinom (n + ν) n * (-1) ^ n := by
    unfold jacobiP
    rw [Finset.sum_eq_single n]
    · simp [gbinom]; left; norm_num
    · intro s hs hsn
      have : n - s ≠ 0 := by
        have := Finset.mem_range.1 hs; omega
      simp [zero_pow this]
    · intro h; exact absurd (Finset.self_mem_range_succ n) h
  have hg : 0 < gbinom (n + ν) n := by
    unfold gbinom
    apply div_pos _ (by positivity)
    apply descPochhammer_pos
    linarith
  refine ⟨jacobiP n α ν (-1), ?_, ?_⟩
  · rw [hP]; exact mul_ne_zero hg.ne' (pow_ne_zero _ (by norm_num))
  have hcont : Continuous (fun r : ℝ => sin r ^ l * jacobiP n α ν (cos (2 * r))) := by
    unfold jacobiP; fun_prop
  have hlim := (hcont.tendsto (π / 2)).mono_left (nhdsWithin_le_nhds (s := Set.Iio (π/2)))
  have h2 : 2 * (π / 2) = π := by ring
  simp only [sin_pi_div_two, h2, cos_pi, one_pow, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity)] with r hr
  have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
  have hb : 0 < cos r ^ twoHPlus d m R := rpow_pos_of_pos hc _
  simp only [modeRadial, α, ν]
  field_simp

lemma normalizable (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (n l : ℕ) :
    IsNormalizableMode d m R (omegaNL d m R n l) l (modeRadial d m R n l) := by
  set b := twoHPlus d m R with hb
  set ν := nu d m R with hνdef
  have hν : 0 ≤ ν := by simp only [ν, nu]; positivity
  set α : ℝ := (l:ℝ) + (d:ℝ)/2 - 1
  have hPc : Continuous (fun r : ℝ => jacobiP n α ν (cos (2 * r))) := by
    unfold jacobiP; fun_prop
  refine ⟨GDRad.radial d m R n l, ?_, ?_, ?_⟩
  · obtain ⟨k, hk, hlim⟩ := asym d m R n l
    have hev : ∀ᶠ r in 𝓝[<] (π / 2), modeRadial d m R n l r / cos r ^ b ≠ 0 :=
      hlim.eventually (isOpen_ne.mem_nhds hk)
    have hev2 := hev.and (Ioo_mem_nhdsLT (show (0:ℝ) < π / 2 by positivity))
    obtain ⟨r, hr1, hr2⟩ := hev2.exists
    refine ⟨r, hr2, fun h => hr1 ?_⟩
    simp [h]
  · -- bounded near the origin
    have hcont : ContinuousOn (fun r => |modeRadial d m R n l r|) (Set.Icc 0 (π / 4)) := by
      apply ContinuousOn.abs
      unfold modeRadial
      intro r hr
      have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], by linarith [hr.2, pi_pos]⟩
      apply ContinuousAt.continuousWithinAt
      refine ((continuous_sin.pow l).continuousAt.mul ?_).mul hPc.continuousAt
      exact (Real.continuousAt_rpow_const _ _ (Or.inl hc.ne')).comp continuous_cos.continuousAt
    exact ((isCompact_Icc.image_of_continuousOn hcont).bddAbove).mono
      (Set.image_mono Set.Ioc_subset_Icc_self)
  · -- finite KG norm
    unfold HasFiniteKGNorm
    set G : ℝ → ℝ := fun r => sin r ^ (d - 1 + 2 * l) * cos r ^ (2 * ν + 1) *
      jacobiP n α ν (cos (2 * r)) ^ 2
    have hG : Continuous G := by
      have : Continuous (fun r : ℝ => cos r ^ (2 * ν + 1)) :=
        (Real.continuous_rpow_const (by linarith)).comp continuous_cos
      exact ((continuous_sin.pow _).mul this).mul (hPc.pow 2)
    have hint : IntegrableOn G (Set.Ioo 0 (π / 2)) :=
      (hG.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    refine hint.congr_fun (fun r hr => ?_) measurableSet_Ioo
    have hc : 0 < cos r := cos_pos_of_mem_Ioo ⟨by linarith [hr.1, pi_pos], hr.2⟩
    have e1 : (cos r ^ b) ^ 2 = (cos r) ^ (d - 1) * cos r ^ (2 * ν + 1) := by
      rw [← rpow_natCast (cos r ^ b), ← rpow_mul hc.le, ← rpow_natCast (cos r), ← rpow_add hc]
      congr 1
      rw [Nat.cast_sub (by omega)]; simp only [hb, twoHPlus, ν]; push_cast; ring
    simp only [G, modeRadial, tan_eq_sin_div_cos, div_pow]
    rw [mul_pow, mul_pow, e1, pow_add, pow_mul]
    field_simp
    have hαe : α = (2 * (l:ℝ) + d - 2) / 2 := by simp only [α]; ring
    rw [hαe, ← pow_mul, ← pow_mul, mul_comm 2 l]

end GDNorm

open Real Filter Topology in
theorem solution (d : ℕ) (hd : 2 ≤ d) (m R : ℝ) (hR : 0 < R) (n l : ℕ) :
    IsNormalizableMode d m R (omegaNL d m R n l) l (modeRadial d m R n l) :=
  GDNorm.normalizable d hd m R n l
