-- Prove2me | solution 1 for Multihoming.Hump.proposition3_hump_shaped
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T12:27:09.483728+00:00
-- url     : https://prove2.me/submissions/6125d3f4-c21d-4a7d-beb3-529caade01a2

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

set_option autoImplicit false

namespace HumpAux

open Set

lemma hump_of_deriv {f f' : ℝ → ℝ} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Ioo a c, 0 < f' x) (hneg : ∀ x ∈ Ioo c b, f' x < 0) :
    StrictMonoOn f (Icc a c) ∧ StrictAntiOn f (Icc c b) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc a c)
    · intro x hx
      exact (hd x ⟨hx.1, hx.2.trans hcb.le⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x ⟨hx.1.le, (hx.2.trans hcb).le⟩).deriv]
      exact hpos x hx
  · apply strictAntiOn_of_deriv_neg (convex_Icc c b)
    · intro x hx
      exact (hd x ⟨hac.le.trans hx.1, hx.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x ⟨(hac.trans hx.1).le, hx.2.le⟩).deriv]
      exact hneg x hx

lemma pM_hasDerivAt (t e x : ℝ) (hx : x < 2 * t) :
    HasDerivAt (fun μ => Multihoming.Thresholds.pM t μ e)
      ((2 * t ^ 2 - 4 * t * x + x ^ 2 - t * e) / (2 * t - x) ^ 2) x := by
  have hne : 2 * t - x ≠ 0 := by linarith
  have h1 : HasDerivAt (fun μ : ℝ => t - μ) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub t
  have h2 : HasDerivAt (fun μ : ℝ => μ + e) 1 x := by
    simpa using (hasDerivAt_id x).add_const e
  have h3 : HasDerivAt (fun μ : ℝ => 2 * t - μ) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (2 * t)
  have h : HasDerivAt (fun μ : ℝ => (t - μ) * (μ + e) / (2 * t - μ))
      ((((-1) * (x + e) + (t - x) * 1) * (2 * t - x) - (t - x) * (x + e) * (-1)) /
        (2 * t - x) ^ 2) x := (h1.mul h2).div h3 hne
  have hf : (fun μ => Multihoming.Thresholds.pM t μ e)
      = fun μ : ℝ => (t - μ) * (μ + e) / (2 * t - μ) := rfl
  rw [hf]
  refine h.congr_deriv ?_
  field_simp
  ring

lemma piM_hasDerivAt (t e x : ℝ) (hx0 : -t < x) (hx : x < 2 * t) :
    HasDerivAt (fun μ => Multihoming.Hump.piM t μ e)
      (2 * t * (e + x) * (-(t + e) * x ^ 2 - t * (2 * t - e) * x + t ^ 2 * (2 * t - e)) /
        ((t + x) ^ 2 * (2 * t - x) ^ 3)) x := by
  have hne1 : t + x ≠ 0 := by linarith
  have hne2 : 2 * t - x ≠ 0 := by linarith
  have hne : (t + x) * ((2 * t - x) * (2 * t - x)) ≠ 0 :=
    mul_ne_zero hne1 (mul_ne_zero hne2 hne2)
  have hA : HasDerivAt (fun μ : ℝ => t * (t - μ)) (t * (-1)) x := by
    simpa using ((hasDerivAt_id x).const_sub t).const_mul t
  have hE : HasDerivAt (fun μ : ℝ => e + μ) 1 x := by
    simpa using (hasDerivAt_id x).const_add e
  have hF : HasDerivAt (fun μ : ℝ => 2 * t - μ) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (2 * t)
  have hD : HasDerivAt (fun μ : ℝ => t + μ) 1 x := by
    simpa using (hasDerivAt_id x).const_add t
  have hB : HasDerivAt (fun μ : ℝ => (e + μ) * (e + μ)) (1 * (e + x) + (e + x) * 1) x :=
    hE.mul hE
  have hC : HasDerivAt (fun μ : ℝ => (2 * t - μ) * (2 * t - μ))
      ((-1) * (2 * t - x) + (2 * t - x) * (-1)) x := hF.mul hF
  have hN : HasDerivAt (fun μ : ℝ => t * (t - μ) * ((e + μ) * (e + μ)))
      (t * (-1) * ((e + x) * (e + x)) + t * (t - x) * (1 * (e + x) + (e + x) * 1)) x :=
    hA.mul hB
  have hQ : HasDerivAt (fun μ : ℝ => (t + μ) * ((2 * t - μ) * (2 * t - μ)))
      (1 * ((2 * t - x) * (2 * t - x)) + (t + x) * ((-1) * (2 * t - x) + (2 * t - x) * (-1))) x :=
    hD.mul hC
  have h := hN.div hQ hne
  have hf : (fun μ => Multihoming.Hump.piM t μ e)
      = fun μ : ℝ => t * (t - μ) * ((e + μ) * (e + μ)) / ((t + μ) * ((2 * t - μ) * (2 * t - μ))) := by
    funext μ; unfold Multihoming.Hump.piM; ring
  rw [hf]
  refine h.congr_deriv ?_
  field_simp
  ring

end HumpAux

open Multihoming.Hump in
theorem solution (t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    (∃ μp ∈ Set.Ioo 0 t,
        StrictMonoOn (fun μ => Multihoming.Thresholds.pM t μ e) (Set.Icc 0 μp) ∧
        StrictAntiOn (fun μ => Multihoming.Thresholds.pM t μ e) (Set.Icc μp t)) ∧
    (∃ μπ ∈ Set.Ioo 0 t,
        StrictMonoOn (fun μ => piM t μ e) (Set.Icc 0 μπ) ∧
        StrictAntiOn (fun μ => piM t μ e) (Set.Icc μπ t)) := by
  constructor
  · -- price: peak at 2t - √(2t² + te)
    set s := Real.sqrt (2 * t ^ 2 + t * e) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hss : s ^ 2 = 2 * t ^ 2 + t * e := Real.sq_sqrt (by positivity)
    have hslt : s < 2 * t := by nlinarith
    have hsgt : t < s := by nlinarith
    refine ⟨2 * t - s, ⟨by linarith, by linarith⟩, ?_⟩
    refine HumpAux.hump_of_deriv (f' := fun x =>
      (2 * t ^ 2 - 4 * t * x + x ^ 2 - t * e) / (2 * t - x) ^ 2) (by linarith) (by linarith)
      (fun x hx => HumpAux.pM_hasDerivAt t e x (by linarith [hx.2])) ?_ ?_
    · intro x hx
      have hd : 0 < (2 * t - x) ^ 2 := pow_pos (by linarith [hx.2]) 2
      apply div_pos _ hd
      have : 2 * t ^ 2 - 4 * t * x + x ^ 2 - t * e = (2 * t - s - x) * (2 * t + s - x) := by
        linear_combination hss
      rw [this]
      apply mul_pos <;> linarith [hx.2]
    · intro x hx
      have hd : 0 < (2 * t - x) ^ 2 := pow_pos (by linarith [hx.2]) 2
      apply div_neg_of_neg_of_pos _ hd
      have : 2 * t ^ 2 - 4 * t * x + x ^ 2 - t * e = (2 * t - s - x) * (2 * t + s - x) := by
        linear_combination hss
      rw [this]
      apply mul_neg_of_neg_of_pos <;> linarith [hx.1, hx.2]
  · -- profit: peak at r₁
    set S := Real.sqrt (3 * (4 * t ^ 2 - e ^ 2)) with hS
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hSS : S ^ 2 = 3 * (4 * t ^ 2 - e ^ 2) := Real.sq_sqrt (by nlinarith)
    have hte : 0 < e + t := by linarith
    have hSgt : 2 * t - e < S := by nlinarith
    have hSlt : S < 4 * t + e := by nlinarith
    set r := (t * S - 2 * t ^ 2 + e * t) / (2 * (e + t)) with hr
    have hr0 : 0 < r := by
      rw [hr]; apply div_pos _ (by linarith); nlinarith
    have hrt : r < t := by
      rw [hr, div_lt_iff₀ (by linarith)]; nlinarith
    have hM : -(t + e) * r ^ 2 - t * (2 * t - e) * r + t ^ 2 * (2 * t - e) = 0 := by
      have h2 : 2 * (e + t) * r = t * S - 2 * t ^ 2 + e * t := by
        rw [hr]; field_simp
      have hM2 : (-(t + e) * r ^ 2 - t * (2 * t - e) * r + t ^ 2 * (2 * t - e)) *
          (2 * (e + t)) ^ 2 = 0 := by
        have e1 : (-(t + e) * r ^ 2 - t * (2 * t - e) * r + t ^ 2 * (2 * t - e)) *
            (2 * (e + t)) ^ 2 = -(t + e) * (2 * (e + t) * r) ^ 2
              - t * (2 * t - e) * (2 * (e + t) * r) * (2 * (e + t))
              + t ^ 2 * (2 * t - e) * (2 * (e + t)) ^ 2 := by ring
        rw [e1, h2]
        linear_combination (-(t + e) * t ^ 2) * hSS
      have hD2 : (2 * (e + t)) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
      exact (mul_eq_zero.mp hM2).resolve_right hD2
    have hfac : ∀ x : ℝ, -(t + e) * x ^ 2 - t * (2 * t - e) * x + t ^ 2 * (2 * t - e)
        = (r - x) * ((t + e) * (x + r) + t * (2 * t - e)) := by
      intro x; linear_combination hM
    refine ⟨r, ⟨hr0, hrt⟩, ?_⟩
    refine HumpAux.hump_of_deriv (f' := fun x =>
      2 * t * (e + x) * (-(t + e) * x ^ 2 - t * (2 * t - e) * x + t ^ 2 * (2 * t - e)) /
        ((t + x) ^ 2 * (2 * t - x) ^ 3)) hr0 hrt
      (fun x hx => HumpAux.piM_hasDerivAt t e x (by linarith [hx.1]) (by linarith [hx.2])) ?_ ?_
    · intro x hx
      have h1 : 0 < t + x := by linarith [hx.1]
      have h2 : 0 < 2 * t - x := by linarith [hx.2]
      have hd : 0 < (t + x) ^ 2 * (2 * t - x) ^ 3 := mul_pos (pow_pos h1 2) (pow_pos h2 3)
      apply div_pos _ hd
      rw [hfac x]
      have h3 : 0 < e + x := by linarith [hx.1]
      have h4 : 0 < r - x := by linarith [hx.2]
      have h5 : 0 < (t + e) * (x + r) + t * (2 * t - e) := by nlinarith [hx.1]
      exact mul_pos (mul_pos (by linarith) h3) (mul_pos h4 h5)
    · intro x hx
      have h1 : 0 < t + x := by linarith [hx.1]
      have h2 : 0 < 2 * t - x := by linarith [hx.2]
      have hd : 0 < (t + x) ^ 2 * (2 * t - x) ^ 3 := mul_pos (pow_pos h1 2) (pow_pos h2 3)
      apply div_neg_of_neg_of_pos _ hd
      rw [hfac x]
      have h3 : 0 < e + x := by linarith [hx.1]
      have h4 : r - x < 0 := by linarith [hx.1]
      have h5 : 0 < (t + e) * (x + r) + t * (2 * t - e) := by nlinarith [hx.1]
      have h6 : 0 < 2 * t * (e + x) := mul_pos (by linarith) h3
      have h7 : (r - x) * ((t + e) * (x + r) + t * (2 * t - e)) < 0 := mul_neg_of_neg_of_pos h4 h5
      nlinarith
