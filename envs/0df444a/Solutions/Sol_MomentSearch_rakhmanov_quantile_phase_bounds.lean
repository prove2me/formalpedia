-- Prove2me | solution 1 for MomentSearch.rakhmanov_quantile_phase_bounds
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:42:37.7611+00:00
-- url     : https://prove2.me/submissions/79b2ca79-b3f4-4ad2-8787-830478a98dd9

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_half_mass_cell

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    ∀ x ∈ Set.Ioo (-r) r, ∃ M y : ℝ,
      y ∈ Set.Ioo (-r) r ∧ f y = 0 ∧ 0 < M ∧ M ≤ (N : ℝ) / 2 ∧
      |x-y| ≤ 2/M ∧ ρ x ≤ M ∧
      let q : ℝ → ℝ := fun z => if z = y then Real.pi * ρ y else |f z| / |z-y|
      M / 4 ≤ q x ∧ ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        q z * max 1 (M * |z-y|) ≤ 4*M := by
  intro r ρ f x hx
  obtain ⟨a,b,y,p,m,hy,hyc,hxc,htail,ha,hb,hconc,hmax,hpeak⟩ :=
    MomentSearch.rakhmanov_half_mass_cell N k hk hkN x hx
  change ConcaveOn ℝ (Set.Icc a b) ρ at hconc
  let M := ρ p
  change M ≤ 2 * ρ y at hpeak
  change ∀ z ∈ Set.Icc a b, ρ z ≤ M at hmax
  let I := fun u v : ℝ => ∫ t in u..v, ρ t
  change I y 1 = (m : ℝ) + 1/2 at htail
  change I a y = 1/2 at ha
  change I y b = 1/2 at hb
  have cont : Continuous ρ := by dsimp [ρ]; fun_prop
  have add (u v z : ℝ) : I u v + I v z = I u z :=
    intervalIntegral.integral_add_adjacent_intervals (cont.intervalIntegrable ..) (cont.intervalIntegrable ..)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have nn (z : ℝ) : 0 ≤ ρ z := by
    dsimp [ρ]
    exact mul_nonneg (by positivity) (Real.arctan_nonneg.mpr (by positivity))
  have nonneg {u v : ℝ} (huv : u ≤ v) : 0 ≤ I u v :=
    intervalIntegral.integral_nonneg_of_forall huv nn
  have cap : M ≤ (N : ℝ)/2 := by
    dsimp [M,ρ]
    have hh := mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two
      ((N : ℝ)/k * Real.sqrt (r^2-p^2))).le (show 0 ≤ (N : ℝ)/Real.pi by positivity)
    calc
      _ ≤ _ := hh
      _ = _ := by field_simp
  have cell {u v : ℝ} (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
      |I u v| ≤ M * |v-u| := by
    change ‖∫ t in u..v, ρ t‖ ≤ _
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (nn t)]
    exact hmax t ⟨(le_min hu.1 hv.1).trans ht.1.le, ht.2.trans (max_le hu.2 hv.2)⟩
  have left := cell ⟨le_rfl,hyc.1.trans hyc.2⟩ hyc
  have right := cell hyc ⟨hyc.1.trans hyc.2,le_rfl⟩
  rw [ha, abs_of_pos (by norm_num), abs_of_nonneg (sub_nonneg.mpr hyc.1)] at left
  rw [hb, abs_of_pos (by norm_num), abs_of_nonneg (sub_nonneg.mpr hyc.2)] at right
  have hM : 0 < M := by
    by_contra! hh
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hh (sub_nonneg.mpr hyc.1)]
  have half : |I x y| ≤ 1/2 := by
    rw [abs_le]
    constructor
    · linarith [add x y b, nonneg hxc.2]
    · linarith [add a x y, nonneg hxc.1]
  have chord : M * |x-y| ≤ 4 * |I x y| := by
    let g := fun s : ℝ => ρ ((y-x)*s+x)
    have hi : (∫ s in (0:ℝ)..1, s * ρ y) ≤ ∫ s in (0:ℝ)..1, g s := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (Continuous.intervalIntegrable (by fun_prop) ..)
        (Continuous.intervalIntegrable (by dsimp [g]; fun_prop) ..)
      intro s hs
      have h := hconc.2 hxc hyc (sub_nonneg.mpr hs.2) hs.1 (show 1-s+s=1 by ring)
      simp only [smul_eq_mul] at h
      dsimp [g]
      rw [show (y-x)*s+x = (1-s)*x+s*y by ring]
      linarith [mul_nonneg (sub_nonneg.mpr hs.2) (nn x)]
    rw [intervalIntegral.integral_mul_const, integral_id] at hi
    norm_num at hi
    have he := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1) ρ (y-x) x
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] at he
    change (y-x) * (∫ s in (0:ℝ)..1, g s) = I x y at he
    rw [← he, abs_mul, abs_sub_comm x y]
    have hn := le_abs_self (∫ s in (0:ℝ)..1, g s)
    nlinarith [mul_nonneg (abs_nonneg (y-x)) (show 0 ≤ 4*|∫ s in (0:ℝ)..1, g s|-M by linarith)]
  have close : |x-y| ≤ 2/M := (le_div_iff₀ hM).mpr (by linarith)
  have zero : f y = 0 := by
    change Real.cos (Real.pi * I y 1) = 0
    apply Real.cos_eq_zero_iff.mpr
    exact ⟨m, by rw [htail]; ring⟩
  have phase (z : ℝ) : |f z| = |Real.sin (Real.pi * I z y)| := by
    have hsin : |Real.sin (Real.pi * I y 1)| = 1 := by
      change Real.cos (Real.pi * I y 1) = 0 at zero
      rcases Real.cos_eq_zero_iff_sin_eq.mp zero with h | h <;> simp [h]
    change |Real.cos (Real.pi * I z 1)| = _
    rw [← add z y 1, mul_add, Real.cos_add]
    change |Real.cos _ * f y - _| = _
    rw [zero, mul_zero, zero_sub, abs_neg, abs_mul, hsin, mul_one]
  refine ⟨M,y,hy,zero,hM,cap,close,hmax _ hxc,?_,?_⟩
  · dsimp only
    split_ifs with h
    · nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (nn y)]
    · apply (le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr h))).2
      rw [phase]
      have harg : |Real.pi * I x y| ≤ Real.pi/2 := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        nlinarith [mul_le_mul_of_nonneg_left half Real.pi_pos.le]
      have hl := Real.mul_abs_le_abs_sin harg
      rw [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero] at hl
      linarith [abs_nonneg (I x y)]
  · intro z hz
    dsimp only
    split_ifs with h
    · subst z
      simp only [sub_self, abs_zero, mul_zero, max_eq_left (by norm_num : (0:ℝ) ≤ 1), mul_one]
      nlinarith [mul_le_mul_of_nonneg_left (hmax y hyc) Real.pi_pos.le,
        mul_le_mul_of_nonneg_right Real.pi_lt_four.le hM.le]
    · have hd := abs_pos.mpr (sub_ne_zero.mpr h)
      have hone : |f z| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
      have localBound : |f z| / |z-y| ≤ 4*M := by
        apply (div_le_iff₀ hd).2
        by_cases hc : z ∈ Set.Icc a b
        · rw [phase]
          have hs := Real.abs_sin_le_abs (x := Real.pi * I z y)
          rw [abs_mul, abs_of_pos Real.pi_pos] at hs
          have hh := cell hc hyc
          rw [abs_sub_comm y z] at hh
          nlinarith [mul_le_mul_of_nonneg_left hh Real.pi_pos.le,
            mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) (mul_nonneg hM.le hd.le)]
        · rcases lt_or_ge z a with hza | hza
          · rw [abs_of_neg (by linarith [hyc.1] : z-y < 0)]
            nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hza.le)]
          · have hbz : b < z := lt_of_not_ge (fun h => hc ⟨hza,h⟩)
            rw [abs_of_pos (by linarith [hyc.2] : 0 < z-y)]
            nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hbz.le)]
      rcases le_total (M*|z-y|) 1 with hnear | hfar
      · simpa [max_eq_left hnear] using localBound
      · rw [max_eq_right hfar, mul_comm M, ← mul_assoc, div_mul_cancel₀ _ hd.ne']
        nlinarith [mul_le_mul_of_nonneg_right hone hM.le]
