-- Prove2me | solution 1 for LogRegretOCO.ONS.exp_concave_quadratic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:50.686904+00:00
-- url     : https://prove2.me/submissions/efa537fe-fb3e-46c2-aafc-b34190678bda

import Mathlib
open scoped RealInnerProductSpace

private theorem log_lb (u : ℝ) (hu : |u| ≤ 1 / 4) : u + u ^ 2 / 4 ≤ -Real.log (1 - u) := by
  have ha0 : (0:ℝ) ≤ |u| := abs_nonneg u
  have habs : |u| < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 3
  have hsum : (∑ i ∈ Finset.range 3, u ^ (i + 1) / ((i : ℝ) + 1)) = u + u ^ 2 / 2 + u ^ 3 / 3 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum] at h
  have h1 : u + u ^ 2 / 2 + u ^ 3 / 3 + Real.log (1 - u) ≤ |u| ^ 4 / (1 - |u|) :=
    le_trans (le_abs_self _) h
  have hden : (0:ℝ) < 1 - |u| := by linarith
  have hb1 : |u| ^ 4 / (1 - |u|) ≤ (4 / 3) * |u| ^ 4 := by
    rw [div_le_iff₀ hden]
    nlinarith [pow_nonneg ha0 4, mul_le_mul_of_nonneg_left hu (pow_nonneg ha0 4)]
  have hc1 : (0:ℝ) ≤ 1 / 4 - (4 / 3) * |u| ^ 2 - |u| / 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hu ha0]
  have hb2 : (4 / 3) * |u| ^ 4 + |u| ^ 3 / 3 ≤ |u| ^ 2 / 4 := by
    nlinarith [mul_nonneg (pow_nonneg ha0 2) hc1]
  have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have hu3 : -(|u| ^ 3) ≤ u ^ 3 := by
    rcases abs_cases u with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; nlinarith [pow_nonneg ha0 3]
    · rw [he]; nlinarith
  linarith

/-- Lemma 3 of Hazan–Agarwal–Kale: the quadratic lower bound for exp-concave functions. -/
private theorem ec_core {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (G D α β : ℝ) (hG : 0 < G) (hD : 0 < D)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ x ∈ P, DifferentiableAt ℝ f x)
    (hgrad : ∀ x ∈ P, ‖gradient f x‖ ≤ G)
    (hexp : ConcaveOn ℝ P (fun x => Real.exp (-α * f x)))
    (hβ_pos : 0 < β) (hβ : β ≤ (1 / 2) * min (1 / (4 * G * D)) α) :
    ∀ x ∈ P, ∀ y ∈ P,
      f y + (inner ℝ (gradient f y) (x - y) : ℝ)
        + (β / 2) * (inner ℝ (gradient f y) (x - y) : ℝ) ^ 2 ≤ f x := by
  have hPconv : Convex ℝ P := hexp.1
  have hmin1 : (1 / 2) * min (1 / (4 * G * D)) α ≤ (1 / 2) * α :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
  have hα : 0 < α := by
    have : β ≤ (1 / 2) * α := le_trans hβ hmin1
    linarith
  have h2βα : 2 * β ≤ α := by
    have : β ≤ (1 / 2) * α := le_trans hβ hmin1
    linarith
  have hGD : β ≤ 1 / (8 * G * D) := by
    have h1 : β ≤ (1 / 2) * (1 / (4 * G * D)) :=
      le_trans hβ (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    have h2 : (1 / 2) * (1 / (4 * G * D)) = 1 / (8 * G * D) := by
      field_simp
      ring
    linarith [h2 ▸ h1]
  -- `exp (-2β f)` is concave on `P`
  set c : ℝ := 2 * β / α with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one hα]
    exact h2βα
  have hpow : ∀ w, Real.exp (-(2 * β) * f w) = (Real.exp (-α * f w)) ^ c := by
    intro w
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, hc]
    congr 1
    field_simp
  have hconc2 : ConcaveOn ℝ P (fun w => Real.exp (-(2 * β) * f w)) := by
    refine ⟨hPconv, ?_⟩
    intro a ha b hb s t hs ht hst
    have h1 : s • Real.exp (-α * f a) + t • Real.exp (-α * f b)
        ≤ Real.exp (-α * f (s • a + t • b)) := hexp.2 ha hb hs ht hst
    have hEa : (0:ℝ) ≤ Real.exp (-α * f a) := (Real.exp_pos _).le
    have hEb : (0:ℝ) ≤ Real.exp (-α * f b) := (Real.exp_pos _).le
    have h3 : s • (Real.exp (-α * f a)) ^ c + t • (Real.exp (-α * f b)) ^ c
        ≤ (s • Real.exp (-α * f a) + t • Real.exp (-α * f b)) ^ c :=
      (Real.concaveOn_rpow hc0.le hc1).2 (Set.mem_Ici.mpr hEa) (Set.mem_Ici.mpr hEb) hs ht hst
    have h4 : (s • Real.exp (-α * f a) + t • Real.exp (-α * f b)) ^ c
        ≤ (Real.exp (-α * f (s • a + t • b))) ^ c := by
      refine Real.rpow_le_rpow ?_ h1 hc0.le
      simp only [smul_eq_mul]
      positivity
    simp only [hpow]
    simp only [smul_eq_mul] at h3 h4 ⊢
    linarith
  -- the tangent inequality for a concave function
  intro x hx y hy
  set Dy : ℝ := (inner ℝ (gradient f y) (x - y) : ℝ) with hDy
  have hDfd : Dy = fderiv ℝ f y (x - y) := by
    rw [hDy]
    exact inner_gradient_left
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => y + t • (x - y) with hγ
  have hγ0 : γ 0 = y := by simp [hγ]
  have hγ1 : γ 1 = x := by simp [hγ]
  have hγconv : ∀ t : ℝ, γ t = (1 - t) • y + t • x := by
    intro t
    simp only [hγ]
    module
  have hderiv : HasDerivAt (fun t : ℝ => Real.exp (-(2 * β) * f (γ t)))
      (Real.exp (-(2 * β) * f y) * (-(2 * β) * Dy)) 0 := by
    have h1 : HasDerivAt γ (x - y) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).smul_const (x - y)).const_add y
      simpa [hγ] using this
    have h2 : HasFDerivAt f (fderiv ℝ f y) (γ 0) := by
      rw [hγ0]
      exact (hdiff y hy).hasFDerivAt
    have h3 : HasDerivAt (fun t : ℝ => f (γ t)) (fderiv ℝ f y (x - y)) 0 :=
      h2.comp_hasDerivAt 0 h1
    have h4 : HasDerivAt (fun t : ℝ => -(2 * β) * f (γ t))
        (-(2 * β) * fderiv ℝ f y (x - y)) 0 := h3.const_mul _
    have h5 := h4.exp
    rw [hγ0] at h5
    rw [hDfd]
    exact h5
  have hslope : Real.exp (-(2 * β) * f x) - Real.exp (-(2 * β) * f y)
      ≤ Real.exp (-(2 * β) * f y) * (-(2 * β) * Dy) := by
    have htend := (hasDerivAt_iff_tendsto_slope.mp hderiv)
    have hmono : (nhdsWithin (0:ℝ) (Set.Ioi 0)) ≤ nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ := by
      refine nhdsWithin_mono _ ?_
      intro t ht
      exact ne_of_gt ht
    have htend' : Filter.Tendsto (slope (fun t : ℝ => Real.exp (-(2 * β) * f (γ t))) 0)
        (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (Real.exp (-(2 * β) * f y) * (-(2 * β) * Dy))) := htend.mono_left hmono
    refine ge_of_tendsto htend' ?_
    have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < 1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    have hev0 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), (0:ℝ) < t :=
      eventually_mem_nhdsWithin
    filter_upwards [hev, hev0] with t ht ht0
    have ht0' : (0:ℝ) < t := ht0
    have htne : t ≠ 0 := ne_of_gt ht0'
    have hmemP : γ t ∈ P := by
      rw [hγconv t]
      exact hPconv hy hx (by linarith) ht0'.le (by ring)
    have hcc : (1 - t) • Real.exp (-(2 * β) * f y) + t • Real.exp (-(2 * β) * f x)
        ≤ Real.exp (-(2 * β) * f (γ t)) := by
      have h := hconc2.2 hy hx (by linarith : (0:ℝ) ≤ 1 - t) ht0'.le (by ring)
      rw [← hγconv t] at h
      exact h
    simp only [smul_eq_mul] at hcc
    have hsl : slope (fun s : ℝ => Real.exp (-(2 * β) * f (γ s))) 0 t
        = (Real.exp (-(2 * β) * f (γ t)) - Real.exp (-(2 * β) * f (γ 0))) / t := by
      rw [slope_def_field, div_eq_div_iff (by intro h; exact htne (by linarith)) htne]
      ring
    rw [hsl, hγ0, le_div_iff₀ ht0']
    nlinarith [hcc]
  -- turn the tangent inequality into the claim
  set u : ℝ := 2 * β * Dy with hu
  have hEx : (0:ℝ) < Real.exp (-(2 * β) * f x) := Real.exp_pos _
  have hEy : (0:ℝ) < Real.exp (-(2 * β) * f y) := Real.exp_pos _
  have hstep : Real.exp (-(2 * β) * f x) ≤ Real.exp (-(2 * β) * f y) * (1 - u) := by
    rw [hu]; nlinarith [hslope]
  have h1u : (0:ℝ) < 1 - u := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hstep, hEx, hEy]
  have hexpdiff : Real.exp (-(2 * β) * f x - -(2 * β) * f y) ≤ 1 - u := by
    rw [Real.exp_sub]
    rw [div_le_iff₀ hEy]
    linarith [hstep]
  have hlog : -(2 * β) * f x - -(2 * β) * f y ≤ Real.log (1 - u) :=
    (Real.le_log_iff_exp_le h1u).mpr hexpdiff
  -- the size of `u`
  have hDybd : |Dy| ≤ G * D := by
    have h1 : |Dy| ≤ ‖gradient f y‖ * ‖x - y‖ := by
      rw [hDy]
      exact abs_real_inner_le_norm _ _
    have h2 : ‖gradient f y‖ ≤ G := hgrad y hy
    have h3 : ‖x - y‖ ≤ D := hdiam x hx y hy
    have h4 : ‖gradient f y‖ * ‖x - y‖ ≤ G * D :=
      mul_le_mul h2 h3 (norm_nonneg _) hG.le
    linarith
  have hubd : |u| ≤ 1 / 4 := by
    rw [hu, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * β)]
    have h1 : 2 * β * |Dy| ≤ 2 * β * (G * D) :=
      mul_le_mul_of_nonneg_left hDybd (by linarith)
    have h2 : 2 * β * (G * D) ≤ 1 / 4 := by
      have h3 : β * (8 * G * D) ≤ 1 := by
        have h4 : (0:ℝ) < 8 * G * D := by positivity
        rw [← le_div_iff₀ h4]
        exact hGD
      nlinarith [h3]
    linarith
  have hlb := log_lb u hubd
  -- assemble
  have hfinal : u + u ^ 2 / 4 ≤ (2 * β) * (f x - f y) := by
    have : -(2 * β) * f x - -(2 * β) * f y = -((2 * β) * (f x - f y)) := by ring
    rw [this] at hlog
    linarith
  rw [hu] at hfinal
  have h2β : (0:ℝ) < 2 * β := by linarith
  have hkey : 2 * β * (Dy + (β / 2) * Dy ^ 2) ≤ 2 * β * (f x - f y) := by
    have he : 2 * β * (Dy + (β / 2) * Dy ^ 2) = 2 * β * Dy + (2 * β * Dy) ^ 2 / 4 := by ring
    rw [he]
    exact hfinal
  have hfin := le_of_mul_le_mul_left hkey h2β
  linarith

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (G D α β : ℝ) (hG : 0 < G) (hD : 0 < D)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ x ∈ P, DifferentiableAt ℝ f x)
    (hgrad : ∀ x ∈ P, ‖gradient f x‖ ≤ G)
    (hexp : ConcaveOn ℝ P (fun x => Real.exp (-α * f x)))
    (hβ_pos : 0 < β) (hβ : β ≤ (1 / 2) * min (1 / (4 * G * D)) α) :
    ∀ x ∈ P, ∀ y ∈ P,
      f y + ⟪gradient f y, x - y⟫ + (β / 2) * ⟪gradient f y, x - y⟫ ^ 2 ≤ f x :=
  ec_core P G D α β hG hD hdiam f hdiff hgrad hexp hβ_pos hβ
