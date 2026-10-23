-- Prove2me | solution 1 for LeveragedPayouts.Unregulated.proposition_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T10:31:57.062163+00:00
-- url     : https://prove2.me/submissions/d0032b90-4b6e-4eec-afb7-83b4c56cbc1e

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

set_option autoImplicit false

namespace P11Aux

open LeveragedPayouts.Unregulated Set Filter Topology

lemma f_cont (E : Economy) : ContinuousOn E.f (Ici 0) := E.hf.2.1

lemma g_cont (E : Economy) : ContinuousOn E.g (Ici 0) := E.hg.2.1

lemma f_diff (E : Economy) {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ E.f x :=
  ((E.hf.2.2.1.differentiableOn (by norm_num)) x hx).differentiableAt (Ioi_mem_nhds hx)

lemma g_diff (E : Economy) {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ E.g x :=
  ((E.hg.2.2.1.differentiableOn one_ne_zero) x hx).differentiableAt (Ioi_mem_nhds hx)

lemma fd_cont (E : Economy) : ContinuousOn (deriv E.f) (Ioi 0) :=
  E.hf.2.2.1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)

lemma gd_cont (E : Economy) : ContinuousOn (deriv E.g) (Ioi 0) :=
  E.hg.2.2.1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl

lemma fd_pos (E : Economy) {x : ℝ} (hx : 0 < x) : 0 < deriv E.f x := E.hf.2.2.2.1 x hx

lemma gd_pos (E : Economy) {x : ℝ} (hx : 0 < x) : 0 < deriv E.g x := E.hg.2.2.2.1 x hx

lemma fd_anti (E : Economy) : StrictAntiOn (deriv E.f) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0) (fd_cont E)
  intro x hx
  rw [interior_Ioi] at hx
  exact E.hf.2.2.2.2.1 x hx

lemma gd_anti (E : Economy) : StrictAntiOn (deriv E.g) (Ioi 0) := E.hg.2.2.2.2.1

lemma f_pos (E : Economy) {x : ℝ} (hx : 0 < x) : 0 < E.f x := by
  have hm : StrictMonoOn E.f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (f_cont E)
    intro y hy
    rw [interior_Ici] at hy
    exact fd_pos E hy
  have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hx.le) hx
  rwa [E.hf.1] at this

lemma R_pos (E : Economy) : 0 < E.R := by linarith [E.hR]

lemma w_pos (E : Economy) : 0 < E.wstar := by
  rw [← E.hw]; exact gd_pos E (by linarith [E.hl1])

lemma fd_ls (E : Economy) : E.π * deriv E.f E.lstar = 2 * E.R * E.wstar := by
  have h := E.h20
  have hR := R_pos E
  rw [E.hw, div_mul_eq_mul_div, div_eq_iff (by positivity)] at h
  linear_combination h

lemma surplus_hasDerivAt (E : Economy) (ρ e : ℝ) {l : ℝ} (h0 : 0 < l) (h1 : l < 1) :
    HasDerivAt (fun x => surplus E ρ e x)
      ((e - e ^ 2 / (2 * E.π)) * deriv E.f l / E.R - ρ * deriv E.g (1 - l)) l := by
  have hf := (f_diff E h0).hasDerivAt
  have hg : HasDerivAt (fun x => E.g (1 - x)) (deriv E.g (1 - l) * (-1)) l := by
    have h1' : HasDerivAt (fun x : ℝ => 1 - x) (-1) l := by
      simpa using (hasDerivAt_id l).const_sub 1
    exact (g_diff E (by linarith)).hasDerivAt.comp l h1'
  have := ((hf.const_mul (e - e ^ 2 / (2 * E.π))).div_const E.R).add (hg.const_mul ρ)
  exact this.congr_deriv (by ring)

lemma surplus_contOn (E : Economy) (ρ e : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ContinuousOn (fun x => surplus E ρ e x) (Icc a b) := by
  unfold surplus
  apply ContinuousOn.add
  · exact (continuousOn_const.mul ((f_cont E).mono (fun x hx => le_trans ha hx.1))).div_const _
  · apply continuousOn_const.mul
    exact (g_cont E).comp (continuousOn_const.sub continuousOn_id)
      (fun x hx => by simp only [mem_Ici, id]; linarith [hx.2])

lemma surplus_lt_of_neg (E : Economy) (ρ e : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hD : ∀ l ∈ Ioo a b,
      (e - e ^ 2 / (2 * E.π)) * deriv E.f l / E.R - ρ * deriv E.g (1 - l) < 0) :
    surplus E ρ e b < surplus E ρ e a := by
  have hanti : StrictAntiOn (fun x => surplus E ρ e x) (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) (surplus_contOn E ρ e ha.le hb)
    intro x hx
    rw [interior_Icc] at hx
    rw [(surplus_hasDerivAt E ρ e (by linarith [hx.1]) (by linarith [hx.2])).deriv]
    exact hD x hx
  exact hanti (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab

lemma surplus_lt_of_pos (E : Economy) (ρ e : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hD : ∀ l ∈ Ioo a b,
      0 < (e - e ^ 2 / (2 * E.π)) * deriv E.f l / E.R - ρ * deriv E.g (1 - l)) :
    surplus E ρ e a < surplus E ρ e b := by
  have hmono : StrictMonoOn (fun x => surplus E ρ e x) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) (surplus_contOn E ρ e ha.le hb)
    intro x hx
    rw [interior_Icc] at hx
    rw [(surplus_hasDerivAt E ρ e (by linarith [hx.1]) (by linarith [hx.2])).deriv]
    exact hD x hx
  exact hmono (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab

lemma phi_pi (E : Economy) : E.π - E.π ^ 2 / (2 * E.π) = E.π / 2 := by
  have := E.hπ0
  field_simp
  ring

lemma phi_le (E : Economy) (e : ℝ) : e - e ^ 2 / (2 * E.π) ≤ E.π / 2 := by
  have hπ := E.hπ0
  have : E.π / 2 - (e - e ^ 2 / (2 * E.π)) = (E.π - e) ^ 2 / (2 * E.π) := by
    field_simp
    ring
  have : 0 ≤ (E.π - e) ^ 2 / (2 * E.π) := by positivity
  linarith

lemma phi_lt (E : Economy) (e : ℝ) (he : e ≠ E.π) : e - e ^ 2 / (2 * E.π) < E.π / 2 := by
  have hπ := E.hπ0
  have : E.π / 2 - (e - e ^ 2 / (2 * E.π)) = (E.π - e) ^ 2 / (2 * E.π) := by
    field_simp
    ring
  have hne : E.π - e ≠ 0 := sub_ne_zero.2 (Ne.symm he)
  have : 0 < (E.π - e) ^ 2 / (2 * E.π) := by positivity
  linarith

lemma phi_mono (E : Economy) {e e' : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ e') (h2 : e' ≤ E.π) :
    e - e ^ 2 / (2 * E.π) ≤ e' - e' ^ 2 / (2 * E.π) := by
  have hπ := E.hπ0
  have : e' - e' ^ 2 / (2 * E.π) - (e - e ^ 2 / (2 * E.π))
      = (e' - e) * (2 * E.π - e - e') / (2 * E.π) := by
    field_simp
    ring
  have : 0 ≤ (e' - e) * (2 * E.π - e - e') / (2 * E.π) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg <;> linarith
  linarith

lemma surplus_le_pi (E : Economy) (ρ e : ℝ) {l : ℝ} (hl : 0 < l) :
    surplus E ρ e l ≤ surplus E ρ E.π l := by
  unfold surplus
  rw [phi_pi]
  have h1 := mul_le_mul_of_nonneg_right (phi_le E e) (f_pos E hl).le
  have h2 := div_le_div_of_nonneg_right h1 (R_pos E).le
  linarith

lemma surplus_mono_e (E : Economy) (ρ : ℝ) {e e' l : ℝ} (h0 : 0 ≤ e) (h1 : e ≤ e') (h2 : e' ≤ E.π)
    (hl : 0 < l) : surplus E ρ e l ≤ surplus E ρ e' l := by
  unfold surplus
  have h1 := mul_le_mul_of_nonneg_right (phi_mono E h0 h1 h2) (f_pos E hl).le
  have h2 := div_le_div_of_nonneg_right h1 (R_pos E).le
  linarith

/-- the root `√(R² - π R f'(l) / (2 w*))` -/
noncomputable def sL (E : Economy) (l : ℝ) : ℝ :=
  Real.sqrt (E.R ^ 2 - E.π * E.R * deriv E.f l / (2 * E.wstar))

noncomputable def eL (E : Economy) (l : ℝ) : ℝ := E.π * E.R / (E.R + sL E l)

noncomputable def rL (E : Economy) (l : ℝ) : ℝ := E.R - sL E l

lemma eL_pos (E : Economy) (l : ℝ) : 0 < eL E l := by
  unfold eL
  have := R_pos E
  have := E.hπ0
  have : 0 ≤ sL E l := Real.sqrt_nonneg _
  apply div_pos (by positivity) (by linarith)

lemma eL_le_pi (E : Economy) (l : ℝ) : eL E l ≤ E.π := by
  unfold eL
  have := R_pos E
  have := E.hπ0
  have hs : 0 ≤ sL E l := Real.sqrt_nonneg _
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma eL_ls (E : Economy) : eL E E.lstar = E.π := by
  have hR := R_pos E
  have hw := w_pos E
  have h := fd_ls E
  have hX : E.R ^ 2 - E.π * E.R * deriv E.f E.lstar / (2 * E.wstar) = 0 := by
    rw [show E.π * E.R * deriv E.f E.lstar = E.R * (E.π * deriv E.f E.lstar) by ring, h]
    field_simp
    ring
  unfold eL sL
  rw [hX, Real.sqrt_zero, add_zero]
  field_simp

lemma fd_le_ls (E : Economy) {l : ℝ} (h : E.lstar ≤ l) : deriv E.f l ≤ deriv E.f E.lstar :=
  (fd_anti E).antitoneOn (mem_Ioi.2 E.hl0) (mem_Ioi.2 (lt_of_lt_of_le E.hl0 h)) h

lemma X_nonneg (E : Economy) {l : ℝ} (h : E.lstar ≤ l) :
    0 ≤ E.R ^ 2 - E.π * E.R * deriv E.f l / (2 * E.wstar) := by
  have hR := R_pos E
  have hw := w_pos E
  have hπ := E.hπ0
  have h1 := fd_le_ls E h
  have h2 := fd_ls E
  have : E.π * E.R * deriv E.f l / (2 * E.wstar) ≤ E.R ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ E.π * E.R)
    nlinarith
  linarith

lemma eL_lt_pi (E : Economy) {l : ℝ} (h : E.lstar < l) : eL E l < E.π := by
  have hR := R_pos E
  have hw := w_pos E
  have hπ := E.hπ0
  have hl0 : 0 < l := lt_trans E.hl0 h
  have h1 : deriv E.f l < deriv E.f E.lstar := (fd_anti E) (mem_Ioi.2 E.hl0) (mem_Ioi.2 hl0) h
  have h2 := fd_ls E
  have hX : 0 < E.R ^ 2 - E.π * E.R * deriv E.f l / (2 * E.wstar) := by
    have : E.π * E.R * deriv E.f l / (2 * E.wstar) < E.R ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have := mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < E.π * E.R)
      nlinarith
    linarith
  have hs : 0 < sL E l := Real.sqrt_pos.2 hX
  unfold eL
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

lemma eL_anti (E : Economy) {a b : ℝ} (ha : E.lstar ≤ a) (hab : a ≤ b) : eL E b ≤ eL E a := by
  have hR := R_pos E
  have hw := w_pos E
  have hπ := E.hπ0
  have ha0 : 0 < a := lt_of_lt_of_le E.hl0 ha
  have h1 : deriv E.f b ≤ deriv E.f a :=
    (fd_anti E).antitoneOn (mem_Ioi.2 ha0) (mem_Ioi.2 (lt_of_lt_of_le ha0 hab)) hab
  have hs : sL E a ≤ sL E b := by
    unfold sL
    apply Real.sqrt_le_sqrt
    have : E.π * E.R * deriv E.f b / (2 * E.wstar) ≤ E.π * E.R * deriv E.f a / (2 * E.wstar) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hsa : 0 ≤ sL E a := Real.sqrt_nonneg _
  unfold eL
  apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- feasibility of the constructed pair `(rL l, l)` for `l* ≤ l ≤ 1` -/
lemma feas (E : Economy) {l : ℝ} (h : E.lstar ≤ l) (h1 : l ≤ 1) :
    0 < rL E l ∧ IsLaborDemand E (rL E l) l ∧ effort E (rL E l) = eL E l := by
  have hR := R_pos E
  have hw := w_pos E
  have hπ := E.hπ0
  have hl0 : 0 < l := lt_of_lt_of_le E.hl0 h
  have hfp := fd_pos E hl0
  have hX := X_nonneg E h
  have hs0 : 0 ≤ sL E l := Real.sqrt_nonneg _
  have hs2 : sL E l ^ 2 = E.R ^ 2 - E.π * E.R * deriv E.f l / (2 * E.wstar) := Real.sq_sqrt hX
  have hsR : sL E l < E.R := by
    unfold sL
    rw [Real.sqrt_lt' hR]
    have : 0 < E.π * E.R * deriv E.f l / (2 * E.wstar) := by positivity
    linarith
  have hmin : min (rL E l) E.R = rL E l := min_eq_left (by unfold rL; linarith)
  refine ⟨by unfold rL; linarith, ⟨hl0, h1, ?_⟩, ?_⟩
  · rw [hmin, div_eq_iff (by unfold rL; linarith)]
    have h' : E.π * E.R * deriv E.f l
        = 2 * E.wstar * (E.π * E.R * deriv E.f l / (2 * E.wstar)) := by
      field_simp
    unfold rL
    linear_combination 2 * E.wstar * hs2 + h'
  · unfold effort eL
    rw [hmin]
    unfold rL
    congr 1
    ring

/-- a feasible pair with `r < R` -/
lemma low (E : Economy) {r l : ℝ} (hrR : r < E.R) (h : IsLaborDemand E r l) :
    E.lstar < l ∧ effort E r = eL E l := by
  have hR := R_pos E
  have hw := w_pos E
  have hπ := E.hπ0
  obtain ⟨hl0, hl1, he⟩ := h
  have hmin : min r E.R = r := min_eq_left hrR.le
  rw [hmin, div_eq_iff (by linarith)] at he
  have e2 : E.π * E.R * deriv E.f E.lstar = 2 * E.R ^ 2 * E.wstar := by
    linear_combination E.R * fd_ls E
  have hq : 0 < E.wstar * (E.R - r) ^ 2 := mul_pos hw (pow_pos (sub_pos.2 hrR) 2)
  have hlt : E.π * E.R * deriv E.f l < E.π * E.R * deriv E.f E.lstar := by nlinarith
  have hlt' : deriv E.f l < deriv E.f E.lstar :=
    lt_of_mul_lt_mul_left hlt (by positivity)
  have hls : E.lstar < l := by
    by_contra hc
    push_neg at hc
    have := (fd_anti E).antitoneOn (mem_Ioi.2 hl0) (mem_Ioi.2 E.hl0) hc
    linarith
  refine ⟨hls, ?_⟩
  have hX : E.R ^ 2 - E.π * E.R * deriv E.f l / (2 * E.wstar) = (E.R - r) ^ 2 := by
    rw [he]
    field_simp
    ring
  have hs : sL E l = E.R - r := by
    unfold sL
    rw [hX, Real.sqrt_sq (by linarith)]
  unfold effort eL
  rw [hmin, hs]
  congr 1
  ring

/-- a feasible pair with `r ≥ R` -/
lemma high (E : Economy) {r l : ℝ} (hrR : E.R ≤ r) (h : IsLaborDemand E r l) :
    l ≤ E.lstar ∧ effort E r = E.π ∧ (E.R < r → l < E.lstar) := by
  have hR := R_pos E
  have hw := w_pos E
  have hπ := E.hπ0
  obtain ⟨hl0, hl1, he⟩ := h
  have hmin : min r E.R = E.R := min_eq_right hrR
  rw [hmin, show 2 * E.R - E.R = E.R by ring, div_eq_iff (by positivity)] at he
  have he' : E.π * deriv E.f l = 2 * r * E.wstar := by
    have : E.R * (E.π * deriv E.f l) = E.R * (2 * r * E.wstar) := by linear_combination he
    exact mul_left_cancel₀ (ne_of_gt hR) this
  have h2 := fd_ls E
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have : deriv E.f l < deriv E.f E.lstar := (fd_anti E) (mem_Ioi.2 E.hl0) (mem_Ioi.2 hl0) hc
    have := mul_lt_mul_of_pos_left this hπ
    nlinarith
  · unfold effort
    rw [hmin, show 2 * E.R - E.R = E.R by ring]
    field_simp
  · intro hr
    by_contra hc
    push_neg at hc
    have : deriv E.f l ≤ deriv E.f E.lstar := fd_le_ls E hc
    have := mul_le_mul_of_nonneg_left this hπ.le
    nlinarith

lemma eL_contOn (E : Economy) : ContinuousOn (eL E) (Icc E.lstar 1) := by
  have hR := R_pos E
  have hsub : Icc E.lstar 1 ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le E.hl0 hx.1
  unfold eL sL
  apply ContinuousOn.div continuousOn_const
  · exact continuousOn_const.add ((continuousOn_const.sub
      ((continuousOn_const.mul ((fd_cont E).mono hsub)).div_const _)).sqrt)
  · intro x _
    exact ne_of_gt (add_pos_of_pos_of_nonneg hR (Real.sqrt_nonneg _))

lemma T_contOn (E : Economy) (ρ : ℝ) :
    ContinuousOn (fun l => surplus E ρ (eL E l) l) (Icc E.lstar 1) := by
  have he := eL_contOn E
  unfold surplus
  apply ContinuousOn.add
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul (he.sub ((he.pow 2).div_const _))
    exact (f_cont E).mono (fun x hx => le_trans E.hl0.le hx.1)
  · apply continuousOn_const.mul
    exact (g_cont E).comp (continuousOn_const.sub continuousOn_id)
      (fun x hx => by simp only [mem_Ici, id]; linarith [hx.2])

theorem main (E : Economy) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (lρ : ℝ)
    (hlρ : IsFirstBestLabor E ρ lρ) :
    (∃ ru lu, IsOptimalRate E ρ ru lu) ∧
    ∀ ru lu, IsOptimalRate E ρ ru lu →
      ru ≤ E.R ∧ lu < lρ ∧ surplus E ρ (effort E ru) lu < surplus E ρ E.π lρ := by
  obtain ⟨hlρ0, hlρ1, hFB⟩ := hlρ
  have hR := R_pos E
  have hw := w_pos E
  have hπ := E.hπ0
  have hls0 := E.hl0
  have hls1 := E.hl1
  have hfls := fd_ls E
  -- l* < lρ
  have hlslρ : E.lstar < lρ := by
    by_contra hc
    push_neg at hc
    have h1 : deriv E.f E.lstar ≤ deriv E.f lρ :=
      (fd_anti E).antitoneOn (mem_Ioi.2 hlρ0) (mem_Ioi.2 hls0) hc
    have h2 : deriv E.g (1 - lρ) ≤ deriv E.g (1 - E.lstar) :=
      (gd_anti E).antitoneOn (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith)) (by linarith)
    have hg := gd_pos E (show 0 < 1 - lρ by linarith)
    have h3 : ρ * deriv E.g (1 - lρ) < deriv E.g (1 - lρ) := mul_lt_of_lt_one_left hg hρ1
    rw [div_eq_iff (by positivity)] at hFB
    have hw' := E.hw
    have h4 := mul_le_mul_of_nonneg_left h1 hπ.le
    have h5 : ρ * deriv E.g (1 - lρ) * (2 * E.R) < E.wstar * (2 * E.R) := by
      apply mul_lt_mul_of_pos_right _ (by positivity)
      linarith
    linarith
  -- derivative signs of the first-best surplus
  have hDpos : ∀ x ∈ Ioo 0 lρ,
      0 < (E.π - E.π ^ 2 / (2 * E.π)) * deriv E.f x / E.R - ρ * deriv E.g (1 - x) := by
    intro x hx
    have h1 : deriv E.f lρ < deriv E.f x := (fd_anti E) (mem_Ioi.2 hx.1) (mem_Ioi.2 hlρ0) hx.2
    have h2 : deriv E.g (1 - x) < deriv E.g (1 - lρ) :=
      (gd_anti E) (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith [hx.2])) (by linarith [hx.2])
    have : (E.π - E.π ^ 2 / (2 * E.π)) * deriv E.f x / E.R - ρ * deriv E.g (1 - x)
        = E.π / (2 * E.R) * (deriv E.f x - deriv E.f lρ)
          + ρ * (deriv E.g (1 - lρ) - deriv E.g (1 - x)) := by
      rw [phi_pi]
      linear_combination hFB
    rw [this]
    have : 0 < E.π / (2 * E.R) := by positivity
    have := mul_pos this (sub_pos.2 h1)
    have := mul_pos hρ0 (sub_pos.2 h2)
    linarith
  have hDneg : ∀ x ∈ Ioo lρ 1,
      (E.π - E.π ^ 2 / (2 * E.π)) * deriv E.f x / E.R - ρ * deriv E.g (1 - x) < 0 := by
    intro x hx
    have h1 : deriv E.f x < deriv E.f lρ :=
      (fd_anti E) (mem_Ioi.2 hlρ0) (mem_Ioi.2 (by linarith [hx.1])) hx.1
    have h2 : deriv E.g (1 - lρ) < deriv E.g (1 - x) :=
      (gd_anti E) (mem_Ioi.2 (by linarith [hx.2])) (mem_Ioi.2 (by linarith)) (by linarith [hx.1])
    have : (E.π - E.π ^ 2 / (2 * E.π)) * deriv E.f x / E.R - ρ * deriv E.g (1 - x)
        = E.π / (2 * E.R) * (deriv E.f x - deriv E.f lρ)
          + ρ * (deriv E.g (1 - lρ) - deriv E.g (1 - x)) := by
      rw [phi_pi]
      linear_combination hFB
    rw [this]
    have : 0 < E.π / (2 * E.R) := by positivity
    have := mul_neg_of_pos_of_neg this (sub_neg.2 h1)
    have := mul_neg_of_pos_of_neg hρ0 (sub_neg.2 h2)
    linarith
  -- the first-best surplus is maximal at lρ
  have hFBmax : ∀ l, 0 < l → l ≤ 1 → l ≠ lρ → surplus E ρ E.π l < surplus E ρ E.π lρ := by
    intro l hl0 hl1 hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact surplus_lt_of_pos E ρ E.π hl0 hlt hlρ1.le
        (fun x hx => hDpos x ⟨by linarith [hx.1], hx.2⟩)
    · exact surplus_lt_of_neg E ρ E.π hlρ0 hgt hl1
        (fun x hx => hDneg x ⟨hx.1, by linarith [hx.2]⟩)
  have hFBmono : ∀ a b, 0 < a → a < b → b ≤ lρ → surplus E ρ E.π a < surplus E ρ E.π b := by
    intro a b ha hab hb
    exact surplus_lt_of_pos E ρ E.π ha hab (by linarith)
      (fun x hx => hDpos x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  -- (R, l*) is feasible
  have hLDR : IsLaborDemand E E.R E.lstar := by
    refine ⟨hls0, hls1.le, ?_⟩
    rw [min_self, show 2 * E.R - E.R = E.R by ring, div_eq_iff (by positivity)]
    linear_combination E.R * hfls
  have heffR : effort E E.R = E.π := by
    unfold effort
    rw [min_self, show 2 * E.R - E.R = E.R by ring]
    field_simp
  -- maximiser of T on [l*, 1]
  obtain ⟨l0, hl0mem, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 hls1.le) (T_contOn E ρ)
  have hmax' : ∀ l ∈ Icc E.lstar 1, surplus E ρ (eL E l) l ≤ surplus E ρ (eL E l0) l0 :=
    fun l hl => isMaxOn_iff.1 hmax l hl
  refine ⟨?_, ?_⟩
  · obtain ⟨hr0, hLD, heff⟩ := feas E hl0mem.1 hl0mem.2
    refine ⟨rL E l0, l0, hr0, hLD, ?_⟩
    intro r l _ hLDrl
    rw [heff]
    by_cases hrR : r < E.R
    · obtain ⟨hls, he⟩ := low E hrR hLDrl
      rw [he]
      exact hmax' l ⟨hls.le, hLDrl.2.1⟩
    · push_neg at hrR
      obtain ⟨hle, he, _⟩ := high E hrR hLDrl
      rw [he]
      have h1 : surplus E ρ E.π l ≤ surplus E ρ E.π E.lstar := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact (hFBmono l E.lstar hLDrl.1 hlt hlslρ.le).le
        · rw [heq]
      have h2 := hmax' E.lstar ⟨le_rfl, hls1.le⟩
      rw [eL_ls] at h2
      linarith
  · intro ru lu hopt
    obtain ⟨hru0, hLDu, hmaxu⟩ := hopt
    have hlu0 := hLDu.1
    have hlu1 := hLDu.2.1
    -- ru ≤ R
    have hruR : ru ≤ E.R := by
      by_contra hc
      push_neg at hc
      obtain ⟨_, he, hlt⟩ := high E hc.le hLDu
      have h1 := hmaxu E.R E.lstar hR hLDR
      rw [heffR, he] at h1
      have h2 := hFBmono lu E.lstar hlu0 (hlt hc) hlslρ.le
      linarith
    -- lu < lρ
    have hluρ : lu < lρ := by
      rcases lt_or_eq_of_le hruR with hlt | heq
      · obtain ⟨hlslu, heu⟩ := low E hlt hLDu
        by_contra hc
        push_neg at hc
        set eu := eL E lu with heu_def
        have heuπ : eu < E.π := eL_lt_pi E hlslu
        have heu0 : 0 < eu := eL_pos E lu
        have hφlt : eu - eu ^ 2 / (2 * E.π) < E.π / 2 := phi_lt E eu (ne_of_lt heuπ)
        have hφ0 : 0 ≤ eu - eu ^ 2 / (2 * E.π) := by
          have : eu - eu ^ 2 / (2 * E.π) = eu * (2 * E.π - eu) / (2 * E.π) := by
            field_simp
          rw [this]
          apply div_nonneg _ (by positivity)
          apply mul_nonneg heu0.le
          linarith
        -- D_u at lρ is negative
        have hfρ := fd_pos E hlρ0
        have hDρ : (eu - eu ^ 2 / (2 * E.π)) * deriv E.f lρ / E.R - ρ * deriv E.g (1 - lρ) < 0 := by
          have h1 : (eu - eu ^ 2 / (2 * E.π)) * deriv E.f lρ / E.R
              < E.π / 2 * deriv E.f lρ / E.R :=
            div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hφlt hfρ) hR
          have h2 : E.π / 2 * deriv E.f lρ / E.R = ρ * deriv E.g (1 - lρ) := by
            linear_combination hFB
          linarith
        -- continuity of D_u at lρ
        have hfc : ContinuousAt (deriv E.f) lρ := (fd_cont E).continuousAt (Ioi_mem_nhds hlρ0)
        have hgc : ContinuousAt (fun l => deriv E.g (1 - l)) lρ := by
          have h1 : ContinuousAt (deriv E.g) (1 - lρ) :=
            (gd_cont E).continuousAt (Ioi_mem_nhds (by linarith))
          exact h1.comp (continuousAt_const.sub continuousAt_id)
        have hDc : ContinuousAt (fun l => (eu - eu ^ 2 / (2 * E.π)) * deriv E.f l / E.R
            - ρ * deriv E.g (1 - l)) lρ :=
          ((continuousAt_const.mul hfc).div_const _).sub (continuousAt_const.mul hgc)
        have hev := hDc.eventually_lt continuousAt_const hDρ
        obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
        set a := max (lρ - ε / 2) E.lstar with ha_def
        have hlsa : E.lstar ≤ a := le_max_right _ _
        have ha1 : lρ - ε / 2 ≤ a := le_max_left _ _
        have haρ : a < lρ := max_lt (by linarith) hlslρ
        have ha0 : 0 < a := lt_of_lt_of_le hls0 hlsa
        have hau : a < lu := lt_of_lt_of_le haρ hc
        have hDa : ∀ l ∈ Ioo a lu,
            (eu - eu ^ 2 / (2 * E.π)) * deriv E.f l / E.R - ρ * deriv E.g (1 - l) < 0 := by
          intro l hl
          by_cases hlρl : l < lρ
          · apply hball
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hl.1]
          · push_neg at hlρl
            have hl1 : l < 1 := lt_of_lt_of_le hl.2 hlu1
            have h1 : deriv E.f l ≤ deriv E.f lρ :=
              (fd_anti E).antitoneOn (mem_Ioi.2 hlρ0) (mem_Ioi.2 (by linarith)) hlρl
            have h2 : deriv E.g (1 - lρ) ≤ deriv E.g (1 - l) :=
              (gd_anti E).antitoneOn (mem_Ioi.2 (by linarith)) (mem_Ioi.2 (by linarith))
                (by linarith)
            have h3 : (eu - eu ^ 2 / (2 * E.π)) * deriv E.f l / E.R
                ≤ (eu - eu ^ 2 / (2 * E.π)) * deriv E.f lρ / E.R :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hφ0) hR.le
            have h4 := mul_le_mul_of_nonneg_left h2 hρ0.le
            linarith
        have hlt1 : surplus E ρ eu lu < surplus E ρ eu a :=
          surplus_lt_of_neg E ρ eu ha0 hau hlu1 hDa
        have hlt2 : surplus E ρ eu a ≤ surplus E ρ (eL E a) a :=
          surplus_mono_e E ρ heu0.le (eL_anti E hlsa hau.le) (eL_le_pi E a) ha0
        obtain ⟨hra0, hLDa, hea⟩ := feas E hlsa (by linarith)
        have hlt3 := hmaxu (rL E a) a hra0 hLDa
        rw [hea, heu] at hlt3
        linarith
      · rw [heq] at hLDu
        obtain ⟨hle, _, _⟩ := high E le_rfl hLDu
        linarith
    refine ⟨hruR, hluρ, ?_⟩
    have h1 := surplus_le_pi E ρ (effort E ru) hlu0
    have h2 := hFBmono lu lρ hlu0 hluρ le_rfl
    linarith

end P11Aux

open LeveragedPayouts.Unregulated in
theorem solution (E : Economy) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (lρ : ℝ)
    (hlρ : IsFirstBestLabor E ρ lρ) :
    (∃ ru lu, IsOptimalRate E ρ ru lu) ∧
    ∀ ru lu, IsOptimalRate E ρ ru lu →
      ru ≤ E.R ∧ lu < lρ ∧ surplus E ρ (effort E ru) lu < surplus E ρ E.π lρ := by
  exact P11Aux.main E ρ hρ0 hρ1 lρ hlρ
