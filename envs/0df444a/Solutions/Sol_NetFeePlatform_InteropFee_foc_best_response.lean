-- Prove2me | solution 1 for NetFeePlatform.InteropFee.foc_best_response
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:32:39.728592+00:00
-- url     : https://prove2.me/submissions/33db002b-a731-4ea4-8046-387725c1be54

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
set_option autoImplicit false
open NetFeePlatform.Competition

noncomputable def PhiF (a g n : ℝ) : ℝ := n * (a - Real.log n + Real.log (1 - n) + g * n)
noncomputable def PsiF (a g n : ℝ) : ℝ := a - Real.log n + Real.log (1 - n) + 2 * g * n - 1 / (1 - n)

theorem PhiF_deriv (a g n : ℝ) (h0 : 0 < n) (h1 : n < 1) : HasDerivAt (PhiF a g) (PsiF a g n) n := by
  have hn : n ≠ 0 := h0.ne'
  have hm : 1 - n ≠ 0 := by linarith
  have l1 : HasDerivAt Real.log n⁻¹ n := Real.hasDerivAt_log hn
  have l2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - n)) n :=
    ((hasDerivAt_id n).const_sub 1).log hm |>.congr_deriv (by simp)
  have inner : HasDerivAt (fun x : ℝ => a - Real.log x + Real.log (1 - x) + g * x)
      (-n⁻¹ + (-1 / (1 - n)) + g) n := by
    have := (((hasDerivAt_const n a).sub l1).add l2).add ((hasDerivAt_id n).const_mul g)
    refine this.congr_deriv ?_
    simp
  have := (hasDerivAt_id n).mul inner
  refine (this.congr_deriv ?_)
  unfold PsiF
  simp only [id]
  field_simp
  ring

theorem PsiF_deriv (a g n : ℝ) (h0 : 0 < n) (h1 : n < 1) :
    HasDerivAt (PsiF a g) (-n⁻¹ + (-1 / (1 - n)) + 2 * g - 1 / (1 - n) ^ 2) n := by
  have hn : n ≠ 0 := h0.ne'
  have hm : 1 - n ≠ 0 := by linarith
  have l1 : HasDerivAt Real.log n⁻¹ n := Real.hasDerivAt_log hn
  have l2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - n)) n :=
    ((hasDerivAt_id n).const_sub 1).log hm |>.congr_deriv (by simp)
  have l3 : HasDerivAt (fun x : ℝ => 1 / (1 - x)) (1 / (1 - n) ^ 2) n := by
    have := (hasDerivAt_const n (1:ℝ)).div ((hasDerivAt_id n).const_sub 1) hm
    refine this.congr_deriv ?_
    simp
  have := ((((hasDerivAt_const n a).sub l1).add l2).add ((hasDerivAt_id n).const_mul (2 * g))).sub l3
  refine this.congr_deriv ?_
  simp

theorem PsiF_deriv_nonpos (a g n : ℝ) (hg : g ≤ 27 / 8) (h0 : 0 < n) (h1 : n < 1) :
    -n⁻¹ + (-1 / (1 - n)) + 2 * g - 1 / (1 - n) ^ 2 ≤ 0 := by
  have hm : 0 < 1 - n := by linarith
  have key : 27 / 4 ≤ n⁻¹ + 1 / (1 - n) + 1 / (1 - n) ^ 2 := by
    have h : n⁻¹ + 1 / (1 - n) + 1 / (1 - n) ^ 2 = 1 / (n * (1 - n) ^ 2) := by
      field_simp; ring
    rw [h, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (3 * n - 1), mul_nonneg (sq_nonneg (3 * n - 1)) (show (0:ℝ) ≤ 4 - 3 * n by linarith)]
  have : -1 / (1 - n) = -(1 / (1 - n)) := by ring
  rw [this]
  linarith

theorem core (a g : ℝ) (hg : g ≤ 27 / 8) (n0 : ℝ) (h0 : 0 < n0) (h1 : n0 < 1)
    (hcrit : PsiF a g n0 = 0) : ∀ n : ℝ, 0 < n → n < 1 → PhiF a g n ≤ PhiF a g n0 := by
  have hcont : ContinuousOn (PhiF a g) (Set.Ioo 0 1) := fun x hx =>
    (PhiF_deriv a g x hx.1 hx.2).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (PsiF a g) (Set.Ioo 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
    · intro x hx; exact (PsiF_deriv a g x hx.1 hx.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      exact (PsiF_deriv a g x hx.1 hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(PsiF_deriv a g x hx.1 hx.2).deriv]
      exact PsiF_deriv_nonpos a g x hg hx.1 hx.2
  intro n hn0 hn1
  rcases le_total n n0 with h | h
  · -- Phi monotone on (0, n0]
    have hmono : MonotoneOn (PhiF a g) (Set.Ioc 0 n0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 n0)
      · exact hcont.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 h1⟩)
      · intro x hx
        rw [interior_Ioc] at hx
        exact (PhiF_deriv a g x hx.1 (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ioc] at hx
        have hx1 : x < 1 := by linarith [hx.2]
        rw [(PhiF_deriv a g x hx.1 hx1).deriv]
        have := hanti ⟨hx.1, hx1⟩ ⟨h0, h1⟩ hx.2.le
        linarith
    exact hmono ⟨hn0, h⟩ ⟨h0, le_refl _⟩ h
  · have hmono : AntitoneOn (PhiF a g) (Set.Ico n0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ico n0 1)
      · exact hcont.mono (fun x hx => ⟨lt_of_lt_of_le h0 hx.1, hx.2⟩)
      · intro x hx
        rw [interior_Ico] at hx
        exact (PhiF_deriv a g x (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ico] at hx
        have hx0 : 0 < x := by linarith [hx.1]
        rw [(PhiF_deriv a g x hx0 hx.2).deriv]
        have := hanti ⟨h0, h1⟩ ⟨hx0, hx.2⟩ hx.1.le
        linarith
    exact hmono ⟨le_refl _, h1⟩ ⟨h, hn1⟩ h

theorem dem_update {J : ℕ} (w : ℝ) (t : Fin J → ℝ) (j : Fin J) (s : ℝ) :
    demand w (Function.update t j s) j =
      Real.exp (-s) / (Real.exp (-s) + (w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k))) := by
  unfold demand
  have : ∑ k, Real.exp (-(Function.update t j s k)) =
      Real.exp (-s) + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [this]
  simp only [Function.update_self]
  ring_nf

theorem sum_update {J : ℕ} (w : ℝ) (t : Fin J → ℝ) (j : Fin J) (s : ℝ) :
    ∑ k ∈ Finset.univ.erase j, demand w (Function.update t j s) k =
      (∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) /
        (Real.exp (-s) + (w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k))) := by
  unfold demand
  have : ∑ k, Real.exp (-(Function.update t j s k)) =
      Real.exp (-s) + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [this, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  ring_nf

theorem profit_formula {J : ℕ} (w c γ lam : ℝ) (t : Fin J → ℝ) (j : Fin J) (s : ℝ)
    (hC : 0 < w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) :
    profit w c γ lam (Function.update t j s) j =
      PhiF (-Real.log (w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) - c
              + lam * γ * ((∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) / (w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k))))
        (γ * (1 - lam * ((∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) / (w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k)))))
        (Real.exp (-s) / (Real.exp (-s) + (w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k)))) := by
  set Cp := ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) with hCp
  set C := w + Cp with hCdef
  have he : 0 < Real.exp (-s) := Real.exp_pos _
  have hD : 0 < Real.exp (-s) + C := by linarith
  have hN0 : 0 < Real.exp (-s) / (Real.exp (-s) + C) := by positivity
  have h1N : 1 - Real.exp (-s) / (Real.exp (-s) + C) = C / (Real.exp (-s) + C) := by
    field_simp; ring
  have hslog : s = -Real.log C + Real.log (1 - Real.exp (-s) / (Real.exp (-s) + C))
      - Real.log (Real.exp (-s) / (Real.exp (-s) + C)) := by
    rw [h1N, Real.log_div hC.ne' hD.ne', Real.log_div he.ne' hD.ne', Real.log_exp]
    ring
  unfold profit
  rw [dem_update, sum_update]
  simp only [Function.update_self]
  unfold PhiF
  set N := Real.exp (-s) / (Real.exp (-s) + C) with hN
  have hCp' : Cp / (Real.exp (-s) + C) = Cp / C * (1 - N) := by
    rw [hN, h1N]; field_simp
  rw [hCp']
  have : s = -Real.log C + Real.log (1 - N) - Real.log N := hslog
  calc _ = N * (s + γ * N + lam * γ * (Cp / C * (1 - N)) - c) := by ring
    _ = _ := by
      rw [this]; ring

theorem foc_general {J : ℕ} (w c γ lam : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hγ : γ ≤ 27 / 8) (t : Fin J → ℝ) (j : Fin J)
    (hfoc : t j = c + 1 / (1 - demand w t j) - 2 * γ * demand w t j
      + lam * γ * diversion w t j * demand w t j
      - lam * γ * ∑ k ∈ Finset.univ.erase j, demand w t k) :
    ∀ s : ℝ, profit w c γ lam (Function.update t j s) j ≤ profit w c γ lam t j := by
  intro s
  set Cp := ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) with hCp
  have hCp0 : 0 ≤ Cp := Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
  have hC : 0 < w + Cp := by
    rcases hJ with h | h
    · linarith
    · have hne : (Finset.univ.erase j).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j)]
        simp
        omega
      have : 0 < Cp := Finset.sum_pos (fun k _ => Real.exp_pos _) hne
      linarith
  set C := w + Cp with hCdef
  set ρ := Cp / C with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg hCp0 hC.le
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hC]; linarith
  set a := -Real.log C - c + lam * γ * ρ with ha
  set g := γ * (1 - lam * ρ) with hg
  have hg27 : g ≤ 27 / 8 := by
    have h1 : 0 ≤ 1 - lam * ρ := by nlinarith
    have h2 : 1 - lam * ρ ≤ 1 := by nlinarith
    rcases le_total 0 γ with h | h
    · calc g = γ * (1 - lam * ρ) := rfl
        _ ≤ γ * 1 := by apply mul_le_mul_of_nonneg_left h2 h
        _ ≤ 27 / 8 := by linarith
    · have : γ * (1 - lam * ρ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h h1
      linarith
  have hP := fun s' => profit_formula w c γ lam t j s' hC
  have hPs := hP s
  have hP0 := hP (t j)
  rw [Function.update_eq_self] at hP0
  rw [hPs]
  -- n0
  obtain ⟨e0, he0⟩ : ∃ e0 : ℝ, e0 = Real.exp (-t j) := ⟨_, rfl⟩
  have he0pos : 0 < e0 := by rw [he0]; exact Real.exp_pos _
  have hD0 : 0 < e0 + C := by linarith
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℝ, n0 = e0 / (e0 + C) := ⟨_, rfl⟩
  have hn0def : demand w t j = n0 := by
    have := dem_update w t j (t j)
    rw [Function.update_eq_self] at this
    rw [this, hn0, he0]
  have hsum0 : ∑ k ∈ Finset.univ.erase j, demand w t k = Cp / (e0 + C) := by
    have := sum_update w t j (t j)
    simp only [Function.update_eq_self] at this
    rw [this, he0]
  have hn0pos : 0 < n0 := by rw [hn0]; exact div_pos he0pos hD0
  have h1n0 : 1 - n0 = C / (e0 + C) := by rw [hn0]; field_simp; ring
  have hn01 : n0 < 1 := by
    have : 0 < C / (e0 + C) := div_pos hC hD0
    linarith
  have hdiv : diversion w t j = ρ := by
    unfold diversion
    rw [hsum0, hn0def, h1n0, hρ]
    field_simp
  have hlogid : t j = -Real.log C + Real.log (1 - n0) - Real.log n0 := by
    rw [h1n0, hn0, Real.log_div hC.ne' hD0.ne', Real.log_div he0pos.ne' hD0.ne', he0, Real.log_exp]
    ring
  have hpsi : PsiF a g n0 = 0 := by
    unfold PsiF
    rw [hdiv, hn0def, hsum0] at hfoc
    have e1 : Cp / (e0 + C) = ρ * (1 - n0) := by rw [h1n0, hρ]; field_simp
    rw [e1] at hfoc
    have hne : 1 - n0 ≠ 0 := by linarith
    have hlog : a - Real.log n0 + Real.log (1 - n0) = t j - c + lam * γ * ρ := by
      rw [ha]; linarith [hlogid]
    have : a - Real.log n0 + Real.log (1 - n0) + 2 * g * n0 - 1 / (1 - n0) =
        (t j - c + lam * γ * ρ) + 2 * g * n0 - 1 / (1 - n0) := by linarith [hlog]
    rw [this, hg]
    have h2 : 1 / (1 - n0) = t j - c + 2 * γ * n0 - lam * γ * ρ * n0 + lam * γ * (ρ * (1 - n0)) := by
      linarith
    rw [h2]; ring
  rw [← he0, ← hn0] at hP0
  rw [hP0]
  have hs0 : 0 < Real.exp (-s) := Real.exp_pos _
  have hDs : 0 < Real.exp (-s) + C := by linarith
  have hNs0 : 0 < Real.exp (-s) / (Real.exp (-s) + C) := div_pos hs0 hDs
  have hNs1 : Real.exp (-s) / (Real.exp (-s) + C) < 1 := by
    rw [div_lt_one hDs]; linarith
  exact core a g hg27 n0 hn0pos hn01 hpsi _ hNs0 hNs1

theorem solution {J : ℕ} (w c γ lam : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hγ : γ ≤ 27 / 8) (t : Fin J → ℝ) (j : Fin J)
    (hfoc : t j = c + 1 / (1 - NetFeePlatform.Competition.demand w t j) - 2 * γ * NetFeePlatform.Competition.demand w t j
      + lam * γ * NetFeePlatform.Competition.diversion w t j * NetFeePlatform.Competition.demand w t j
      - lam * γ * ∑ k ∈ Finset.univ.erase j, NetFeePlatform.Competition.demand w t k) :
    ∀ s : ℝ, NetFeePlatform.Competition.profit w c γ lam (Function.update t j s) j ≤ NetFeePlatform.Competition.profit w c γ lam t j :=
  foc_general w c γ lam hw hJ hlam0 hlam1 hγ t j hfoc
