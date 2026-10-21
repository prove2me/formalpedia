-- Prove2me | solution 1 for NetFeePlatform.Competition.gChar_characterization
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:17:50.405881+00:00
-- url     : https://prove2.me/submissions/52ab72df-8412-4de6-afee-de1c74ae6038

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_Competition_GChar
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

theorem foc_sol {J : ℕ} (w c γ : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (hγ : γ ≤ 27 / 8) (t : Fin J → ℝ) (j : Fin J)
    (hfoc : t j = c + 1 / (1 - demand w t j) - 2 * γ * demand w t j) :
    ∀ s : ℝ, profit w c γ 0 (Function.update t j s) j ≤ profit w c γ 0 t j :=
  foc_general w c γ 0 hw hJ le_rfl zero_le_one hγ t j (by simp only [zero_mul, add_zero, sub_zero]; exact hfoc)

theorem aux_sum_p1 {J : ℕ} (t : Fin J → ℝ) (j : Fin J) (s : ℝ) :
    ∑ k, Real.exp (-(Function.update t j s k)) =
      Real.exp (-s) + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem logit_deriv_aux {J : ℕ} (w : ℝ) (hw : 0 ≤ w) (t : Fin J → ℝ) (j : Fin J) :
    HasDerivAt (fun s => demand w (Function.update t j s) j)
      (-(demand w t j * (1 - demand w t j))) (t j) := by
  set C : ℝ := w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) :=
      Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
    linarith
  have hf : (fun s => demand w (Function.update t j s) j) = fun s => Real.exp (-s) / (Real.exp (-s) + C) := by
    funext s
    unfold demand
    rw [aux_sum_p1]
    simp only [Function.update_self]
    rw [hC]; ring_nf
  rw [hf]
  have hD : ∀ s, 0 < Real.exp (-s) + C := fun s => by have := Real.exp_pos (-s); linarith
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-(t j))) (t j) := by
    have := ((hasDerivAt_id (t j)).neg).exp
    have this : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-(t j)) * -1) (t j) := this
    refine this.congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s) + C) (-Real.exp (-(t j))) (t j) := h1.add_const C
  have h3 : HasDerivAt (fun s : ℝ => Real.exp (-s) / (Real.exp (-s) + C))
      ((-Real.exp (-t j) * (Real.exp (-t j) + C) - Real.exp (-t j) * -Real.exp (-t j)) / (Real.exp (-t j) + C) ^ 2) (t j) :=
    h1.div h2 (hD (t j)).ne'
  refine h3.congr_deriv ?_
  have hdem : demand w t j = Real.exp (-t j) / (Real.exp (-t j) + C) := by
    unfold demand
    have := aux_sum_p1 t j (t j)
    rw [Function.update_eq_self] at this
    rw [this, hC]; ring_nf
  rw [hdem]
  have := (hD (t j)).ne'
  field_simp
  ring

theorem prop1_sol {J : ℕ} (w c γ : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (t : Fin J → ℝ) (ht : IsEquilibrium w c γ 0 t) :
    ∀ j, t j = c + 1 / (1 - demand w t j) - 2 * γ * demand w t j := by
  intro j
  have hn := logit_deriv_aux w hw t j
  have hsplit : ∑ k, Real.exp (-t k) = Real.exp (-t j) + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hC : 0 < w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) := by
    have h0 : 0 ≤ ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) :=
      Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
    rcases hJ with h | h
    · linarith
    · have hne : (Finset.univ.erase j).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j)]
        simp
        omega
      have : 0 < ∑ k ∈ Finset.univ.erase j, Real.exp (-t k) :=
        Finset.sum_pos (fun k _ => Real.exp_pos _) hne
      linarith
  have hD : 0 < w + ∑ k, Real.exp (-t k) := by
    rw [hsplit]; have := Real.exp_pos (-t j); linarith
  have hn0 : 0 < demand w t j := by unfold demand; positivity
  have hn1 : 0 < 1 - demand w t j := by
    unfold demand
    rw [sub_pos, div_lt_one hD, hsplit]
    linarith
  set n := demand w t j with hnn
  have hf : (fun s => profit w c γ 0 (Function.update t j s) j) =
      fun s => (s + γ * demand w (Function.update t j s) j - c) * demand w (Function.update t j s) j := by
    funext s
    simp [profit]
  have hder : HasDerivAt (fun s => profit w c γ 0 (Function.update t j s) j)
      ((1 + γ * (-(n * (1 - n)))) * n + (t j + γ * n - c) * (-(n * (1 - n)))) (t j) := by
    rw [hf]
    have h1 : HasDerivAt (fun s : ℝ => s + γ * demand w (Function.update t j s) j - c)
        (1 + γ * (-(n * (1 - n)))) (t j) :=
      (((hasDerivAt_id (t j)).add (hn.const_mul γ)).sub_const c)
    have h2 : HasDerivAt (fun s : ℝ => (s + γ * demand w (Function.update t j s) j - c) *
          demand w (Function.update t j s) j)
        ((1 + γ * (-(n * (1 - n)))) * demand w (Function.update t j (t j)) j +
          (t j + γ * demand w (Function.update t j (t j)) j - c) * (-(n * (1 - n)))) (t j) :=
      h1.mul hn
    rw [Function.update_eq_self] at h2
    exact h2
  have hmax : IsLocalMax (fun s => profit w c γ 0 (Function.update t j s) j) (t j) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have := ht j s
    simpa [Function.update_eq_self] using this
  have h0 := hmax.hasDerivAt_eq_zero hder
  have key : n * ((1 - γ * (n * (1 - n))) - (t j + γ * n - c) * (1 - n)) = 0 := by linarith
  have key2 : (1 - γ * (n * (1 - n))) - (t j + γ * n - c) * (1 - n) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hn0.ne'
    · exact h
  have : t j - c + 2 * γ * n = 1 / (1 - n) := by
    rw [eq_div_iff hn1.ne']
    linear_combination (-1) * key2
  linarith


theorem solution (c γ : ℝ) (J : ℕ) (hJ : 2 ≤ J) (n : ℝ)
    (hn0 : 0 < n) (hn1 : n < 1) (i : Fin J) :
    (∀ t : Fin J → ℝ, IsEquilibrium 0 c γ 0 t → demand 0 t i = 1 - n →
        (∀ k, k ≠ i → demand 0 t k = n / ((J : ℝ) - 1)) → gChar γ J n = 0) ∧
    (γ ≤ 27 / 8 → gChar γ J n = 0 →
      ∃ t : Fin J → ℝ, IsEquilibrium 0 c γ 0 t ∧ demand 0 t i = 1 - n ∧
        ∀ k, k ≠ i → demand 0 t k = n / ((J : ℝ) - 1)) := by
  have hJ2 : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) < J := by linarith
  have hJm : 0 < (J : ℝ) - 1 := by linarith
  have h1n : 0 < 1 - n := by linarith
  have hnJ : 0 < n / ((J : ℝ) - 1) := div_pos hn0 hJm
  have hnJ1 : n / ((J : ℝ) - 1) < 1 := by
    rw [div_lt_one hJm]; linarith
  have hlogJ : Real.log (n / ((J : ℝ) - 1)) = Real.log n - Real.log ((J : ℝ) - 1) :=
    Real.log_div hn0.ne' hJm.ne'
  constructor
  · intro t ht hi hk
    obtain ⟨k, hki⟩ : ∃ k : Fin J, k ≠ i := by
      by_cases h : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
    have hf := prop1_sol 0 c γ le_rfl (Or.inr hJ) t ht
    have fi := hf i
    have fk := hf k
    rw [hi] at fi
    rw [hk k hki] at fk
    have e1 : 1 - (1 - n) = n := by ring
    rw [e1] at fi
    -- the ratio of shares
    set D : ℝ := 0 + ∑ j, Real.exp (-t j) with hD
    have hDpos : 0 < D := by
      have : Real.exp (-t i) ≤ ∑ j, Real.exp (-t j) :=
        Finset.single_le_sum (f := fun j => Real.exp (-t j)) (fun j _ => (Real.exp_pos _).le)
          (Finset.mem_univ i)
      have := Real.exp_pos (-t i)
      rw [hD]; linarith
    have hei : Real.exp (-t i) = (1 - n) * D := by
      have : demand 0 t i = Real.exp (-t i) / D := rfl
      rw [hi] at this
      field_simp at this
      linarith
    have hek : Real.exp (-t k) = n / ((J : ℝ) - 1) * D := by
      have : demand 0 t k = Real.exp (-t k) / D := rfl
      rw [hk k hki] at this
      field_simp at this
      rw [div_mul_eq_mul_div, eq_div_iff hJm.ne']
      linarith
    have hti : -t i = Real.log (1 - n) + Real.log D := by
      rw [← Real.log_mul h1n.ne' hDpos.ne', ← hei, Real.log_exp]
    have htk : -t k = Real.log (n / ((J : ℝ) - 1)) + Real.log D := by
      rw [← Real.log_mul hnJ.ne' hDpos.ne', ← hek, Real.log_exp]
    unfold gChar
    rw [hlogJ] at htk
    linarith
  · intro hγ hg
    set L : ℝ := Real.log n - Real.log ((J : ℝ) - 1) - Real.log (1 - n) with hL
    set τ : ℝ := c + 1 / n - 2 * γ * (1 - n) with hτ
    set t : Fin J → ℝ := fun j => if j = i then τ else τ - L with ht
    have hexpL : Real.exp L = n / ((J : ℝ) - 1) / (1 - n) := by
      rw [hL, Real.exp_sub, Real.exp_sub, Real.exp_log hn0, Real.exp_log hJm, Real.exp_log h1n]
    have hsum : ∑ j, Real.exp (-t j) = Real.exp (-τ) / (1 - n) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have : ∀ j ∈ Finset.univ.erase i, Real.exp (-t j) = Real.exp (-τ) * Real.exp L := by
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp only [ht, if_neg hji]
        rw [← Real.exp_add]; congr 1; ring
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hexpL]
      simp only [ht, if_pos rfl]
      have : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this]
      field_simp
      ring
    have hdem : ∀ j, demand 0 t j = Real.exp (-t j) * (1 - n) / Real.exp (-τ) := by
      intro j
      unfold demand
      rw [hsum, zero_add]
      have := Real.exp_pos (-τ)
      field_simp
    have hdi : demand 0 t i = 1 - n := by
      rw [hdem]
      simp only [ht, if_pos rfl]
      have := Real.exp_pos (-τ)
      field_simp
    have hdk : ∀ k, k ≠ i → demand 0 t k = n / ((J : ℝ) - 1) := by
      intro k hki
      rw [hdem]
      simp only [ht, if_neg hki]
      have : Real.exp (-(τ - L)) = Real.exp (-τ) * Real.exp L := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this, hexpL]
      have := Real.exp_pos (-τ)
      field_simp
    refine ⟨t, ?_, hdi, hdk⟩
    intro j s
    refine foc_sol 0 c γ le_rfl (Or.inr hJ) hγ t j ?_ s
    by_cases hji : j = i
    · subst hji
      rw [hdi]
      have : 1 - (1 - n) = n := by ring
      rw [this]
      simp only [ht, if_pos rfl, hτ]
    · rw [hdk j hji]
      simp only [ht, if_neg hji]
      unfold gChar at hg
      rw [hL, hτ]
      linarith
