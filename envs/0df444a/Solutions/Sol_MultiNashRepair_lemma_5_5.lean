-- Prove2me | solution 1 for MultiNashRepair.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:54:47.005515+00:00
-- url     : https://prove2.me/submissions/1bad653e-c267-42bf-93c1-147a624a7bd5

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_Controls
import Definitions.Def_MultiNashRepair_Regret
import Theorems.Thm_MultiNashRepair_controls_5_7

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset
open MultiNashRepair

theorem MNR55_ep_bounds {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (hx : AGT.IsMixedProfile x) (i : Fin m) :
    0 ≤ AGT.expectedPayoff u x i ∧ AGT.expectedPayoff u x i ≤ 1 := by
  have hp : ∀ s : Tuple n, 0 ≤ AGT.profileProb x s := fun s =>
    Finset.prod_nonneg (fun j _ => (hx j).1 (s j))
  have hsum : ∑ s : Tuple n, AGT.profileProb x s = 1 := by
    unfold AGT.profileProb
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun j _ => (hx j).2)
  unfold AGT.expectedPayoff
  constructor
  · exact Finset.sum_nonneg (fun s _ => mul_nonneg (hp s) (hu i s).1)
  · calc ∑ s, AGT.profileProb x s * u i s ≤ ∑ s, AGT.profileProb x s * 1 :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hu i s).2 (hp s))
      _ = 1 := by simp [hsum]

theorem MNR55_update_mixed {m : ℕ} {n : Fin m → ℕ} (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (j : Fin m) (y : Fin (n j) → ℝ) (hy : AGT.IsLottery y) :
    AGT.IsMixedProfile (Function.update x j y) := by
  intro k
  by_cases hk : k = j
  · subst hk; simpa using hy
  · simpa [Function.update_of_ne hk] using hx k

theorem MNR55_deficit_nonneg {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (hu : BoundedGame u)
    (x : Mixed n) (hx : AGT.IsMixedProfile x) (i : Fin m) (b : Fin (n i) → ℝ)
    (hb : AGT.IsLottery b) : 0 ≤ deficitMix u x i b := by
  unfold deficitMix
  have h1 := (MNR55_ep_bounds u hu _ (MNR55_update_mixed x hx i b hb) i).2
  have h2 := (MNR55_ep_bounds u hu x hx i).1
  linarith

theorem MNR55_isRat_sum {m : ℕ} (f : Fin m → ℝ) (hf : ∀ i, IsRat (f i)) : IsRat (∑ i, f i) := by
  choose q hq using hf
  exact ⟨∑ i, q i, by push_cast; simp [hq]⟩

set_option maxHeartbeats 4000000 in
theorem solution {σ : ℚ} (ctrl : Controls σ) {m : ℕ} {n : Fin m → ℕ} (hm : ctrl.m0 ≤ m)
    (hn : ∀ i, 0 < n i) (u : Utility n) (hu : BoundedGame u) (x : Mixed n)
    (hx : AGT.IsMixedProfile x) (lam' : Fin m → ℝ) (b : Mixed n) (hlam : AGT.IsLottery lam')
    (hb : AGT.IsMixedProfile b) (h : Fin m → ℝ) (hh0 : ∀ i, 0 ≤ h i)
    (hL0 : ∑ i, h i ≤ ctrl.knobs.L0)
    (hv : ∀ i, (m : ℝ) * h i - ∑ j, h j ≤ ctrl.knobs.R0 * ∑ j, h j)
    (h511 : ∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
      ∑ i, lam' i * deficitMix u (Function.update x j y) i (b i) <
        (scaled u x + ctrl.mu (scaled u x) (∑ i, h i)) / m)
    (h526 : (⨆ i, (m : ℝ) * lam' i) - 1 +
      ctrl.knobs.Q * ∑ i, lam' i * ((m : ℝ) * h i - ∑ j, h j) ≤ ctrl.knobs.R0) :
    let k := ctrl.knobs
    let H := ∑ i, h i
    let v : Fin m → ℝ := fun i => (m : ℝ) * h i - H
    let τ := ∑ i, lam' i * v i
    let γ : Fin m → ℝ := fun i => lam' i * (k.G0 - k.Q * v i) / (k.G0 - k.Q * τ)
    let δ : Fin m → ℝ := fun i => k.beta / m * (k.G0 - k.Q * v i - m * γ i)
    let h' : Fin m → ℝ := k.c • (h + k.t • γ)
    let H' := k.c * (H + k.t)
    (AGT.IsLottery γ ∧ (∀ i, γ i < 3 / m) ∧ (∀ i, γ i ≤ 3 * lam' i) ∧
      ((∀ i, IsRat (lam' i)) → (∀ i, IsRat (h i)) → ∀ i, IsRat (γ i))) ∧
    ((∀ i, 0 ≤ δ i) ∧ ∑ i, δ i = 1 - k.rho ∧
      ∀ i, δ i = k.Dsh H / m - k.beta * γ i - k.nu * h i) ∧
    ((∀ i, 0 ≤ h' i) ∧ ∑ i, h' i = H' ∧ H' ≤ k.L0 ∧ ∀ i, (m : ℝ) * h' i - H' ≤ k.R0 * H') ∧
    (∀ P : ℝ, 0 < P → P ≤ 1 →
      (∀ i, 0 ≤ P * h i) ∧ P * H ≤ k.L0 ∧ ∀ i, (m : ℝ) * (P * h i) - P * H ≤ k.R0 * (P * H)) ∧
    (∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
      ∑ i ∈ univ.erase j, γ i * deficitMix u (Function.update x j y) i (b i) < 9 / m) := by
  intro k H v τ γ δ h' H'
  -- scalar constants
  have hdq : (0:ℚ) < ctrl.d := ctrl.d_pos
  have hd : (0:ℝ) < ctrl.d := by exact_mod_cast hdq
  have huq : ctrl.u = 1/2 * min (1/144) (ctrl.d/100) := rfl
  have hu0q : (0:ℚ) < ctrl.u := by
    rw [huq]; have := lt_min (by norm_num : (0:ℚ) < 1/144) (by positivity : (0:ℚ) < ctrl.d/100)
    linarith
  have hu1q : ctrl.u ≤ 1/288 := by
    rw [huq]; have := min_le_left (1/144 : ℚ) (ctrl.d/100); linarith
  have hu0 : (0:ℝ) < ctrl.u := by exact_mod_cast hu0q
  have hu1 : (ctrl.u:ℝ) ≤ 1/288 := by
    have := (Rat.cast_le (K := ℝ)).mpr hu1q; push_cast at this; exact this
  have hf1 : (7/12:ℝ) ≤ ctrl.f0 := by
    have := (Rat.cast_le (K := ℝ)).mpr ctrl.f0_ge; push_cast at this; exact this
  have hf2 : (ctrl.f0:ℝ) ≤ 3/5 := by
    have := (Rat.cast_le (K := ℝ)).mpr ctrl.f0_le; push_cast at this; exact this
  have hF0 : (0:ℝ) < ctrl.f0 := by linarith
  -- m > 0
  have hmpos : (0:ℝ) < m := by
    have h1 := ctrl.m0_ge_d
    have : (0:ℝ) < 66 / (ctrl.d:ℝ) := by positivity
    have : (ctrl.m0:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  -- controls facts
  have hC := MultiNashRepair.controls_5_7 (ctrl.f0:ℝ) (ctrl.u:ℝ) hf1 hf2 hu0 (by linarith)
  dsimp only at hC
  have hR0pos : 0 < k.R0 := hC.1.1
  have hR0lt : k.R0 < 1 := hC.1.2.1
  have hQ1 : 1 < k.Q := hC.1.2.2.1
  have hQ2 : k.Q < 2 := hC.1.2.2.2.1
  have hL0f : k.L0 < ctrl.f0 := hC.1.2.2.2.2.2.2.1
  have hQL0 : k.Q * k.L0 < k.c := hC.1.2.2.2.2.2.2.2
  have hSuB : ∀ H : ℝ, 0 ≤ H → H ≤ k.L0 → k.Su H ≤ 1 + k.L0 + k.R0 ∧ 1 + k.L0 + k.R0 < 13 / 5 :=
    fun H h0 h1 => ⟨(hC.2 H h0 h1).2.2.1, (hC.2 H h0 h1).2.2.2⟩
  have hc : k.c = 1 - ctrl.u + (ctrl.u:ℝ)^2/2 - (ctrl.u:ℝ)^3 := rfl
  have ht : k.t = ctrl.f0 * ctrl.u := rfl
  have hcpos : 0 < k.c := by rw [hc]; nlinarith only [hu0, hu1]
  have hc1 : k.c < 1 := by rw [hc]; nlinarith only [hu0, hu1]
  have htpos : 0 < k.t := by rw [ht]; positivity
  have hu0' : 0 < 1 + k.u0 := by
    have : k.u0 = (ctrl.u:ℝ) - (ctrl.u:ℝ)^2 := rfl
    rw [this]; nlinarith only [hu0, hu1]
  have hβpos : 0 < k.beta := by
    have : k.beta = k.c * k.t * (1 + k.u0) := rfl
    rw [this]; positivity
  have hν : k.nu = k.Q * k.beta := by
    have : k.Q = k.nu / k.beta := rfl
    rw [this]; field_simp
  have hρ : 1 - k.rho = k.beta * k.R0 := by
    have : k.R0 = (1 - k.rho) / k.beta := rfl
    rw [this]; field_simp
  have hG0 : k.G0 = 1 + k.R0 := rfl
  have hQt : k.Q * k.t < 1 := by
    rw [ht]
    have : (ctrl.f0:ℝ) * ctrl.u ≤ 3/5 * (1/288) := by
      apply mul_le_mul hf2 hu1 hu0.le (by norm_num)
    nlinarith only [this, hQ2, hQ1, mul_pos hF0 hu0]
  have hL0eq : k.c * (k.L0 + k.t) = k.L0 := by
    have : k.L0 = k.c * k.t / (1 - k.c) := rfl
    have h1c : (1 - k.c) ≠ 0 := by linarith
    rw [this]; field_simp; ring
  -- memory facts
  have hHnn : 0 ≤ H := Finset.sum_nonneg (fun i _ => hh0 i)
  have hHL : H ≤ k.L0 := hL0
  have hvdef : ∀ i, v i = (m:ℝ) * h i - H := fun i => rfl
  have hvsum : ∑ i, v i = 0 := by
    simp only [hvdef, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hvlo : ∀ i, -H ≤ v i := by
    intro i; rw [hvdef]; nlinarith only [hh0 i, hmpos]
  have hvhi : ∀ i, v i ≤ k.R0 * H := hv
  have hlam0 : ∀ i, 0 ≤ lam' i := hlam.1
  have hlam1 : ∑ i, lam' i = 1 := hlam.2
  have hτdef : τ = ∑ i, lam' i * v i := rfl
  have hτhi : τ ≤ k.R0 * H := by
    rw [hτdef]
    calc ∑ i, lam' i * v i ≤ ∑ i, lam' i * (k.R0 * H) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hvhi i) (hlam0 i))
      _ = k.R0 * H := by rw [← Finset.sum_mul, hlam1, one_mul]
  have hQH : k.Q * H ≤ k.c := by
    have := mul_le_mul_of_nonneg_left hHL (by linarith : (0:ℝ) ≤ k.Q)
    linarith
  have hQR0H : k.Q * (k.R0 * H) ≤ k.R0 := by
    have := mul_le_mul_of_nonneg_left hQH hR0pos.le
    nlinarith only [this, hc1, hR0pos]
  set Z0 := k.G0 - k.Q * τ with hZ0def
  have hZ0 : 1 ≤ Z0 := by
    have := mul_le_mul_of_nonneg_left hτhi (by linarith : (0:ℝ) ≤ k.Q)
    rw [hZ0def, hG0]; linarith
  have hGv_lo : ∀ i, 1 ≤ k.G0 - k.Q * v i := by
    intro i
    have := mul_le_mul_of_nonneg_left (hvhi i) (by linarith : (0:ℝ) ≤ k.Q)
    rw [hG0]; linarith
  have hGv_hi : ∀ i, k.G0 - k.Q * v i < 3 := by
    intro i
    have := mul_le_mul_of_nonneg_left (hvlo i) (by linarith : (0:ℝ) ≤ k.Q)
    rw [hG0]; nlinarith only [this, hQH, hR0lt, hc1]
  -- the floor condition
  have hpi : ∀ i, (m:ℝ) * lam' i ≤ Z0 := by
    intro i
    have h1 : (m:ℝ) * lam' i ≤ ⨆ i, (m : ℝ) * lam' i :=
      le_ciSup (f := fun i => (m:ℝ) * lam' i) (Set.finite_range _).bddAbove i
    have h2 : ∑ i, lam' i * ((m : ℝ) * h i - ∑ j, h j) = τ := rfl
    rw [h2] at h526
    rw [hZ0def, hG0]; linarith
  have hγdef : ∀ i, γ i = lam' i * (k.G0 - k.Q * v i) / Z0 := fun i => rfl
  have hZ0pos : 0 < Z0 := by linarith
  have hγ0 : ∀ i, 0 ≤ γ i := by
    intro i; rw [hγdef]
    exact div_nonneg (mul_nonneg (hlam0 i) (by linarith [hGv_lo i])) hZ0pos.le
  have hmγ : ∀ i, (m:ℝ) * γ i ≤ k.G0 - k.Q * v i := by
    intro i; rw [hγdef]
    rw [show (m:ℝ) * (lam' i * (k.G0 - k.Q * v i) / Z0) = ((m:ℝ) * lam' i) * (k.G0 - k.Q * v i) / Z0 by ring,
      div_le_iff₀ hZ0pos]
    have := mul_le_mul_of_nonneg_right (hpi i) (by linarith [hGv_lo i] : (0:ℝ) ≤ k.G0 - k.Q * v i)
    linarith
  have hγsum : ∑ i, γ i = 1 := by
    simp only [hγdef]
    rw [← Finset.sum_div, div_eq_one_iff_eq hZ0pos.ne']
    have : ∑ i, lam' i * (k.G0 - k.Q * v i) = k.G0 * ∑ i, lam' i - k.Q * ∑ i, lam' i * v i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, hlam1, ← hτdef, hZ0def]; ring
  have hδdef : ∀ i, δ i = k.beta / m * (k.G0 - k.Q * v i - m * γ i) := fun i => rfl
  have hh'def : ∀ i, h' i = k.c * (h i + k.t * γ i) := by
    intro i
    show (k.c • (h + k.t • γ)) i = _
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hH'def : H' = k.c * (H + k.t) := rfl
  refine ⟨⟨⟨hγ0, hγsum⟩, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- γ_i < 3/m
    intro i
    rw [lt_div_iff₀ hmpos]
    have := hmγ i; have := hGv_hi i; linarith [mul_comm (γ i) (m:ℝ)]
  · -- γ_i ≤ 3 λ_i
    intro i; rw [hγdef, div_le_iff₀ hZ0pos]
    have := mul_le_mul_of_nonneg_left (le_of_lt (hGv_hi i)) (hlam0 i)
    have := mul_le_mul_of_nonneg_left hZ0 (hlam0 i)
    nlinarith only [this, ‹lam' i * (k.G0 - k.Q * v i) ≤ lam' i * 3›, hlam0 i]
  · -- rationality
    intro hlq hhq i
    choose lq hlq' using hlq
    choose hq hhq' using hhq
    have hG0q : IsRat k.G0 := by
      refine ⟨1 + (1 - (1 - (1 - ctrl.f0) * ctrl.u + (1 - ctrl.f0)^2 * ctrl.u^2/2)) /
        ((1 - ctrl.u + ctrl.u^2/2 - ctrl.u^3) * (ctrl.f0 * ctrl.u) * (1 + (ctrl.u - ctrl.u^2))), ?_⟩
      push_cast; rfl
    have hQq : IsRat k.Q := by
      refine ⟨((1 - ctrl.u + ctrl.u^2/2 - ctrl.u^3) * (ctrl.u - ctrl.u^2)) /
        ((1 - ctrl.u + ctrl.u^2/2 - ctrl.u^3) * (ctrl.f0 * ctrl.u) * (1 + (ctrl.u - ctrl.u^2))), ?_⟩
      push_cast; rfl
    obtain ⟨gq, hgq⟩ := hG0q
    obtain ⟨qq, hqq⟩ := hQq
    refine ⟨lq i * (gq - qq * ((m:ℚ) * hq i - ∑ j, hq j)) /
      (gq - qq * ∑ j, lq j * ((m:ℚ) * hq j - ∑ l, hq l)), ?_⟩
    rw [hγdef, hZ0def, hτdef]
    simp only [hvdef]
    push_cast
    simp only [hlq', hhq', hgq, hqq]
    rfl
  · -- δ ≥ 0
    intro i; rw [hδdef]
    apply mul_nonneg (div_nonneg hβpos.le hmpos.le)
    linarith [hmγ i]
  · -- Σ δ = 1 - ρ
    simp only [hδdef]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hvsum, hγsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hρ, hG0]
    field_simp; ring
  · -- δ formula
    intro i
    rw [hδdef, hvdef, hν]
    have : k.Dsh H = k.beta * (k.G0 + k.Q * H) := rfl
    rw [this]; field_simp; ring
  · intro i; rw [hh'def]
    exact mul_nonneg hcpos.le (add_nonneg (hh0 i) (mul_nonneg htpos.le (hγ0 i)))
  · simp only [hh'def]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hγsum, hH'def]; ring
  · rw [hH'def, ← hL0eq]
    exact mul_le_mul_of_nonneg_left (by linarith) hcpos.le
  · intro i
    rw [hh'def, hH'def]
    have key : (m:ℝ) * h i + k.t * ((m:ℝ) * γ i) - H - k.t ≤ k.R0 * (H + k.t) := by
      have h1 := hmγ i
      have h2 : k.t * ((m:ℝ) * γ i) ≤ k.t * (k.G0 - k.Q * v i) :=
        mul_le_mul_of_nonneg_left h1 htpos.le
      have h3 : v i * (1 - k.Q * k.t) ≤ k.R0 * H := by
        rcases le_total 0 (v i) with hv0 | hv0
        · have : v i * (1 - k.Q * k.t) ≤ v i := by nlinarith only [hv0, hQt, mul_pos (by linarith : (0:ℝ) < k.Q) htpos]
          linarith [hvhi i]
        · have : v i * (1 - k.Q * k.t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv0 (by linarith)
          have : 0 ≤ k.R0 * H := mul_nonneg hR0pos.le hHnn
          linarith
      rw [hvdef] at h2 h3
      rw [hG0] at h2
      nlinarith only [h2, h3]
    have := mul_le_mul_of_nonneg_left key hcpos.le
    nlinarith only [this]
  · intro P hP0 hP1
    refine ⟨fun i => mul_nonneg hP0.le (hh0 i), ?_, ?_⟩
    · nlinarith only [hP0, hP1, hHL, hHnn]
    · intro i
      have := mul_le_mul_of_nonneg_left (hvhi i) hP0.le
      rw [hvdef] at this
      nlinarith only [this]
  · -- column bound
    intro j y hy
    have hxj := MNR55_update_mixed x hx j y hy
    have hdef0 : ∀ i, 0 ≤ deficitMix u (Function.update x j y) i (b i) :=
      fun i => MNR55_deficit_nonneg u hu _ hxj i (b i) (hb i)
    have hsub : ∑ i ∈ univ.erase j, γ i * deficitMix u (Function.update x j y) i (b i)
        ≤ ∑ i, γ i * deficitMix u (Function.update x j y) i (b i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun i _ _ => mul_nonneg (hγ0 i) (hdef0 i))
    have hγl : ∀ i, γ i ≤ 3 * lam' i := by
      intro i; rw [hγdef, div_le_iff₀ hZ0pos]
      have := mul_le_mul_of_nonneg_left (le_of_lt (hGv_hi i)) (hlam0 i)
      have := mul_le_mul_of_nonneg_left hZ0 (hlam0 i)
      nlinarith only [this, ‹lam' i * (k.G0 - k.Q * v i) ≤ lam' i * 3›, hlam0 i]
    have h3 : ∑ i, γ i * deficitMix u (Function.update x j y) i (b i)
        ≤ 3 * ∑ i, lam' i * deficitMix u (Function.update x j y) i (b i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => by
        have := mul_le_mul_of_nonneg_right (hγl i) (hdef0 i); linarith)
    have h4 := h511 j y hy
    have hmu : scaled u x + ctrl.mu (scaled u x) H = k.Su H - ctrl.d := by
      simp only [Controls.mu]; ring
    have h5 : k.Su H - ctrl.d < 13/5 := by
      have := hSuB H hHnn hHL; linarith
    rw [hmu] at h4
    have h6 : (k.Su H - ctrl.d) / m < 13/5/m := div_lt_div_of_pos_right h5 hmpos
    have h7 : 3 * (13/5/(m:ℝ)) < 9 / m := by
      rw [show 3 * (13/5/(m:ℝ)) = (39/5)/m by ring]; exact div_lt_div_of_pos_right (by norm_num) hmpos
    linarith
