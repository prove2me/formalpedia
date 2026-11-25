-- Prove2me | solution 1 for GlobalTheory.hsGrowth_exp_radius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:56.444011+00:00
-- url     : https://prove2.me/submissions/5b6798b8-b159-4c2e-9be1-e6c552d03c08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountGrowthExponentialRadii
import Theorems.Thm_GlobalTheory_hsGrowth_log_add_div_tendsto
import Theorems.Thm_GlobalTheory_hsGrowth_log_floor_le
import Theorems.Thm_GlobalTheory_T_tendsto_div_pow_of_choose_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (D e δ : ℕ) (N : ℕ → ℝ → ℕ) (κ t : ℝ), 0 < e → 0 < κ → κ ≤ 1 → 0 < t → (∀ m, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' → N m R ≤ N m R') → (∀ s : ℕ, s < e → ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, δ / ((e : ℝ) ^ D * D.factorial) * t - ε ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ∧ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ δ / ((e : ℝ) ^ D * D.factorial) * (t - Real.log κ / e) + ε := by
  intro D e δ N κ t he hκ hκ1 ht hmono h ε hε
  have h' : ∀ s : ℕ, ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ (s < e → ∀ (q : ℕ) (R : ℝ), 0 ≤ R →
      (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧
      N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) := by
    intro s
    by_cases hs : s < e
    · obtain ⟨c, c', C, C', h1, h2, h3⟩ := h s hs
      exact ⟨c, c', C, C', h1, h2, fun _ => h3⟩
    · exact ⟨0, 0, 1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose c c' C C' hC hC' hb using h'
  set L : ℝ := δ / ((e : ℝ) ^ D * D.factorial) with hL
  have hdiv : ∀ q s, s < e → (e * q + s) / e = q ∧ (e * q + s) % e = s := by
    intro q s hs
    constructor
    · rw [add_comm, Nat.add_mul_div_left _ _ he, Nat.div_eq_of_lt hs, zero_add]
    · rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have hlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D)
      atTop (𝓝 L) := by
    refine GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e - c (m % e) + D).choose D) he ?_
    intro s hs
    refine ⟨c s, 0, fun q => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hdiv (q + c s) s hs
      simp only [h1, h2, Nat.add_sub_cancel, le_refl]
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [h1, h2, add_zero]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))
  have hup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D)
      atTop (𝓝 L) := by
    refine GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e + c' (m % e) + D).choose D) he ?_
    intro s hs
    refine ⟨0, c' s, fun q => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [add_zero, h1, h2]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [h1, h2, le_refl]
  set B : ℝ := ∑ s ∈ Finset.range e, |Real.log (C s)| with hBdef
  set B' : ℝ := ∑ s ∈ Finset.range e, |Real.log (C' s)| with hB'def
  set P : ℝ := ∑ s ∈ Finset.range e, (c' s : ℝ) with hPdef
  set M : ℕ := ∑ s ∈ Finset.range e, c s with hMdef
  have hB : ∀ s, s < e → Real.log (C s) ≤ B := fun s hs => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun s => |Real.log (C s)|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.mpr hs))
  have hB' : ∀ s, s < e → |Real.log (C' s)| ≤ B' := fun s hs =>
    Finset.single_le_sum (f := fun s => |Real.log (C' s)|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.mpr hs)
  have hP : ∀ s, s < e → (c' s : ℝ) ≤ P := fun s hs =>
    Finset.single_le_sum (f := fun s => (c' s : ℝ)) (fun i _ => Nat.cast_nonneg _)
      (Finset.mem_range.mpr hs)
  have hlk : Real.log κ ≤ 0 := Real.log_nonpos hκ.le hκ1

  have hlowE : ∀ᶠ m : ℕ in atTop,
      ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
        (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) ≤
      Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop (e * M + 1)] with m hm
    have hm0' : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos _) hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm0'
    set s := m % e with hs_def
    have hse : s < e := Nat.mod_lt _ he
    have hcm : c s ≤ m / e := by
      have : M ≤ m / e := by
        rw [Nat.le_div_iff_mul_le he]
        rw [mul_comm]; linarith
      exact (Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr hse)).trans this
    set q := m / e - c s with hq
    have hqm : q ≤ m := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
    have hmq : e * (q + c s) + s = m := by
      rw [hq, Nat.sub_add_cancel hcm]; exact Nat.div_add_mod m e
    have hKpos : 0 < (q + D).choose D := Nat.choose_pos (by omega)
    have hKpos' : (0 : ℝ) < ((q + D).choose D : ℝ) := by exact_mod_cast hKpos
    have hCs := hC s
    set R : ℝ := Real.exp (t * m) / (C s * ((q + D).choose D : ℝ)) with hR
    have hRpos : 0 < R := by rw [hR]; positivity
    have hCKR : C s * ((q + D).choose D : ℝ) * R = Real.exp (t * m) := by
      rw [hR]; field_simp
    have hb1 := (hb s hse q R hRpos.le).1
    rw [hmq, hCKR] at hb1
    have hK1 : Real.log ((q + D).choose D : ℝ) ≤ D * Real.log ((m : ℝ) + D) := by
      rw [← Real.log_pow]
      apply Real.log_le_log hKpos'
      have : (q + D).choose D ≤ (m + D) ^ D :=
        (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
      exact_mod_cast this
    set K := (q + D).choose D with hK
    have hlogN : (δ * K : ℝ) * Real.log R ≤ Real.log (N m (Real.exp (t * m))) := by
      have h1 : R ≤ ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        have := Nat.lt_floor_add_one R
        have := Nat.cast_nonneg (α := ℝ) ⌊R⌋₊
        linarith
      have h2 : ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) ≤ N m (Real.exp (t * m)) := by
        exact_mod_cast hb1
      have h3 : (0 : ℝ) < (((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ) : ℝ) := by positivity
      calc (δ * K : ℝ) * Real.log R ≤ (δ * K : ℝ) * Real.log ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log hRpos h1) (by positivity)
        _ = Real.log ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) := by
            rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
        _ ≤ _ := Real.log_le_log h3 h2
    have hlogR : t * m - B - D * Real.log ((m : ℝ) + D) ≤ Real.log R := by
      rw [hR, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp,
        Real.log_mul hCs.ne' hKpos'.ne']
      linarith [hB s hse]
    have key : (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) ≤
        Real.log (N m (Real.exp (t * m))) :=
      (mul_le_mul_of_nonneg_left hlogR (by positivity)).trans hlogN
    rw [le_div_iff₀ (by positivity)]
    calc ((δ * K : ℕ) : ℝ) / (m : ℝ) ^ D * (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) *
          (m : ℝ) ^ (D + 1) = (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) := by
          push_cast; field_simp; ring
      _ ≤ _ := key

  have hupE : ∀ᶠ m : ℕ in atTop, Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤
      ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
        ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    set s := m % e with hs_def
    have hse : s < e := Nat.mod_lt _ he
    set q := m / e with hq
    have hmq : e * q + s = m := Nat.div_add_mod m e
    have hCs := hC' s
    set Y : ℝ := C' s * Real.exp (t * m) / κ ^ (q + c' s) with hY
    have hYpos : 0 < Y := by rw [hY]; positivity
    have hb2 := (hb s hse q (Real.exp (t * m)) (Real.exp_pos _).le).2
    rw [hmq, ← hY] at hb2
    set K := (q + c' s + D).choose D with hK
    have hlogN : Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|) := by
      have h0 : 0 ≤ Real.log 3 + |Real.log Y| := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); positivity
      rcases Nat.eq_zero_or_pos (N m (Real.exp (t * m))) with hN | hN
      · rw [hN, Nat.cast_zero, Real.log_zero]; positivity
      · calc Real.log (N m (Real.exp (t * m)))
            ≤ Real.log ((((2 * ⌊Y⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) :=
              Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hb2)
          _ = (δ * K : ℝ) * Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hsGrowth_log_floor_le hYpos) (by positivity)
    have hlogY : |Real.log Y| ≤ B' + t * m + (m / e + P) * (-Real.log κ) := by
      rw [hY, Real.log_div (by positivity) (by positivity),
        Real.log_mul hCs.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
      have hq1 : ((q : ℕ) : ℝ) ≤ (m : ℝ) / e := Nat.cast_div_le
      have hc1 := hP s hse
      have hx : ((q : ℝ) + c' s) * (-Real.log κ) ≤ ((m : ℝ) / e + P) * (-Real.log κ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have hx0 : 0 ≤ ((q : ℝ) + c' s) * (-Real.log κ) := mul_nonneg (by positivity) (by linarith)
      have ha := abs_le.mp (hB' s hse)
      have htm : 0 ≤ t * m := by positivity
      rw [abs_le]; push_cast; constructor <;> nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|) := hlogN
      _ ≤ (δ * K : ℝ) * (Real.log 3 + (B' + t * m + (m / e + P) * (-Real.log κ))) := by
          gcongr
      _ = ((δ * K : ℕ) : ℝ) / (m : ℝ) ^ D *
            ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e)) * (m : ℝ) ^ (D + 1) := by
          push_cast; field_simp; ring

  have hLlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
      (t - (B / m + D * (Real.log ((m : ℝ) + D) / m)))) atTop (𝓝 (L * t)) := by
    have h0 : Tendsto (fun m : ℕ => B / (m : ℝ) + D * (Real.log ((m : ℝ) + D) / m)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat B).add
        ((hsGrowth_log_add_div_tendsto D).const_mul (D : ℝ))
      simpa only [mul_zero, add_zero] using this
    have := hlow.mul ((tendsto_const_nhds (x := t)).sub h0)
    simpa only [sub_zero] using this
  have hLup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
      ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e))) atTop
      (𝓝 (L * (t - Real.log κ / e))) := by
    have := hup.mul ((tendsto_const_div_atTop_nhds_zero_nat (Real.log 3 + B' + P * (-Real.log κ))).add
      (tendsto_const_nhds (x := t - Real.log κ / e)))
    simpa only [zero_add] using this
  have e1 := hLlow.eventually (lt_mem_nhds (show L * t - ε < L * t by linarith))
  have e2 := hLup.eventually (gt_mem_nhds
    (show L * (t - Real.log κ / e) < L * (t - Real.log κ / e) + ε by linarith))
  filter_upwards [e1, e2, hlowE, hupE] with m h1 h2 h3 h4
  exact ⟨by linarith, by linarith⟩
end GlobalTheory
