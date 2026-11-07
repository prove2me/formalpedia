-- Prove2me | solution 1 for KumarSeidman.TwoType.example2_periodic_trajectory_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T09:39:42.30362+00:00
-- url     : https://prove2.me/submissions/1be9b2d8-0ecc-4c33-ae96-a94d8301f505

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2

namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory

namespace KS2
variable {S : KumarSeidman.TwoType.System} {T : S.Schedule}

theorem tr_y0 (hT : T.IsTrajectory) (b : S.Buffer) : T.y b 0 = 0 := hT.1 b
theorem tr_mono (hT : T.IsTrajectory) (b : S.Buffer) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    T.y b s ≤ T.y b t := hT.2.1 b hs (le_trans hs hst) hst
theorem tr_bal (hT : T.IsTrajectory) (b : S.Buffer) {t : ℝ} (ht : 0 ≤ t) :
    T.x b t = T.x b 0 + S.inflow T.y b t - T.y b t := hT.2.2.1 b t ht
theorem tr_nonneg (hT : T.IsTrajectory) (b : S.Buffer) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ T.x b t :=
  hT.2.2.2.1 b t ht
theorem tr_run0 (hT : T.IsTrajectory) (m : Fin S.M) : T.RunExists m 0 ∧ T.s m 0 = 0 :=
  hT.2.2.2.2.1 m
theorem tr_mach (hT : T.IsTrajectory) {m : Fin S.M} {k : ℕ} (h : T.RunExists m k) :
    S.mach (T.β m k) = m := hT.2.2.2.2.2.1 m k h
theorem tr_setup (hT : T.IsTrajectory) {m : Fin S.M} {k : ℕ} (h : T.RunExists m (k + 1)) :
    T.procStart m k ≤ T.s m (k + 1) := hT.2.2.2.2.2.2.1 m k h
theorem tr_cap (hT : T.IsTrajectory) (b : S.Buffer) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    T.y b t - T.y b s ≤
      (volume {σ | σ ∈ Set.Icc s t ∧ T.ProcessingBuffer (S.mach b) b σ}).toReal / S.procTime b :=
  hT.2.2.2.2.2.2.2.2.1 b s t hs hst
theorem tr_full (hT : T.IsTrajectory) (b : S.Buffer) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : ∀ σ ∈ Set.Ico s t, T.ProcessingBuffer (S.mach b) b σ ∧ 0 < T.x b σ) :
    T.y b t - T.y b s = (t - s) / S.procTime b :=
  hT.2.2.2.2.2.2.2.2.2 b s t hs hst h

theorem run_mono {m : Fin S.M} {k j : ℕ} (h : T.RunExists m k) (hj : j ≤ k) : T.RunExists m j :=
  lt_of_le_of_lt (by exact_mod_cast hj) h

theorem s_le_procStart (hδ : ∀ b b', 0 ≤ S.δ b b') (m : Fin S.M) (k : ℕ) :
    T.s m k ≤ T.procStart m k := by
  cases k with
  | zero => simp [procStart]
  | succ k => simp only [procStart]; linarith [hδ (T.β m k) (T.β m (k + 1))]

theorem s_mono (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') {m : Fin S.M} {k j : ℕ}
    (h : T.RunExists m k) (hj : j ≤ k) : T.s m j ≤ T.s m k := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hj with hj | hj
    · rw [hj]
    · have h1 := ih (run_mono h (Nat.le_succ k)) (by omega)
      have h2 := s_le_procStart (T := T) hδ m k
      have h3 := tr_setup hT h
      linarith

theorem procStart_le_s (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') {m : Fin S.M}
    {k j : ℕ} (h : T.RunExists m j) (hj : k < j) : T.procStart m k ≤ T.s m j := by
  have h1 := tr_setup hT (run_mono h hj)
  have h2 := s_mono hT hδ h hj
  linarith

theorem procStart_mono (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') {m : Fin S.M}
    {k j : ℕ} (h : T.RunExists m j) (hj : k ≤ j) : T.procStart m k ≤ T.procStart m j := by
  rcases Nat.eq_or_lt_of_le hj with rfl | hj
  · exact le_rfl
  · linarith [procStart_le_s hT hδ h hj, s_le_procStart (T := T) hδ m j]

/-- A run processing at `σ < procStart K` has index `< K`. -/
theorem idx_lt (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') {m : Fin S.M} {k K : ℕ}
    {σ : ℝ} (h : T.InProcessing m k σ) (hK : T.RunExists m K → σ < T.procStart m K) : k < K := by
  by_contra hc
  push Not at hc
  have hK' : T.RunExists m K := run_mono h.1 hc
  have := procStart_mono hT hδ h.1 hc
  linarith [h.2.1, hK hK']

/-- A run processing at `σ ≥ s K` has index `≥ K`. -/
theorem idx_ge (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') {m : Fin S.M} {k K : ℕ}
    {σ : ℝ} (h : T.InProcessing m k σ) (hK : T.RunExists m K) (hσ : T.s m K ≤ σ) : K ≤ k := by
  by_contra hc
  push Not at hc
  have h1 : T.RunExists m (k + 1) := run_mono hK hc
  have h2 := h.2.2 h1
  have h3 := s_mono hT hδ hK hc
  linarith

theorem cap (hT : T.IsTrajectory) (b : S.Buffer) {s t a : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hτ : 0 < S.procTime b)
    (ha : ∀ σ ∈ Set.Icc s t, T.ProcessingBuffer (S.mach b) b σ → a ≤ σ) :
    T.y b t - T.y b s ≤ max (t - a) 0 / S.procTime b := by
  refine (tr_cap hT b hs hst).trans (div_le_div_of_nonneg_right ?_ hτ.le)
  have hsub : {σ | σ ∈ Set.Icc s t ∧ T.ProcessingBuffer (S.mach b) b σ} ⊆
      Set.Icc (max a s) t := by
    intro σ hσ
    exact ⟨max_le (ha σ hσ.1 hσ.2) hσ.1.1, hσ.1.2⟩
  have h1 := measure_mono (μ := volume) hsub
  rw [Real.volume_Icc] at h1
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal'] at h2
  refine h2.trans ?_
  apply max_le_max _ le_rfl
  linarith [le_max_left a s]

theorem cap_zero (hT : T.IsTrajectory) (b : S.Buffer) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hτ : 0 < S.procTime b)
    (ha : ∀ σ ∈ Set.Icc s t, T.ProcessingBuffer (S.mach b) b σ → t ≤ σ) :
    T.y b t = T.y b s := by
  have := cap hT b hs hst hτ ha
  simp at this
  linarith [tr_mono hT b hs hst]

theorem cap_rate (hT : T.IsTrajectory) (b : S.Buffer) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hτ : 0 < S.procTime b) : T.y b t - T.y b s ≤ (t - s) / S.procTime b := by
  have := cap hT b hs hst hτ (a := s) (fun σ hσ _ => hσ.1)
  rwa [max_eq_left (by linarith)] at this

theorem xdiff (hT : T.IsTrajectory) (b : S.Buffer) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.x b t - T.x b s = (S.inflow T.y b t - S.inflow T.y b s) - (T.y b t - T.y b s) := by
  rw [tr_bal hT b ht, tr_bal hT b hs]; ring

/-- A buffer processed throughout `[p, t]`, empty at `p` and fed at rate at most `1/τ`,
stays empty. -/
theorem stays_zero (hT : T.IsTrajectory) (b : S.Buffer) {p t r : ℝ} (hp : 0 ≤ p) (hpt : p ≤ t)
    (hτ : 0 < S.procTime b) (hr0 : 0 ≤ r) (hr : r ≤ 1 / S.procTime b)
    (hin : ∀ u v, p ≤ u → u ≤ v → v ≤ t → S.inflow T.y b v - S.inflow T.y b u ≤ r * (v - u))
    (hproc : ∀ σ ∈ Set.Icc p t, T.ProcessingBuffer (S.mach b) b σ) (hx0 : T.x b p = 0) :
    T.x b t = 0 := by
  have hnn := tr_nonneg hT b (le_trans hp hpt)
  by_contra hne
  have hxt : 0 < T.x b t := lt_of_le_of_ne hnn (Ne.symm hne)
  set Z := {σ | σ ∈ Set.Icc p t ∧ T.x b σ = 0} with hZ
  have hZne : Z.Nonempty := ⟨p, ⟨le_rfl, hpt⟩, hx0⟩
  have hZbdd : BddAbove Z := ⟨t, fun σ hσ => hσ.1.2⟩
  set a := sSup Z with ha
  have hpa : p ≤ a := le_csSup hZbdd ⟨⟨le_rfl, hpt⟩, hx0⟩
  have hat : a ≤ t := csSup_le hZne (fun σ hσ => hσ.1.2)
  have hpos : ∀ σ, a < σ → σ ≤ t → 0 < T.x b σ := by
    intro σ h1 h2
    have hσ0 : 0 ≤ σ := by linarith
    rcases lt_or_eq_of_le (tr_nonneg hT b hσ0) with h | h
    · exact h
    · exfalso
      have : σ ≤ a := le_csSup hZbdd ⟨⟨by linarith, h2⟩, h.symm⟩
      linarith
  -- for every ε > 0, x t ≤ r * ε
  have key : ∀ ε > 0, T.x b t ≤ r * ε := by
    intro ε hε
    obtain ⟨z, hz, hza⟩ := exists_lt_of_lt_csSup hZne (show a - ε / 2 < a by linarith)
    have hza' : z ≤ a := le_csSup hZbdd hz
    set s := min (a + ε / 2) t with hs
    have has : a ≤ s := le_min (by linarith) hat
    have hst : s ≤ t := min_le_right _ _
    have hz0 : 0 ≤ z := le_trans hp hz.1.1
    have h1 : T.x b t ≤ T.x b s := by
      rcases lt_or_eq_of_le hst with hlt | heq
      · have has' : a < s := by
          rcases lt_or_eq_of_le has with h | h
          · exact h
          · exfalso; rw [hs] at h
            have : min (a + ε / 2) t = t := by
              by_contra hh
              have : min (a + ε / 2) t = a + ε / 2 := by
                rcases min_choice (a + ε / 2) t with h' | h'
                · exact h'
                · exact absurd h' hh
              linarith
            rw [hs] at hlt; linarith
        have hfull := tr_full hT b (by linarith) hst (fun σ hσ =>
          ⟨hproc σ ⟨by linarith [hσ.1], le_of_lt hσ.2⟩, hpos σ (by linarith [hσ.1]) (le_of_lt hσ.2)⟩)
        have hd := xdiff hT b (s := s) (t := t) (by linarith) (by linarith)
        have hi := hin s t (by linarith) hst le_rfl
        have : r * (t - s) ≤ (t - s) / S.procTime b := by
          rw [div_eq_mul_one_div, mul_comm (t - s)]
          exact mul_le_mul_of_nonneg_right hr (by linarith)
        linarith
      · rw [heq]
    have h2 : T.x b s ≤ r * ε := by
      have hd := xdiff hT b (s := z) (t := s) hz0 (by linarith)
      have hi := hin z s hz.1.1 (by linarith) hst
      have hm := tr_mono hT b hz0 (show z ≤ s by linarith)
      have hxz : T.x b z = 0 := hz.2
      have : r * (s - z) ≤ r * ε := mul_le_mul_of_nonneg_left (by
        have : s ≤ a + ε / 2 := min_le_left _ _
        linarith) hr0
      linarith
    linarith
  have := key (T.x b t / (2 * (r + 1))) (by positivity)
  have hlt : r * (T.x b t / (2 * (r + 1))) < T.x b t := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith


theorem other_buf (hT : T.IsTrajectory) (hC : T.IsClearing) {m : Fin S.M} {bX bY : S.Buffer}
    (honly : ∀ b, S.mach b = m → b = bX ∨ b = bY) {k : ℕ} (h : T.RunExists m (k + 1))
    (hk : T.β m k = bY) : T.β m (k + 1) = bX := by
  have h1 := ((hC m k (run_mono h (Nat.le_succ k))).2 h).2.1
  rcases honly _ (tr_mach hT h) with h2 | h2
  · exact h2
  · exact absurd (h2.trans hk.symm) h1

theorem other_buf' (hT : T.IsTrajectory) (hC : T.IsClearing) {m : Fin S.M} {bX bY : S.Buffer}
    (honly : ∀ b, S.mach b = m → b = bX ∨ b = bY) {k : ℕ} (h : T.RunExists m (k + 1))
    (hk : T.β m k = bX) : T.β m (k + 1) = bY := by
  have h1 := ((hC m k (run_mono h (Nat.le_succ k))).2 h).2.1
  rcases honly _ (tr_mach hT h) with h2 | h2
  · exact absurd (h2.trans hk.symm) h1
  · exact h2

/-- First switch: machine `m` starts on an empty buffer `bX` fed at unit rate while its other
buffer `bY` is nonempty; it switches to `bY` at once. -/
theorem first_switch (hT : T.IsTrajectory) (hC : T.IsClearing) (hδ : ∀ b b', 0 ≤ S.δ b b')
    {m : Fin S.M} {bX bY : S.Buffer} (hX : S.mach bX = m) (hY : S.mach bY = m) (hXY : bX ≠ bY)
    (honly : ∀ b, S.mach b = m → b = bX ∨ b = bY) (hβ0 : T.β m 0 = bX) (hx0 : T.x bX 0 = 0)
    (hτX : 0 < S.procTime bX) (hτX1 : S.procTime bX ≤ 1)
    (hinX : ∀ v, S.inflow T.y bX v = v) (hY0 : 0 < T.x bY 0)
    (hinY : ∀ u v, 0 ≤ u → u ≤ v → S.inflow T.y bY u ≤ S.inflow T.y bY v)
    (hτY : 0 < S.procTime bY) :
    T.RunExists m 1 ∧ T.s m 1 = 0 ∧ T.β m 1 = bY := by
  obtain ⟨hr0, hs0⟩ := tr_run0 hT m
  have hp0 : T.procStart m 0 = 0 := hs0
  have claim : ∀ t, 0 < t → (T.RunExists m 1 → t < T.s m 1) → False := by
    intro t ht hlt
    have hxX : T.x bX t = 0 := by
      refine stays_zero hT bX (p := 0) (r := 1) le_rfl ht.le hτX zero_le_one
        (by rw [le_div_iff₀ hτX]; linarith) (fun u v _ _ _ => by rw [hinX, hinX]; linarith)
        (fun σ hσ => ?_) hx0
      rw [hX]
      exact ⟨0, hβ0, hr0, by rw [hp0]; exact hσ.1, fun h1 => lt_of_le_of_lt hσ.2 (hlt h1)⟩
    have hyY : T.y bY t = T.y bY 0 := by
      refine cap_zero hT bY le_rfl ht.le hτY (fun σ hσ hp => ?_)
      rw [hY] at hp
      obtain ⟨k, hk, hkp⟩ := hp
      exfalso
      have : k < 1 := idx_lt hT hδ hkp (fun h1 => lt_of_le_of_lt hσ.2
        (lt_of_lt_of_le (hlt h1) (s_le_procStart hδ m 1)))
      obtain rfl : k = 0 := by omega
      exact hXY (hβ0.symm.trans hk)
    have hxY : 0 < T.x bY t := by
      have := xdiff hT bY (s := 0) (t := t) le_rfl ht.le
      have := hinY 0 t le_rfl ht.le
      linarith
    have hc := (hC m 0 hr0).1 t (by rw [hp0]; exact ht) hlt
    apply hc
    rw [hβ0]
    exact ⟨hxX, bY, hY, Ne.symm hXY, Or.inl hxY⟩
  have hr1 : T.RunExists m 1 := by
    by_contra h
    exact claim 1 one_pos (fun h' => absurd h' h)
  have hs1 : T.s m 1 = 0 := by
    have hge : 0 ≤ T.s m 1 := by have := tr_setup hT (k := 0) hr1; rw [hp0] at this; exact this
    by_contra hne
    have hpos : 0 < T.s m 1 := lt_of_le_of_ne hge (Ne.symm hne)
    exact claim (T.s m 1 / 2) (by linarith) (fun _ => by linarith)
  exact ⟨hr1, hs1, other_buf' hT hC honly hr1 hβ0⟩

/-- Processing of `bX` after the first switch happens only in runs `≥ 2`. -/
theorem procX_late (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b')
    {m : Fin S.M} {bX bY : S.Buffer} (hXY : bX ≠ bY)
    (hr1 : T.RunExists m 1) (hs1 : T.s m 1 = 0) (hβ1 : T.β m 1 = bY) {σ : ℝ} (hσ : 0 ≤ σ)
    (hp : T.ProcessingBuffer m bX σ) : T.RunExists m 2 ∧ T.procStart m 2 ≤ σ := by
  obtain ⟨k, hk, hkp⟩ := hp
  rcases k with _ | _ | k
  · have := hkp.2.2 hr1; linarith
  · exact absurd (hk.symm.trans hβ1) hXY
  · have h2 : T.RunExists m 2 := run_mono hkp.1 (by omega)
    exact ⟨h2, le_trans (procStart_mono hT hδ hkp.1 (by omega)) hkp.2.1⟩

theorem procY_cases (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b')
    {m : Fin S.M} {bX bY : S.Buffer} (hXY : bX ≠ bY) (hβ0 : T.β m 0 = bX)
    (hr1 : T.RunExists m 1) (hβ2 : T.RunExists m 2 → T.β m 2 = bX) {σ : ℝ}
    (hp : T.ProcessingBuffer m bY σ) :
    T.procStart m 1 ≤ σ ∧ (T.RunExists m 2 → σ < T.s m 2 ∨ (T.RunExists m 3 ∧ T.procStart m 3 ≤ σ)) := by
  obtain ⟨k, hk, hkp⟩ := hp
  rcases k with _ | _ | _ | k
  · exact absurd (hβ0.symm.trans hk) hXY
  · exact ⟨hkp.2.1, fun h2 => Or.inl (hkp.2.2 h2)⟩
  · exact absurd ((hβ2 hkp.1).symm.trans hk) hXY
  · refine ⟨le_trans (procStart_mono hT hδ hkp.1 (by omega)) hkp.2.1, fun _ => Or.inr
      ⟨run_mono hkp.1 (by omega), le_trans (procStart_mono hT hδ hkp.1 (by omega)) hkp.2.1⟩⟩


theorem machine_low (hT : T.IsTrajectory) (hC : T.IsClearing) (hδ : ∀ b b', 0 ≤ S.δ b b')
    {m : Fin S.M} {bX bY : S.Buffer} (hX : S.mach bX = m) (hY : S.mach bY = m) (hXY : bX ≠ bY)
    (honly : ∀ b, S.mach b = m → b = bX ∨ b = bY) (hβ0 : T.β m 0 = bX)
    (hr1 : T.RunExists m 1) (hs1 : T.s m 1 = 0) (hβ1 : T.β m 1 = bY)
    {d e : ℝ} (hd : T.procStart m 1 = d) (he : T.RunExists m 2 → T.procStart m 2 = T.s m 2 + e)
    (hτX : 0 < S.procTime bX) (hτY : 0 < S.procTime bY) (hY0 : 0 < T.x bY 0)
    (hinY : ∀ u v, 0 ≤ u → u ≤ v → S.inflow T.y bY u ≤ S.inflow T.y bY v) :
    (∀ t, 0 ≤ t → t < d + S.procTime bY * T.x bY 0 → 0 < T.x bY t) ∧
    (T.RunExists m 2 → T.β m 2 = bX ∧ d + S.procTime bY * T.x bY 0 ≤ T.s m 2) ∧
    (∀ t, 0 ≤ t → t ≤ d + S.procTime bY * T.x bY 0 + e → T.y bX t = T.y bX 0) := by
  have hβ2 : T.RunExists m 2 → T.β m 2 = bX := fun h2 => other_buf hT hC honly h2 hβ1
  have hpos : ∀ t, 0 ≤ t → t < d + S.procTime bY * T.x bY 0 → 0 < T.x bY t := by
    intro t ht htC
    have h1 := xdiff hT bY (s := 0) (t := t) le_rfl ht
    have h2 := hinY 0 t le_rfl ht
    have h3 := cap hT bY (s := 0) (t := t) (a := d) le_rfl ht hτY (fun σ _ hp => by
      rw [hY] at hp
      have := (procY_cases hT hδ hXY hβ0 hr1 hβ2 hp).1
      rw [hd] at this; exact this)
    have h4 : max (t - d) 0 / S.procTime bY < T.x bY 0 := by
      rw [div_lt_iff₀ hτY]
      rcases le_total (t - d) 0 with h | h
      · rw [max_eq_right h]; positivity
      · rw [max_eq_left h]; linarith
    linarith
  have hlow : T.RunExists m 2 → T.β m 2 = bX ∧ d + S.procTime bY * T.x bY 0 ≤ T.s m 2 := by
    intro h2
    refine ⟨hβ2 h2, ?_⟩
    have hex := ((hC m 1 hr1).2 h2).1
    rw [hβ1] at hex
    have hs2 : 0 ≤ T.s m 2 := by
      have := s_mono hT hδ h2 (Nat.zero_le 2); rw [(tr_run0 hT m).2] at this; exact this
    by_contra hlt
    push Not at hlt
    have := hpos _ hs2 hlt
    linarith
  refine ⟨hpos, hlow, ?_⟩
  intro t ht htP
  have h3 := cap hT bX (s := 0) (t := t) (a := d + S.procTime bY * T.x bY 0 + e) le_rfl ht hτX
    (fun σ hσ hp => by
      rw [hX] at hp
      obtain ⟨h2, hle⟩ := procX_late hT hδ hXY hr1 hs1 hβ1 hσ.1 hp
      rw [he h2] at hle
      linarith [(hlow h2).2])
  rw [max_eq_right (by linarith)] at h3
  simp at h3
  linarith [tr_mono hT bX le_rfl ht]

theorem machine_rest (hT : T.IsTrajectory) (hC : T.IsClearing) (hδ : ∀ b b', 0 ≤ S.δ b b')
    {m : Fin S.M} {bX bY : S.Buffer} (hX : S.mach bX = m) (hY : S.mach bY = m) (hXY : bX ≠ bY)
    (honly : ∀ b, S.mach b = m → b = bX ∨ b = bY) (hβ0 : T.β m 0 = bX)
    (hr1 : T.RunExists m 1) (hs1 : T.s m 1 = 0) (hβ1 : T.β m 1 = bY)
    {d e η Q : ℝ} (hd : T.procStart m 1 = d) (hd0 : 0 ≤ d)
    (he : T.RunExists m 2 → T.procStart m 2 = T.s m 2 + e)
    (hτX : 0 < S.procTime bX) (hτX1 : S.procTime bX < 1) (hτY : 0 < S.procTime bY)
    (hY0 : 0 < T.x bY 0) (hX0 : T.x bX 0 = 0)
    (hinY : ∀ u v, 0 ≤ u → u ≤ v → S.inflow T.y bY u ≤ S.inflow T.y bY v)
    (hCQ : d + S.procTime bY * T.x bY 0 < Q)
    (hinYc : ∀ t, 0 ≤ t → t ≤ Q → S.inflow T.y bY t = S.inflow T.y bY 0)
    (hinX : ∀ v, S.inflow T.y bX v = v)
    (hη : d + S.procTime bY * T.x bY 0 + e = η * (1 - S.procTime bX)) (hη0 : 0 < η) :
    T.RunExists m 2 ∧ T.s m 2 = d + S.procTime bY * T.x bY 0 ∧ T.β m 2 = bX ∧
      (T.RunExists m 3 → η ≤ T.s m 3) ∧ T.y bX η - T.y bX 0 = η ∧ T.x bX η = 0 ∧
      T.y bY η - T.y bY 0 = T.x bY 0 := by
  obtain ⟨hpos, hlow, hyX⟩ := machine_low hT hC hδ hX hY hXY honly hβ0 hr1 hs1 hβ1 hd he hτX hτY
    hY0 hinY
  set C := d + S.procTime bY * T.x bY 0 with hCdef
  have hCpos : 0 < C := by positivity
  have hdC : d < C := by have : 0 < S.procTime bY * T.x bY 0 := by positivity
                         linarith
  -- y_Y over [d, C] when run 2 does not start before C
  have hyYC : (T.RunExists m 2 → C ≤ T.s m 2) → T.y bY C - T.y bY 0 = T.x bY 0 := by
    intro hs2
    have hfull := tr_full hT bY (s := d) (t := C) hd0 hdC.le (fun σ hσ => by
      refine ⟨?_, hpos σ (by linarith [hσ.1]) hσ.2⟩
      rw [hY]
      exact ⟨1, hβ1, hr1, by rw [hd]; exact hσ.1, fun h2 => lt_of_lt_of_le hσ.2 (hs2 h2)⟩)
    have hyd := cap hT bY (s := 0) (t := d) (a := d) le_rfl hd0 hτY (fun σ _ hp => by
      rw [hY] at hp
      have := (procY_cases hT hδ hXY hβ0 hr1 (fun h2 => other_buf hT hC honly h2 hβ1) hp).1
      rw [hd] at this; exact this)
    simp at hyd
    have hq : (C - d) / S.procTime bY = T.x bY 0 := by
      rw [show C - d = S.procTime bY * T.x bY 0 by rw [hCdef]; ring]; field_simp
    have := tr_mono hT bY le_rfl hd0
    linarith
  -- existence and exact time of the second switch
  have claim : ∀ t, C < t → t ≤ Q → (T.RunExists m 2 → t < T.s m 2) → False := by
    intro t hCt htQ hlt
    have hyC := hyYC (fun h2 => le_of_lt (lt_trans hCt (hlt h2)))
    have hxC : T.x bY C = 0 := by
      have := xdiff hT bY (s := 0) (t := C) le_rfl hCpos.le
      rw [hinYc C hCpos.le hCQ.le] at this
      linarith
    have hxt : T.x bY t = 0 := by
      have := xdiff hT bY (s := C) (t := t) hCpos.le (by linarith)
      rw [hinYc C hCpos.le hCQ.le, hinYc t (by linarith) htQ] at this
      have := tr_mono hT bY hCpos.le hCt.le
      have := tr_nonneg hT bY (show 0 ≤ t by linarith)
      linarith
    have hc := (hC m 1 hr1).1 t (by rw [hd]; linarith) hlt
    apply hc
    rw [hβ1]
    exact ⟨hxt, bX, hX, hXY, Or.inr (fun σ hσ => by rw [hinX, hinX]; exact hσ)⟩
  have hr2 : T.RunExists m 2 := by
    by_contra h
    exact claim ((C + Q) / 2) (by linarith) (by linarith) (fun h' => absurd h' h)
  have hs2 : T.s m 2 = C := by
    have hge := (hlow hr2).2
    by_contra hne
    have hgt : C < T.s m 2 := lt_of_le_of_ne hge (Ne.symm hne)
    exact claim ((C + min (T.s m 2) Q) / 2) (by linarith [lt_min hgt hCQ])
      (by linarith [min_le_right (T.s m 2) Q, lt_min hgt hCQ])
      (fun _ => by linarith [min_le_left (T.s m 2) Q, lt_min hgt hCQ])
  have hβ2 := (hlow hr2).1
  have hP : T.procStart m 2 = C + e := by rw [he hr2, hs2]
  set P := C + e with hPdef
  have hPη : P < η := by nlinarith
  have hCP : C ≤ P := by rw [← hP, ← hs2]; exact s_le_procStart hδ m 2
  -- positivity of x_X on [C, η)
  have hcapX : ∀ t, 0 ≤ t → T.y bX t - T.y bX 0 ≤ max (t - P) 0 / S.procTime bX := by
    intro t ht
    exact cap hT bX le_rfl ht hτX (fun σ hσ hp => by
      rw [hX] at hp
      obtain ⟨_, hle⟩ := procX_late hT hδ hXY hr1 hs1 hβ1 hσ.1 hp
      rw [hP] at hle; exact hle)
  have hposX : ∀ t, C ≤ t → t < η → 0 < T.x bX t := by
    intro t hCt htη
    have h1 := xdiff hT bX (s := 0) (t := t) le_rfl (by linarith)
    rw [hinX, hinX, hX0] at h1
    have h2 := hcapX t (by linarith)
    have h3 : max (t - P) 0 / S.procTime bX < t := by
      rw [div_lt_iff₀ hτX]
      rcases le_total (t - P) 0 with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    linarith
  have hs3 : T.RunExists m 3 → η ≤ T.s m 3 := by
    intro h3
    have hex := ((hC m 2 hr2).2 h3).1
    rw [hβ2] at hex
    have : P ≤ T.s m 3 := by rw [← hP]; exact tr_setup hT h3
    by_contra hlt
    push Not at hlt
    have := hposX _ (by linarith) hlt
    linarith
  have hfullX := tr_full hT bX (s := P) (t := η) (by linarith) hPη.le (fun σ hσ => by
    refine ⟨?_, hposX σ (by linarith [hσ.1]) hσ.2⟩
    rw [hX]
    exact ⟨2, hβ2, hr2, by rw [hP]; exact hσ.1, fun h3 => lt_of_lt_of_le hσ.2 (hs3 h3)⟩)
  have hyP := hyX P (by linarith) le_rfl
  have hyη : T.y bX η - T.y bX 0 = η := by
    rw [← hyP]
    rw [hfullX, div_eq_iff hτX.ne']
    linarith
  have hxη : T.x bX η = 0 := by
    have h1 := xdiff hT bX (s := 0) (t := η) le_rfl hη0.le
    rw [hinX, hinX, hX0] at h1
    linarith
  have hyYη : T.y bY η - T.y bY 0 = T.x bY 0 := by
    have h1 := hyYC (fun _ => hs2.ge)
    have h2 := cap hT bY (s := C) (t := η) (a := η) hCpos.le (by linarith) hτY (fun σ hσ hp => by
      rw [hY] at hp
      rcases (procY_cases hT hδ hXY hβ0 hr1 (fun _ => hβ2) hp).2 hr2 with h | ⟨h3, h4⟩
      · rw [hs2] at h; linarith [hσ.1]
      · linarith [s_le_procStart (T := T) hδ m 3, hs3 h3])
    simp at h2
    linarith [tr_mono hT bY hCpos.le (show C ≤ η by linarith)]
  exact ⟨hr2, hs2, hβ2, hs3, hyη, hxη, hyYη⟩

end KS2
end KumarSeidman.TwoType


namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory

namespace KS2
variable {S : KumarSeidman.TwoType.System} {T : S.Schedule}

/-- A buffer processed throughout `[p, t]`, empty at `p` and fed at rate at most `1/τ`,
stays empty. -/
theorem stays_zero' (hT : T.IsTrajectory) (b : S.Buffer) {p t r : ℝ} (hp : 0 ≤ p) (hpt : p ≤ t)
    (hτ : 0 < S.procTime b) (hr0 : 0 ≤ r) (hr : r ≤ 1 / S.procTime b)
    (hin : ∀ u v, p ≤ u → u ≤ v → v ≤ t → S.inflow T.y b v - S.inflow T.y b u ≤ r * (v - u))
    (hproc : ∀ σ ∈ Set.Ico p t, T.ProcessingBuffer (S.mach b) b σ) (hx0 : T.x b p = 0) :
    T.x b t = 0 := by
  have hnn := tr_nonneg hT b (le_trans hp hpt)
  by_contra hne
  have hxt : 0 < T.x b t := lt_of_le_of_ne hnn (Ne.symm hne)
  set Z := {σ | σ ∈ Set.Icc p t ∧ T.x b σ = 0} with hZ
  have hZne : Z.Nonempty := ⟨p, ⟨le_rfl, hpt⟩, hx0⟩
  have hZbdd : BddAbove Z := ⟨t, fun σ hσ => hσ.1.2⟩
  set a := sSup Z with ha
  have hpa : p ≤ a := le_csSup hZbdd ⟨⟨le_rfl, hpt⟩, hx0⟩
  have hat : a ≤ t := csSup_le hZne (fun σ hσ => hσ.1.2)
  have hpos : ∀ σ, a < σ → σ ≤ t → 0 < T.x b σ := by
    intro σ h1 h2
    have hσ0 : 0 ≤ σ := by linarith
    rcases lt_or_eq_of_le (tr_nonneg hT b hσ0) with h | h
    · exact h
    · exfalso
      have : σ ≤ a := le_csSup hZbdd ⟨⟨by linarith, h2⟩, h.symm⟩
      linarith
  -- for every ε > 0, x t ≤ r * ε
  have key : ∀ ε > 0, T.x b t ≤ r * ε := by
    intro ε hε
    obtain ⟨z, hz, hza⟩ := exists_lt_of_lt_csSup hZne (show a - ε / 2 < a by linarith)
    have hza' : z ≤ a := le_csSup hZbdd hz
    set s := min (a + ε / 2) t with hs
    have has : a ≤ s := le_min (by linarith) hat
    have hst : s ≤ t := min_le_right _ _
    have hz0 : 0 ≤ z := le_trans hp hz.1.1
    have h1 : T.x b t ≤ T.x b s := by
      rcases lt_or_eq_of_le hst with hlt | heq
      · have has' : a < s := by
          rcases lt_or_eq_of_le has with h | h
          · exact h
          · exfalso; rw [hs] at h
            have : min (a + ε / 2) t = t := by
              by_contra hh
              have : min (a + ε / 2) t = a + ε / 2 := by
                rcases min_choice (a + ε / 2) t with h' | h'
                · exact h'
                · exact absurd h' hh
              linarith
            rw [hs] at hlt; linarith
        have hfull := tr_full hT b (by linarith) hst (fun σ hσ =>
          ⟨hproc σ ⟨by linarith [hσ.1], hσ.2⟩, hpos σ (by linarith [hσ.1]) (le_of_lt hσ.2)⟩)
        have hd := xdiff hT b (s := s) (t := t) (by linarith) (by linarith)
        have hi := hin s t (by linarith) hst le_rfl
        have : r * (t - s) ≤ (t - s) / S.procTime b := by
          rw [div_eq_mul_one_div, mul_comm (t - s)]
          exact mul_le_mul_of_nonneg_right hr (by linarith)
        linarith
      · rw [heq]
    have h2 : T.x b s ≤ r * ε := by
      have hd := xdiff hT b (s := z) (t := s) hz0 (by linarith)
      have hi := hin z s hz.1.1 (by linarith) hst
      have hm := tr_mono hT b hz0 (show z ≤ s by linarith)
      have hxz : T.x b z = 0 := hz.2
      have : r * (s - z) ≤ r * ε := mul_le_mul_of_nonneg_left (by
        have : s ≤ a + ε / 2 := min_le_left _ _
        linarith) hr0
      linarith
    linarith
  have := key (T.x b t / (2 * (r + 1))) (by positivity)
  have hlt : r * (T.x b t / (2 * (r + 1))) < T.x b t := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith


/-- First switch: machine `m` starts on an empty buffer `bX` fed at unit rate while its other
buffer `bY` is nonempty; it switches to `bY` at once. -/
theorem first_switch' (hT : T.IsTrajectory) (hC : T.IsClearing) (hδ : ∀ b b', 0 ≤ S.δ b b')
    {m : Fin S.M} {bX bY : S.Buffer} (hX : S.mach bX = m) (hY : S.mach bY = m) (hXY : bX ≠ bY)
    (honly : ∀ b, S.mach b = m → b = bX ∨ b = bY) (hβ0 : T.β m 0 = bX) (hx0 : T.x bX 0 = 0)
    (hτX : 0 < S.procTime bX) (hτX1 : S.procTime bX ≤ 1)
    {W : ℝ} (hW : 0 < W)
    (hinX : ∀ u v, 0 ≤ u → u ≤ v → v ≤ W → S.inflow T.y bX v - S.inflow T.y bX u ≤ 1 * (v - u)) (hY0 : 0 < T.x bY 0)
    (hinY : ∀ u v, 0 ≤ u → u ≤ v → S.inflow T.y bY u ≤ S.inflow T.y bY v)
    (hτY : 0 < S.procTime bY) :
    T.RunExists m 1 ∧ T.s m 1 = 0 ∧ T.β m 1 = bY := by
  obtain ⟨hr0, hs0⟩ := tr_run0 hT m
  have hp0 : T.procStart m 0 = 0 := hs0
  have claim : ∀ t, 0 < t → t ≤ W → (T.RunExists m 1 → t < T.s m 1) → False := by
    intro t ht htW hlt
    have hxX : T.x bX t = 0 := by
      refine stays_zero' hT bX (p := 0) (r := 1) le_rfl ht.le hτX zero_le_one
        (by rw [le_div_iff₀ hτX]; linarith) (fun u v hu huv hv => hinX u v hu huv (le_trans hv htW))
        (fun σ hσ => ?_) hx0
      rw [hX]
      exact ⟨0, hβ0, hr0, by rw [hp0]; exact hσ.1, fun h1 => lt_trans hσ.2 (hlt h1)⟩
    have hyY : T.y bY t = T.y bY 0 := by
      refine cap_zero hT bY le_rfl ht.le hτY (fun σ hσ hp => ?_)
      rw [hY] at hp
      obtain ⟨k, hk, hkp⟩ := hp
      exfalso
      have : k < 1 := idx_lt hT hδ hkp (fun h1 => lt_of_le_of_lt hσ.2
        (lt_of_lt_of_le (hlt h1) (s_le_procStart hδ m 1)))
      obtain rfl : k = 0 := by omega
      exact hXY (hβ0.symm.trans hk)
    have hxY : 0 < T.x bY t := by
      have := xdiff hT bY (s := 0) (t := t) le_rfl ht.le
      have := hinY 0 t le_rfl ht.le
      linarith
    have hc := (hC m 0 hr0).1 t (by rw [hp0]; exact ht) hlt
    apply hc
    rw [hβ0]
    exact ⟨hxX, bY, hY, Ne.symm hXY, Or.inl hxY⟩
  have hr1 : T.RunExists m 1 := by
    by_contra h
    exact claim W hW le_rfl (fun h' => absurd h' h)
  have hs1 : T.s m 1 = 0 := by
    have hge : 0 ≤ T.s m 1 := by have := tr_setup hT (k := 0) hr1; rw [hp0] at this; exact this
    by_contra hne
    have hpos : 0 < T.s m 1 := lt_of_le_of_ne hge (Ne.symm hne)
    exact claim (min (T.s m 1) W / 2) (by have := lt_min hpos hW; linarith)
      (by have := min_le_right (T.s m 1) W; have := lt_min hpos hW; linarith)
      (fun _ => by have := min_le_left (T.s m 1) W; have := lt_min hpos hW; linarith)
  exact ⟨hr1, hs1, other_buf' hT hC honly hr1 hβ0⟩


/-- A run on `bA` started processing at `p` with `x_A(p) = X > 0`, inflow at exact rate `r`:
the buffer empties exactly at `c` and the run lasts at least until `c`. -/
theorem clear_low (hT : T.IsTrajectory) (hC : T.IsClearing)
    {m : Fin S.M} {bA : S.Buffer} (hA : S.mach bA = m) {k : ℕ} (hk : T.RunExists m k)
    (hβ : T.β m k = bA) {p X c r : ℝ} (hp : T.procStart m k = p) (hp0 : 0 ≤ p)
    (hτ : 0 < S.procTime bA) (hX : T.x bA p = X) (hX0 : 0 < X) (hr : r < 1 / S.procTime bA)
    (hc : (c - p) * (1 / S.procTime bA - r) = X)
    (hin : ∀ u v, p ≤ u → u ≤ v → v ≤ c → S.inflow T.y bA v - S.inflow T.y bA u = r * (v - u)) :
    (T.RunExists m (k + 1) → c ≤ T.s m (k + 1)) ∧ T.x bA c = 0 ∧
      T.y bA c - T.y bA p = (c - p) / S.procTime bA ∧ (∀ t, p ≤ t → t < c → 0 < T.x bA t) ∧
      p < c := by
  have hq : 0 < 1 / S.procTime bA - r := by linarith
  have hpc : p < c := by
    by_contra h
    push Not at h
    have : (c - p) * (1 / S.procTime bA - r) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hq.le
    linarith
  have hpos : ∀ t, p ≤ t → t < c → 0 < T.x bA t := by
    intro t hpt htc
    have h1 := xdiff hT bA (s := p) (t := t) hp0 (by linarith)
    have h2 := hin p t le_rfl hpt htc.le
    have h3 := cap_rate hT bA hp0 hpt hτ
    have h4 : (t - p) * (1 / S.procTime bA - r) < X := by
      rw [← hc]; exact mul_lt_mul_of_pos_right (by linarith) hq
    have h5 : (t - p) / S.procTime bA = (t - p) * (1 / S.procTime bA) := by ring
    nlinarith
  have hlow : T.RunExists m (k + 1) → c ≤ T.s m (k + 1) := by
    intro h1
    have hex := ((hC m k hk).2 h1).1
    rw [hβ] at hex
    have : p ≤ T.s m (k + 1) := by rw [← hp]; exact tr_setup hT h1
    by_contra hlt
    push Not at hlt
    have := hpos _ this hlt
    linarith
  have hfull := tr_full hT bA (s := p) (t := c) hp0 hpc.le (fun σ hσ => by
    refine ⟨?_, hpos σ hσ.1 hσ.2⟩
    rw [hA]
    exact ⟨k, hβ, hk, by rw [hp]; exact hσ.1, fun h1 => lt_of_lt_of_le hσ.2 (hlow h1)⟩)
  refine ⟨hlow, ?_, hfull, hpos, hpc⟩
  have h1 := xdiff hT bA (s := p) (t := c) hp0 (by linarith)
  have h2 := hin p c le_rfl hpc.le le_rfl
  have h5 : (c - p) / S.procTime bA = (c - p) * (1 / S.procTime bA) := by ring
  nlinarith

theorem clear_switch (hT : T.IsTrajectory) (hC : T.IsClearing)
    {m : Fin S.M} {bA bB : S.Buffer} (hA : S.mach bA = m) (hB : S.mach bB = m) (hAB : bA ≠ bB)
    (honly : ∀ b, S.mach b = m → b = bA ∨ b = bB) {k : ℕ} (hk : T.RunExists m k)
    (hβ : T.β m k = bA) {p X c r W : ℝ} (hp : T.procStart m k = p) (hp0 : 0 ≤ p)
    (hτ : 0 < S.procTime bA) (hX : T.x bA p = X) (hX0 : 0 < X) (hr : r < 1 / S.procTime bA)
    (hr0 : 0 ≤ r) (hc : (c - p) * (1 / S.procTime bA - r) = X) (hcW : c < W)
    (hin : ∀ u v, p ≤ u → u ≤ v → v ≤ W → S.inflow T.y bA v - S.inflow T.y bA u = r * (v - u))
    (hdem : ∀ t, c < t → t < W → (T.RunExists m (k + 1) → t < T.s m (k + 1)) → T.Demanding bB t) :
    T.RunExists m (k + 1) ∧ T.s m (k + 1) = c ∧ T.β m (k + 1) = bB := by
  obtain ⟨hlow, hxc, -, -, hpc⟩ := clear_low hT hC hA hk hβ hp hp0 hτ hX hX0 hr hc
    (fun u v hu huv hv => hin u v hu huv (by linarith))
  have claim : ∀ t, c < t → t < W → (T.RunExists m (k + 1) → t < T.s m (k + 1)) → False := by
    intro t hct htW hlt
    have hxt : T.x bA t = 0 := by
      refine stays_zero' hT bA (p := c) (r := r) (by linarith) hct.le hτ hr0 hr.le
        (fun u v hu huv hv => (hin u v (by linarith) huv (by linarith)).le) (fun σ hσ => ?_) hxc
      rw [hA]
      exact ⟨k, hβ, hk, by rw [hp]; linarith [hσ.1], fun h1 => lt_trans hσ.2 (hlt h1)⟩
    have hcl := (hC m k hk).1 t (by rw [hp]; linarith) hlt
    apply hcl
    rw [hβ]
    exact ⟨hxt, bB, hB, Ne.symm hAB, hdem t hct htW hlt⟩
  have hr1 : T.RunExists m (k + 1) := by
    by_contra h
    exact claim ((c + W) / 2) (by linarith) (by linarith) (fun h' => absurd h' h)
  have hs : T.s m (k + 1) = c := by
    have hge := hlow hr1
    by_contra hne
    have hgt : c < T.s m (k + 1) := lt_of_le_of_ne hge (Ne.symm hne)
    have := lt_min hgt hcW
    exact claim ((c + min (T.s m (k + 1)) W) / 2) (by linarith)
      (by linarith [min_le_right (T.s m (k + 1)) W])
      (fun _ => by linarith [min_le_left (T.s m (k + 1)) W])
  exact ⟨hr1, hs, other_buf' hT hC honly hr1 hβ⟩

end KS2
end KumarSeidman.TwoType


namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory

namespace KS2

section Ex2
variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}

local notation "SS" => example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄

theorem ex_cases (P : (SS).Buffer → Prop) (h1 : P b₁) (h2 : P b₂) (h3 : P b₃) (h4 : P b₄) :
    ∀ b, P b := by
  intro b
  obtain ⟨p, i⟩ := b
  fin_cases p <;> fin_cases i
  exacts [h1, h2, h3, h4]

theorem ex_hδ (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄) :
    ∀ b b' : (SS).Buffer, 0 ≤ (SS).δ b b' := by
  intro b b'
  revert b'
  refine ex_cases _ ?_ ?_ ?_ ?_
  · show 0 ≤ ite (b = b₁) 0 δ₁; split_ifs <;> linarith
  · show 0 ≤ ite (b = b₂) 0 δ₂; split_ifs <;> linarith
  · show 0 ≤ ite (b = b₃) 0 δ₃; split_ifs <;> linarith
  · show 0 ≤ ite (b = b₄) 0 δ₄; split_ifs <;> linarith

theorem ex_only₁ (b : (SS).Buffer) (h : (SS).mach b = m₁) : b = b₁ ∨ b = b₄ := by
  obtain ⟨p, i⟩ := b
  fin_cases p <;> fin_cases i <;> simp_all [System.mach, example2, m₁, b₁, b₄]

theorem ex_only₂ (b : (SS).Buffer) (h : (SS).mach b = m₂) : b = b₃ ∨ b = b₂ := by
  obtain ⟨p, i⟩ := b
  fin_cases p <;> fin_cases i <;> simp_all [System.mach, example2, m₂, b₂, b₃]

theorem ex_b14 : (b₁ : (SS).Buffer) ≠ b₄ := fun h => by
  have := congrArg (fun b : (SS).Buffer => (b.1 : ℕ)) h; exact absurd this (by simp [b₁, b₄])
theorem ex_b32 : (b₃ : (SS).Buffer) ≠ b₂ := fun h => by
  have := congrArg (fun b : (SS).Buffer => (b.1 : ℕ)) h; exact absurd this (by simp [b₃, b₂])

theorem ex_in₁ (y : (SS).Buffer → ℝ → ℝ) (t : ℝ) : (SS).inflow y b₁ t = t := by
  simp [System.inflow, b₁, example2]
theorem ex_in₂ (y : (SS).Buffer → ℝ → ℝ) (t : ℝ) : (SS).inflow y b₂ t = y b₁ t := by
  simp [System.inflow, b₁, b₂, example2]
theorem ex_in₃ (y : (SS).Buffer → ℝ → ℝ) (t : ℝ) : (SS).inflow y b₃ t = t := by
  simp [System.inflow, b₃, example2]
theorem ex_in₄ (y : (SS).Buffer → ℝ → ℝ) (t : ℝ) : (SS).inflow y b₄ t = y b₃ t := by
  simp [System.inflow, b₃, b₄, example2]

theorem ex_δ14 : (SS).δ b₁ b₄ = δ₄ := by simp [example2, b₁, b₄]
theorem ex_δ41 : (SS).δ b₄ b₁ = δ₁ := by simp [example2, b₁, b₄]
theorem ex_δ32 : (SS).δ b₃ b₂ = δ₂ := by simp [example2, b₃, b₂]
theorem ex_δ23 : (SS).δ b₂ b₃ = δ₃ := by simp [example2, b₃, b₂]

theorem ex_only₁r (b : (SS).Buffer) (h : (SS).mach b = m₁) : b = b₄ ∨ b = b₁ :=
  (ex_only₁ b h).symm
theorem ex_only₂r (b : (SS).Buffer) (h : (SS).mach b = m₂) : b = b₂ ∨ b = b₃ :=
  (ex_only₂ b h).symm
theorem ex_pt₁ : (SS).procTime b₁ = τ₁ := rfl
theorem ex_pt₂ : (SS).procTime b₂ = τ₂ := rfl
theorem ex_pt₃ : (SS).procTime b₃ = τ₃ := rfl
theorem ex_pt₄ : (SS).procTime b₄ = τ₄ := rfl

end Ex2

end KS2
end KumarSeidman.TwoType


namespace KumarSeidman.TwoType
namespace KS2
open MeasureTheory

/-- `V PS t` is the Lebesgue measure of `PS ∩ [0, t]`. -/
noncomputable def V (PS : Set ℝ) (t : ℝ) : ℝ := (volume (PS ∩ Set.Icc 0 t)).toReal

theorem vol_fin (PS : Set ℝ) (s t : ℝ) : volume (PS ∩ Set.Icc s t) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_right)

theorem V_zero0 (PS : Set ℝ) : V PS 0 = 0 := by
  unfold V
  have : volume (PS ∩ Set.Icc (0 : ℝ) 0) = 0 :=
    measure_mono_null Set.inter_subset_right (by simp)
  rw [this]; rfl

theorem V_mono (PS : Set ℝ) {s t : ℝ} (hst : s ≤ t) : V PS s ≤ V PS t :=
  ENNReal.toReal_mono (vol_fin PS 0 t)
    (measure_mono (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc le_rfl hst)))

theorem V_cap (PS : Set ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    V PS t - V PS s ≤ (volume (PS ∩ Set.Icc s t)).toReal := by
  unfold V
  have hsub : PS ∩ Set.Icc 0 t ⊆ (PS ∩ Set.Icc 0 s) ∪ (PS ∩ Set.Icc s t) := by
    intro σ ⟨h1, h2, h3⟩
    rcases le_total σ s with h | h
    · exact Or.inl ⟨h1, h2, h⟩
    · exact Or.inr ⟨h1, h, h3⟩
  have h1 := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨vol_fin PS 0 s, vol_fin PS s t⟩) h1
  rw [ENNReal.toReal_add (vol_fin PS 0 s) (vol_fin PS s t)] at h2
  linarith

theorem V_full (PS : Set ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (h : Set.Ioo s t ⊆ PS) :
    V PS t - V PS s = t - s := by
  apply le_antisymm
  · refine (V_cap PS hs hst).trans ?_
    have := ENNReal.toReal_mono (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono (μ := volume) (Set.inter_subset_right : PS ∩ Set.Icc s t ⊆ Set.Icc s t))
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at this
    exact this
  · unfold V
    have hsub : (PS ∩ Set.Icc 0 s) ∪ Set.Ioo s t ⊆ PS ∩ Set.Icc 0 t := by
      rintro σ (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2, le_trans h3 hst⟩
      · exact ⟨h ⟨h1, h2⟩, by linarith, h2.le⟩
    have hdis : Disjoint (PS ∩ Set.Icc 0 s) (Set.Ioo s t) := by
      rw [Set.disjoint_left]
      rintro σ ⟨_, _, h3⟩ ⟨h4, _⟩
      linarith
    have h1 := measure_mono (μ := volume) hsub
    rw [measure_union hdis measurableSet_Ioo, Real.volume_Ioo] at h1
    have h2 := ENNReal.toReal_mono (vol_fin PS 0 t) h1
    rw [ENNReal.toReal_add (vol_fin PS 0 s) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at h2
    linarith

theorem V_zero (PS : Set ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : ∀ σ ∈ Set.Ioo s t, σ ∉ PS) : V PS t = V PS s := by
  apply le_antisymm _ (V_mono PS hst)
  have h1 := V_cap PS hs hst
  have hnull : volume (PS ∩ Set.Icc s t) = 0 := by
    apply measure_mono_null (t := {s} ∪ {t})
    · intro σ ⟨h1, h2, h3⟩
      rcases eq_or_lt_of_le h2 with e | e
      · exact Or.inl e.symm
      · rcases eq_or_lt_of_le h3 with e' | e'
        · exact Or.inr e'
        · exact absurd h1 (h σ ⟨e, e'⟩)
    · exact measure_union_null (by simp) (by simp)
  rw [hnull] at h1
  simp at h1
  linarith

/-- The periodic set `⋃ₖ [kη + c, kη + d)`. -/
def PSet (η c d : ℝ) : Set ℝ := {σ | ∃ k : ℕ, (k : ℝ) * η + c ≤ σ ∧ σ < (k : ℝ) * η + d}

theorem per_in {η c d : ℝ} (n : ℕ) {σ : ℝ} (h : σ ∈ Set.Ioo ((n : ℝ) * η + c) ((n : ℝ) * η + d)) :
    σ ∈ PSet η c d := ⟨n, h.1.le, h.2⟩

theorem per_out {η c d a b : ℝ} (hη : 0 < η) (hc : 0 ≤ c) (hd : d ≤ η) (ha : 0 ≤ a) (hb : b ≤ η)
    (hab : b ≤ c ∨ d ≤ a) (n : ℕ) {σ : ℝ} (h : σ ∈ Set.Ioo ((n : ℝ) * η + a) ((n : ℝ) * η + b)) :
    σ ∉ PSet η c d := by
  rintro ⟨k, hk1, hk2⟩
  obtain ⟨h1, h2⟩ := h
  rcases lt_trichotomy k n with hkn | rfl | hkn
  · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    nlinarith
  · rcases hab with hab | hab <;> linarith
  · have : (n : ℝ) + 1 ≤ k := by exact_mod_cast hkn
    nlinarith

/-- Within one period, `V(PSet c d)` increases by `clamp(t - nη - c, 0, d - c)`. -/
theorem V_per_step {η c d : ℝ} (hη : 0 < η) (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ η) (n : ℕ)
    {t : ℝ} (h1 : (n : ℝ) * η ≤ t) (h2 : t ≤ (n : ℝ) * η + η) :
    V (PSet η c d) t - V (PSet η c d) ((n : ℝ) * η) =
      max 0 (min (t - (n : ℝ) * η - c) (d - c)) := by
  have hn0 : 0 ≤ (n : ℝ) * η := by positivity
  rcases le_total t ((n : ℝ) * η + c) with ht | ht
  · rw [V_zero _ hn0 h1 (fun σ hσ => per_out hη hc hd le_rfl (b := c) (by linarith) (Or.inl le_rfl) n
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)]
    rw [max_eq_left (min_le_of_left_le (by linarith))]; ring
  · have hzc : V (PSet η c d) ((n : ℝ) * η + c) = V (PSet η c d) ((n : ℝ) * η) :=
      V_zero _ hn0 (by linarith) (fun σ hσ => per_out hη hc hd le_rfl (b := c) (by linarith)
        (Or.inl le_rfl) n ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
    rcases le_total t ((n : ℝ) * η + d) with ht' | ht'
    · have hf := V_full (PSet η c d) (s := (n : ℝ) * η + c) (t := t) (by linarith) ht
        (fun σ hσ => per_in n ⟨hσ.1, by linarith [hσ.2]⟩)
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      linarith
    · have hf := V_full (PSet η c d) (s := (n : ℝ) * η + c) (t := (n : ℝ) * η + d) (by linarith)
        (by linarith) (fun σ hσ => per_in n hσ)
      have hz := V_zero (PSet η c d) (s := (n : ℝ) * η + d) (t := t) (by linarith) ht'
        (fun σ hσ => per_out hη hc hd (a := d) (b := η) (by linarith) le_rfl (Or.inr le_rfl) n
          ⟨hσ.1, by linarith [hσ.2]⟩)
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      linarith

theorem V_per_n {η c d : ℝ} (hη : 0 < η) (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ η) (n : ℕ) :
    V (PSet η c d) ((n : ℝ) * η) = n * (d - c) := by
  induction n with
  | zero => simp [V_zero0]
  | succ n ih =>
    have := V_per_step hη hc hcd hd n (t := (n : ℝ) * η + η) (by linarith) le_rfl
    rw [min_eq_right (by linarith), max_eq_right (by linarith), ih] at this
    push_cast
    rw [show ((n : ℝ) + 1) * η = (n : ℝ) * η + η by ring]
    linarith

end KS2
end KumarSeidman.TwoType


namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory Filter

namespace KS2

/-- Run start times of a machine in the periodic regime: run `2n+1` starts at `nη`, run
`2n+2` at `nη + D`, run `0` at `0`. -/
noncomputable def ps (η D : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k % 2 = 1 then (((k - 1) / 2 : ℕ) : ℝ) * η
  else (((k - 2) / 2 : ℕ) : ℝ) * η + D

theorem ps_zero (η D : ℝ) : ps η D 0 = 0 := by simp [ps]
theorem ps_odd (η D : ℝ) (n : ℕ) : ps η D (2 * n + 1) = (n : ℝ) * η := by
  simp only [ps, show 2 * n + 1 ≠ 0 by omega, if_false, show (2 * n + 1) % 2 = 1 by omega, if_true,
    show (2 * n + 1 - 1) / 2 = n by omega]
theorem ps_even (η D : ℝ) (n : ℕ) : ps η D (2 * n + 2) = (n : ℝ) * η + D := by
  unfold ps
  rw [if_neg (by omega), if_neg (by omega), show (2 * n + 2 - 2) / 2 = n by omega]

section Ex2
variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}

local notation "SS" => example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄

/-- Buffers of the runs of a machine alternating between `cX` (even runs) and `cY` (odd runs). -/
def pb (cX cY : (SS).Buffer) (k : ℕ) : (SS).Buffer := if k % 2 = 0 then cX else cY

theorem ex_mcases2 (P : Fin (SS).M → Prop) (h1 : P m₁) (h2 : P m₂) : ∀ m, P m := by
  intro m
  fin_cases m
  exacts [h1, h2]

theorem pb_even (cX cY : (SS).Buffer) (n : ℕ) : pb cX cY (2 * n) = cX := by
  simp [pb]
theorem pb_odd (cX cY : (SS).Buffer) (n : ℕ) : pb cX cY (2 * n + 1) = cY := by
  simp [pb, show (2 * n + 1) % 2 = 1 by omega]

/-- Generic characterization of processing for an alternating machine. -/
theorem proc_alt {T : (SS).Schedule} {m : Fin (SS).M} {cX cY : (SS).Buffer} (hXY : cX ≠ cY)
    {η D dX dY : ℝ} (hn : T.nruns m = ⊤) (hβ : T.β m = pb cX cY) (hs : T.s m = ps η D)
    (hdY : (SS).δ cX cY = dY) (hdX : (SS).δ cY cX = dX) (σ : ℝ) :
    (T.ProcessingBuffer m cY σ ↔ σ ∈ PSet η dY D) ∧
      (T.ProcessingBuffer m cX σ ↔ σ ∈ PSet η (D + dX) η) := by
  have hr : ∀ k, T.RunExists m k := fun k => by
    unfold RunExists; rw [hn]; exact WithTop.coe_lt_top _
  have hp0 : T.procStart m 0 = 0 := by show T.s m 0 = 0; rw [hs, ps_zero]
  have hpo : ∀ n : ℕ, T.procStart m (2 * n + 1) = (n : ℝ) * η + dY := by
    intro n
    show T.s m (2 * n + 1) + (SS).δ (T.β m (2 * n)) (T.β m (2 * n + 1)) = _
    rw [hs, hβ, ps_odd, pb_even, pb_odd, hdY]
  have hpe : ∀ n : ℕ, T.procStart m (2 * n + 2) = (n : ℝ) * η + D + dX := by
    intro n
    show T.s m (2 * n + 1 + 1) + (SS).δ (T.β m (2 * n + 1)) (T.β m (2 * n + 1 + 1)) = _
    rw [hs, hβ, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pb_odd, pb_even,
      show 2 * (n + 1) = 2 * n + 2 by ring, ps_even, hdX]
  have hinp : ∀ k σ, T.InProcessing m k σ ↔ T.procStart m k ≤ σ ∧ σ < T.s m (k + 1) :=
    fun k σ => ⟨fun h => ⟨h.2.1, h.2.2 (hr _)⟩, fun h => ⟨hr k, h.1, fun _ => h.2⟩⟩
  constructor
  · constructor
    · rintro ⟨k, hk, hkp⟩
      rw [hinp] at hkp
      obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
      · rw [hβ, pb_even] at hk; exact absurd hk hXY
      · refine ⟨n, ?_, ?_⟩
        · rw [hpo] at hkp; exact hkp.1
        · have := hkp.2; rw [hs, show 2 * n + 1 + 1 = 2 * n + 2 by ring, ps_even] at this
          exact this
    · rintro ⟨n, h1, h2⟩
      refine ⟨2 * n + 1, by rw [hβ, pb_odd], (hinp _ _).2 ⟨by rw [hpo]; exact h1, ?_⟩⟩
      rw [hs, show 2 * n + 1 + 1 = 2 * n + 2 by ring, ps_even]; exact h2
  · constructor
    · rintro ⟨k, hk, hkp⟩
      rw [hinp] at hkp
      obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
      · rcases n with _ | n
        · have := hkp.2
          rw [hp0] at hkp
          rw [hs, show 2 * 0 + 1 = 2 * 0 + 1 from rfl, ps_odd] at this
          simp at this; linarith [hkp.1]
        · refine ⟨n, ?_, ?_⟩
          · have := hkp.1; rw [show 2 * (n + 1) = 2 * n + 2 by ring, hpe] at this; linarith
          · have := hkp.2
            rw [hs, show 2 * (n + 1) + 1 = 2 * (n + 1) + 1 from rfl, ps_odd] at this
            push_cast at this; linarith
      · rw [hβ, pb_odd] at hk; exact absurd hk.symm hXY
    · rintro ⟨n, h1, h2⟩
      refine ⟨2 * n + 2, by rw [hβ, show 2 * n + 2 = 2 * (n + 1) by ring, pb_even],
        (hinp _ _).2 ⟨by rw [hpe]; linarith, ?_⟩⟩
      rw [hs, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, ps_odd]; push_cast; linarith

theorem alt_ps {T : (SS).Schedule} {m : Fin (SS).M} {cX cY : (SS).Buffer}
    {η D dX dY : ℝ} (hβ : T.β m = pb cX cY) (hs : T.s m = ps η D)
    (hdY : (SS).δ cX cY = dY) (hdX : (SS).δ cY cX = dX) :
    T.procStart m 0 = 0 ∧ (∀ n : ℕ, T.procStart m (2 * n + 1) = (n : ℝ) * η + dY) ∧
      (∀ n : ℕ, T.procStart m (2 * n + 2) = (n : ℝ) * η + D + dX) := by
  refine ⟨by show T.s m 0 = 0; rw [hs, ps_zero], fun n => ?_, fun n => ?_⟩
  · show T.s m (2 * n + 1) + (SS).δ (T.β m (2 * n)) (T.β m (2 * n + 1)) = _
    rw [hs, hβ, ps_odd, pb_even, pb_odd, hdY]
  · show T.s m (2 * n + 1 + 1) + (SS).δ (T.β m (2 * n + 1)) (T.β m (2 * n + 1 + 1)) = _
    rw [hs, hβ, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pb_odd, pb_even,
      show 2 * (n + 1) = 2 * n + 2 by ring, ps_even, hdX]

/-- The clearing rule for an alternating machine, from the values of its buffer levels. -/
theorem clear_alt {T : (SS).Schedule} {m : Fin (SS).M} {cX cY : (SS).Buffer} (hXY : cX ≠ cY)
    {η D dX dY : ℝ} (hη : 0 < η) (hn : T.nruns m = ⊤) (hβ : T.β m = pb cX cY)
    (hs : T.s m = ps η D) (hdY : (SS).δ cX cY = dY) (hdX : (SS).δ cY cX = dX)
    (posY : ∀ n : ℕ, ∀ t, (n : ℝ) * η + dY < t → t < (n : ℝ) * η + D → 0 < T.x cY t)
    (zeroY : ∀ n : ℕ, T.x cY ((n : ℝ) * η + D) = 0)
    (posX : ∀ n : ℕ, ∀ t, (n : ℝ) * η + D + dX < t → t < (n : ℝ) * η + η → 0 < T.x cX t)
    (zeroX : ∀ n : ℕ, T.x cX ((n : ℝ) * η + η) = 0) (x0 : T.x cX 0 = 0)
    (demY : ∀ n : ℕ, T.Demanding cY ((n : ℝ) * η))
    (demX : ∀ n : ℕ, T.Demanding cX ((n : ℝ) * η + D)) :
    ∀ k, T.RunExists m k →
    (∀ t, T.procStart m k < t → (T.RunExists m (k + 1) → t < T.s m (k + 1)) →
      ¬ (T.x (T.β m k) t = 0 ∧
          ∃ b', (SS).mach b' = m ∧ b' ≠ T.β m k ∧ T.Demanding b' t)) ∧
    (T.RunExists m (k + 1) →
      T.x (T.β m k) (T.s m (k + 1)) = 0 ∧ T.β m (k + 1) ≠ T.β m k ∧
        T.Demanding (T.β m (k + 1)) (T.s m (k + 1))) := by
  have hr : ∀ k, T.RunExists m k := fun k => by
    unfold RunExists; rw [hn]; exact WithTop.coe_lt_top _
  obtain ⟨hp0, hpo, hpe⟩ := alt_ps hβ hs hdY hdX
  intro k _
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · rcases n with _ | n
    · refine ⟨fun t ht hlt => ?_, fun _ => ?_⟩
      · have := hlt (hr _)
        rw [hp0] at ht
        rw [hs, show 2 * 0 + 1 = 2 * 0 + 1 from rfl, ps_odd] at this
        simp at this; linarith
      · rw [hs, hβ, show 2 * 0 + 1 = 2 * 0 + 1 from rfl, ps_odd, pb_even, pb_odd]
        simp only [Nat.cast_zero, zero_mul]
        refine ⟨x0, Ne.symm hXY, ?_⟩
        have := demY 0; simpa using this
    · rw [show 2 * (n + 1) = 2 * n + 2 by ring]
      refine ⟨fun t ht hlt => ?_, fun _ => ?_⟩
      · rw [hpe] at ht
        have := hlt (hr _)
        rw [hs, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, ps_odd] at this
        rw [hβ, show 2 * n + 2 = 2 * (n + 1) by ring, pb_even]
        have hp := posX n t (by linarith) (by push_cast at this; linarith)
        exact fun h => absurd h.1 hp.ne'
      · rw [hs, hβ, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, ps_odd, pb_odd,
          show 2 * n + 2 = 2 * (n + 1) by ring, pb_even]
        refine ⟨by push_cast; rw [add_mul, one_mul]; exact zeroX n, Ne.symm hXY, demY (n + 1)⟩
  · refine ⟨fun t ht hlt => ?_, fun _ => ?_⟩
    · rw [hpo] at ht
      have := hlt (hr _)
      rw [hs, show 2 * n + 1 + 1 = 2 * n + 2 by ring, ps_even] at this
      rw [hβ, pb_odd]
      have hp := posY n t ht this
      exact fun h => absurd h.1 hp.ne'
    · rw [hs, hβ, show 2 * n + 1 + 1 = 2 * n + 2 by ring, ps_even, pb_odd,
        show 2 * n + 2 = 2 * (n + 1) by ring, pb_even]
      exact ⟨zeroY n, hXY, demX n⟩

theorem setup_alt {T : (SS).Schedule} {m : Fin (SS).M} {cX cY : (SS).Buffer}
    {η D dX dY : ℝ} (hβ : T.β m = pb cX cY) (hs : T.s m = ps η D)
    (hdY : (SS).δ cX cY = dY) (hdX : (SS).δ cY cX = dX) (h1 : dY ≤ D) (h2 : D + dX ≤ η) :
    ∀ k, T.procStart m k ≤ T.s m (k + 1) := by
  obtain ⟨hp0, hpo, hpe⟩ := alt_ps hβ hs hdY hdX
  intro k
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · rcases n with _ | n
    · rw [hp0, hs, show 2 * 0 + 1 = 2 * 0 + 1 from rfl, ps_odd]; simp
    · rw [show 2 * (n + 1) = 2 * n + 2 by ring, hpe, hs,
        show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, ps_odd]
      push_cast; linarith
  · rw [hpo, hs, show 2 * n + 1 + 1 = 2 * n + 2 by ring, ps_even]; linarith

theorem tendsto_ps {η D : ℝ} (hη : 0 < η) (hD : 0 ≤ D) : Tendsto (ps η D) atTop atTop := by
  have hlow : ∀ k : ℕ, (k : ℝ) * (η / 2) + (-η) ≤ ps η D k := by
    intro k
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
    · rcases n with _ | n
      · rw [ps_zero]; simp; linarith
      · rw [show 2 * (n + 1) = 2 * n + 2 by ring, ps_even]; push_cast; nlinarith
    · rw [ps_odd]; push_cast; nlinarith
  refine tendsto_atTop_mono hlow ?_
  exact tendsto_atTop_add_const_right _ _
    (tendsto_natCast_atTop_atTop.atTop_mul_const (half_pos hη))

end Ex2
end KS2
end KumarSeidman.TwoType


namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory Filter

namespace KS2

section Ex2
variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}

local notation "SS" => example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄

/-- Run data of the periodic regime (levels are dummies). -/
noncomputable def runsS (η A B : ℝ) : (SS).Schedule where
  x _ _ := 0
  y _ _ := 0
  nruns _ := ⊤
  β m := ![pb b₁ b₄, pb b₃ b₂] m
  s m := ![ps η A, ps η B] m

/-- The set of times at which buffer `b` is processed in the periodic regime. -/
def PSb (η A B : ℝ) (b : (SS).Buffer) : Set ℝ :=
  {σ | (runsS η A B).ProcessingBuffer ((SS).mach b) b σ}

/-- The periodic clearing trajectory: outputs are `1/τ_b` times the time spent processing. -/
noncomputable def perS (η A B : ℝ) : (SS).Schedule where
  x b t := levels 0 η 0 η b + (SS).inflow (fun b t => V (PSb η A B b) t / (SS).procTime b) b t -
    V (PSb η A B b) t / (SS).procTime b
  y b t := V (PSb η A B b) t / (SS).procTime b
  nruns _ := ⊤
  β := (runsS η A B).β
  s := (runsS η A B).s

theorem runsS_β1 (η A B : ℝ) : (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁)
    (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B).β m₁ = pb b₁ b₄ := rfl
theorem runsS_β2 (η A B : ℝ) : (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁)
    (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B).β m₂ = pb b₃ b₂ := rfl
theorem runsS_s1 (η A B : ℝ) : (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁)
    (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B).s m₁ = ps η A := rfl
theorem runsS_s2 (η A B : ℝ) : (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁)
    (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B).s m₂ = ps η B := rfl
theorem runsS_n (η A B : ℝ) (m : Fin (SS).M) : (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄)
    (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B).nruns m = ⊤ := rfl

theorem perS_proc (η A B : ℝ) (m : Fin (SS).M) (b : (SS).Buffer) (σ : ℝ) :
    (perS η A B).ProcessingBuffer m b σ ↔ (runsS η A B).ProcessingBuffer m b σ := Iff.rfl

theorem yper {η c d τ : ℝ} (hη : 0 < η) (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ η) (hτ : 0 < τ)
    (hL : d - c = τ * η) (n : ℕ) {t : ℝ} (h1 : (n : ℝ) * η ≤ t) (h2 : t ≤ (n : ℝ) * η + η) :
    V (PSet η c d) t / τ = (n : ℝ) * η + max 0 (min (t - (n : ℝ) * η - c) (d - c)) / τ := by
  have := V_per_step hη hc hcd hd n h1 h2
  rw [V_per_n hη hc hcd hd n, hL] at this
  rw [show V (PSet η c d) t = (n : ℝ) * (τ * η) + max 0 (min (t - (n : ℝ) * η - c) (τ * η))
    by linarith, hL]
  field_simp

end Ex2
theorem cl_nonneg (z L : ℝ) : 0 ≤ max 0 (min z L) := le_max_left _ _
theorem cl_le {z L : ℝ} (hL : 0 ≤ L) : max 0 (min z L) ≤ L := max_le hL (min_le_right _ _)
theorem cl_neg {z L : ℝ} (hz : z ≤ 0) : max 0 (min z L) = 0 :=
  max_eq_left (le_trans (min_le_left _ _) hz)
theorem cl_mid {z L : ℝ} (h0 : 0 ≤ z) (hL : z ≤ L) : max 0 (min z L) = z := by
  rw [min_eq_left hL, max_eq_right h0]
theorem cl_top {z L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ z) : max 0 (min z L) = L := by
  rw [min_eq_right hL, max_eq_right hL0]

/-- First-stage buffer: `u - clamp(u - P, τη)/τ`, with `P = η(1 - τ)`. -/
theorem fs_nonneg {u η τ P : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hP : P = η * (1 - τ)) (hu0 : 0 ≤ u)
    (hu : u ≤ η) : max 0 (min (u - P) (η - P)) / τ ≤ u := by
  rcases le_total u P with h | h
  · rw [cl_neg (by linarith), zero_div]; exact hu0
  · rw [cl_mid (by linarith) (by linarith), div_le_iff₀ hτ]; nlinarith
theorem fs_pos {u η τ P : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hP : P = η * (1 - τ)) (hu0 : P < u)
    (hu : u < η) : max 0 (min (u - P) (η - P)) / τ < u := by
  rw [cl_mid (by linarith) (by linarith), div_lt_iff₀ hτ]; nlinarith
theorem fs_top {η τ P : ℝ} (hτ : 0 < τ) (hP : P = η * (1 - τ)) (hη : 0 < η) :
    max 0 (min (η - P) (η - P)) / τ = η := by
  rw [min_self, max_eq_right (by nlinarith), hP]; field_simp; ring

section Ex2
variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}

set_option maxHeartbeats 4000000 in
theorem periodic_exists (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h8 : (δ₁ + δ₄) / (1 - τ₁ - τ₄) = (δ₂ + δ₃) / (1 - τ₂ - τ₃))
    (h9 : δ₄ < (1 - τ₃ - τ₄) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h10 : δ₂ < (1 - τ₁ - τ₂) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    let η := (δ₁ + δ₄) / (1 - τ₁ - τ₄)
    ∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃) := by
  intro η
  have hD1 : 0 < 1 - τ₁ - τ₄ := by linarith
  have hD2 : 0 < 1 - τ₂ - τ₃ := by linarith
  have hηdef : η = (δ₁ + δ₄) / (1 - τ₁ - τ₄) := rfl
  have hη : 0 < η := by positivity
  have hηa : η * (1 - τ₁ - τ₄) = δ₁ + δ₄ := by rw [hηdef]; field_simp
  have hηb : η * (1 - τ₂ - τ₃) = δ₂ + δ₃ := by rw [hηdef, h8]; field_simp
  rw [← hηdef] at h9 h10
  clear_value η
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = δ₄ + τ₄ * η := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = δ₂ + τ₂ * η := ⟨_, rfl⟩
  have hP1 : A + δ₁ = η * (1 - τ₁) := by rw [hA]; linear_combination -hηa
  have hP3 : B + δ₃ = η * (1 - τ₃) := by rw [hB]; linear_combination -hηb
  have hAP3 : A < B + δ₃ := by rw [hA, hB]; nlinarith
  have hBP1 : B < A + δ₁ := by rw [hA, hB]; nlinarith
  have hτ1 : τ₁ < 1 := by linarith
  have hτ3 : τ₃ < 1 := by linarith
  have hδA : δ₄ < A := by rw [hA]; have := mul_pos hτ₄ hη; linarith
  have hδB : δ₂ < B := by rw [hB]; have := mul_pos hτ₂ hη; linarith
  have hP1η : A + δ₁ < η := by rw [hP1]; nlinarith
  have hP3η : B + δ₃ < η := by rw [hP3]; nlinarith
  set T := perS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃)
    (δ₄ := δ₄) η A B with hTdef
  -- processing sets
  have hPS1 : (PSb (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) b₁ = PSet η (A + δ₁) η := Set.ext fun σ =>
    (proc_alt (T := (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) (m := m₁) ex_b14 ((runsS_n (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) m₁) ((runsS_β1 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ((runsS_s1 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ex_δ14 ex_δ41 σ).2
  have hPS4 : (PSb (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) b₄ = PSet η δ₄ A := Set.ext fun σ =>
    (proc_alt (T := (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) (m := m₁) ex_b14 ((runsS_n (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) m₁) ((runsS_β1 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ((runsS_s1 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ex_δ14 ex_δ41 σ).1
  have hPS3 : (PSb (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) b₃ = PSet η (B + δ₃) η := Set.ext fun σ =>
    (proc_alt (T := (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) (m := m₂) ex_b32 ((runsS_n (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) m₂) ((runsS_β2 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ((runsS_s2 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ex_δ32 ex_δ23 σ).2
  have hPS2 : (PSb (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) b₂ = PSet η δ₂ B := Set.ext fun σ =>
    (proc_alt (T := (runsS (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) (m := m₂) ex_b32 ((runsS_n (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) m₂) ((runsS_β2 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ((runsS_s2 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ex_δ32 ex_δ23 σ).1
  -- outputs in period n
  have hy1 : ∀ n : ℕ, ∀ t, (n : ℝ) * η ≤ t → t ≤ (n : ℝ) * η + η →
      T.y b₁ t = (n : ℝ) * η + max 0 (min (t - (n : ℝ) * η - (A + δ₁)) (η - (A + δ₁))) / τ₁ := by
    intro n t h1 h2
    show V _ t / τ₁ = _
    rw [hPS1]
    exact yper hη (by linarith) hP1η le_rfl hτ₁ (by linarith) n h1 h2
  have hy3 : ∀ n : ℕ, ∀ t, (n : ℝ) * η ≤ t → t ≤ (n : ℝ) * η + η →
      T.y b₃ t = (n : ℝ) * η + max 0 (min (t - (n : ℝ) * η - (B + δ₃)) (η - (B + δ₃))) / τ₃ := by
    intro n t h1 h2
    show V _ t / τ₃ = _
    rw [hPS3]
    exact yper hη (by linarith) hP3η le_rfl hτ₃ (by linarith) n h1 h2
  have hy4 : ∀ n : ℕ, ∀ t, (n : ℝ) * η ≤ t → t ≤ (n : ℝ) * η + η →
      T.y b₄ t = (n : ℝ) * η + max 0 (min (t - (n : ℝ) * η - δ₄) (τ₄ * η)) / τ₄ := by
    intro n t h1 h2
    show V _ t / τ₄ = _
    rw [hPS4, show τ₄ * η = A - δ₄ by rw [hA]; ring]
    exact yper hη hδ₄.le hδA (by linarith) hτ₄ (by rw [hA]; ring) n h1 h2
  have hy2 : ∀ n : ℕ, ∀ t, (n : ℝ) * η ≤ t → t ≤ (n : ℝ) * η + η →
      T.y b₂ t = (n : ℝ) * η + max 0 (min (t - (n : ℝ) * η - δ₂) (τ₂ * η)) / τ₂ := by
    intro n t h1 h2
    show V _ t / τ₂ = _
    rw [hPS2, show τ₂ * η = B - δ₂ by rw [hB]; ring]
    exact yper hη hδ₂.le hδB (by linarith) hτ₂ (by rw [hB]; ring) n h1 h2
  -- levels
  have hpt : ∀ b, 0 < (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).procTime b :=
    ex_cases _ hτ₁ hτ₂ hτ₃ hτ₄
  have hy0 : ∀ b, T.y b 0 = 0 := fun b => by show V _ 0 / _ = 0; rw [V_zero0, zero_div]
  have hin0 : ∀ b, (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).inflow T.y b 0 = 0 := by
    refine ex_cases _ ?_ ?_ ?_ ?_
    · rw [ex_in₁]
    · rw [ex_in₂, hy0]
    · rw [ex_in₃]
    · rw [ex_in₄, hy0]
  have hxdef : ∀ b t, T.x b t = levels 0 η 0 η b +
      (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).inflow T.y b t - T.y b t := fun b t => rfl
  have hx1 : ∀ t, T.x b₁ t = t - T.y b₁ t := fun t => by
    rw [hxdef, ex_in₁]; show (0 : ℝ) + t - _ = _; ring
  have hx2 : ∀ t, T.x b₂ t = η + T.y b₁ t - T.y b₂ t := fun t => by
    rw [hxdef, ex_in₂]; rfl
  have hx3 : ∀ t, T.x b₃ t = t - T.y b₃ t := fun t => by
    rw [hxdef, ex_in₃]; show (0 : ℝ) + t - _ = _; ring
  have hx4 : ∀ t, T.x b₄ t = η + T.y b₃ t - T.y b₄ t := fun t => by
    rw [hxdef, ex_in₄]; rfl
  have hperiod : ∀ t, 0 ≤ t → ∃ n : ℕ, (n : ℝ) * η ≤ t ∧ t ≤ (n : ℝ) * η + η := by
    intro t ht
    refine ⟨⌊t / η⌋₊, ?_, ?_⟩
    · have := Nat.floor_le (div_nonneg ht hη.le)
      calc (⌊t / η⌋₊ : ℝ) * η ≤ t / η * η := mul_le_mul_of_nonneg_right this hη.le
        _ = t := by field_simp
    · have := Nat.lt_floor_add_one (t / η)
      have : t / η * η < ((⌊t / η⌋₊ : ℝ) + 1) * η := mul_lt_mul_of_pos_right this hη
      rw [div_mul_cancel₀ _ hη.ne'] at this
      linarith
  have hτ4η : 0 ≤ τ₄ * η := by positivity
  have hτ2η : 0 ≤ τ₂ * η := by positivity
  have hcl4 : ∀ z, max 0 (min z (τ₄ * η)) / τ₄ ≤ η := fun z => by
    rw [div_le_iff₀ hτ₄]; nlinarith [cl_le (z := z) hτ4η]
  have hcl2 : ∀ z, max 0 (min z (τ₂ * η)) / τ₂ ≤ η := fun z => by
    rw [div_le_iff₀ hτ₂]; nlinarith [cl_le (z := z) hτ2η]
  have hcl4' : ∀ z, z < τ₄ * η → max 0 (min z (τ₄ * η)) / τ₄ < η := fun z hz => by
    rw [div_lt_iff₀ hτ₄, min_eq_left hz.le]
    rcases le_total z 0 with h | h
    · rw [max_eq_left h]; positivity
    · rw [max_eq_right h]; linarith
  have hcl2' : ∀ z, z < τ₂ * η → max 0 (min z (τ₂ * η)) / τ₂ < η := fun z hz => by
    rw [div_lt_iff₀ hτ₂, min_eq_left hz.le]
    rcases le_total z 0 with h | h
    · rw [max_eq_left h]; positivity
    · rw [max_eq_right h]; linarith
  have hnn3 : ∀ z, 0 ≤ max 0 (min z (η - (B + δ₃))) / τ₃ := fun z => div_nonneg (cl_nonneg _ _) hτ₃.le
  have hnn1 : ∀ z, 0 ≤ max 0 (min z (η - (A + δ₁))) / τ₁ := fun z => div_nonneg (cl_nonneg _ _) hτ₁.le
  have hcl4top : max 0 (min (A - δ₄) (τ₄ * η)) / τ₄ = η := by
    rw [cl_top hτ4η (by rw [hA]; linarith)]; field_simp
  have hcl2top : max 0 (min (B - δ₂) (τ₂ * η)) / τ₂ = η := by
    rw [cl_top hτ2η (by rw [hB]; linarith)]; field_simp
  refine ⟨T, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  -- 1. y b 0 = 0
  · exact hy0
  -- 2. monotone
  · intro b u _ v _ huv
    exact div_le_div_of_nonneg_right (V_mono _ huv) (hpt b).le
  -- 3. balance
  · intro b t _
    rw [hxdef b t, hxdef b 0, hin0, hy0]; ring
  -- 4. nonneg
  · intro b t ht
    obtain ⟨n, h1, h2⟩ := hperiod t ht
    revert b
    refine ex_cases _ ?_ ?_ ?_ ?_
    · rw [hx1, hy1 n t h1 h2]
      have := fs_nonneg (u := t - n * η) hτ₁ hτ1 hP1 (by linarith) (by linarith)
      linarith
    · rw [hx2, hy1 n t h1 h2, hy2 n t h1 h2]
      linarith [hcl2 (t - n * η - δ₂), hnn1 (t - n * η - (A + δ₁))]
    · rw [hx3, hy3 n t h1 h2]
      have := fs_nonneg (u := t - n * η) hτ₃ hτ3 hP3 (by linarith) (by linarith)
      linarith
    · rw [hx4, hy3 n t h1 h2, hy4 n t h1 h2]
      linarith [hcl4 (t - n * η - δ₄), hnn3 (t - n * η - (B + δ₃))]
  -- 5. run 0
  · exact ex_mcases2 _ ⟨WithTop.coe_lt_top _, ps_zero η A⟩ ⟨WithTop.coe_lt_top _, ps_zero η B⟩
  -- 6. machines
  · refine ex_mcases2 _ (fun k _ => ?_) (fun k _ => ?_)
    · show (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).mach (pb b₁ b₄ k) = m₁
      unfold pb; split_ifs <;> rfl
    · show (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).mach (pb b₃ b₂ k) = m₂
      unfold pb; split_ifs <;> rfl
  -- 7. set-ups are not cut
  · refine ex_mcases2 _ (fun k _ => ?_) (fun k _ => ?_)
    · exact setup_alt (T := T) (m := m₁) ((runsS_β1 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ((runsS_s1 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ex_δ14 ex_δ41 hδA.le hP1η.le k
    · exact setup_alt (T := T) (m := m₂) ((runsS_β2 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ((runsS_s2 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ex_δ32 ex_δ23 hδB.le hP3η.le k
  -- 8. run starts tend to infinity
  · refine ex_mcases2 _ (fun _ => ?_) (fun _ => ?_)
    · exact tendsto_ps hη (by linarith)
    · exact tendsto_ps hη (by linarith)
  -- 9. rate cap
  · intro b u v hu huv
    have e : {σ | σ ∈ Set.Icc u v ∧ T.ProcessingBuffer
        ((example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).mach b) b σ} = (PSb (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) b ∩ Set.Icc u v := by
      ext σ; exact and_comm
    rw [e]
    show V _ v / _ - V _ u / _ ≤ _
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (V_cap _ hu huv) (hpt b).le
  -- 10. full rate
  · intro b u v hu huv hall
    show V _ v / _ - V _ u / _ = _
    rw [← sub_div, V_full ((PSb (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) b) hu huv (fun σ hσ => (hall σ ⟨hσ.1.le, hσ.2⟩).1)]
  -- start
  · intro b; rw [hxdef, hin0, hy0]; ring
  · refine ex_mcases2 _ ?_ ?_
    · show pb b₁ b₄ 0 = b₁; simp [pb]
    · show pb b₃ b₂ 0 = b₃; simp [pb]
  -- clearing
  · refine ex_mcases2 _ ?_ ?_
    · refine clear_alt (T := T) (m := m₁) ex_b14 hη ((runsS_n (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) m₁) ((runsS_β1 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ((runsS_s1 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ex_δ14 ex_δ41 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro n t h1 h2
        rw [hx4, hy3 n t (by linarith) (by linarith), hy4 n t (by linarith) (by linarith)]
        have := hcl4' (t - n * η - δ₄) (by rw [hA] at h2; linarith)
        linarith [hnn3 (t - n * η - (B + δ₃))]
      · intro n
        have h1 : (n : ℝ) * η ≤ n * η + A := by linarith
        have h2 : (n : ℝ) * η + A ≤ n * η + η := by linarith
        rw [hx4, hy3 n _ h1 h2, hy4 n _ h1 h2, cl_neg (by linarith),
          show (n : ℝ) * η + A - n * η - δ₄ = A - δ₄ by ring, hcl4top]
        ring
      · intro n t h1 h2
        rw [hx1, hy1 n t (by linarith) h2.le]
        have := fs_pos (u := t - n * η) hτ₁ hτ1 hP1 (by linarith) (by linarith)
        linarith
      · intro n
        rw [hx1, hy1 n _ (by linarith) le_rfl, show (n : ℝ) * η + η - n * η - (A + δ₁) =
          η - (A + δ₁) by ring, fs_top hτ₁ hP1 hη]
        ring
      · rw [hx1, hy0]; ring
      · intro n
        refine Or.inl ?_
        rw [hx4, hy3 n _ le_rfl (by linarith), hy4 n _ le_rfl (by linarith), sub_self,
          cl_neg (by linarith), cl_neg (by linarith)]
        simp; exact hη
      · intro n
        exact Or.inr (fun σ hσ => by rw [ex_in₁, ex_in₁]; exact hσ)
    · refine clear_alt (T := T) (m := m₂) ex_b32 hη ((runsS_n (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B) m₂) ((runsS_β2 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ((runsS_s2 (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂) (δ₃ := δ₃) (δ₄ := δ₄) η A B)) ex_δ32 ex_δ23 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro n t h1 h2
        rw [hx2, hy1 n t (by linarith) (by linarith), hy2 n t (by linarith) (by linarith)]
        have := hcl2' (t - n * η - δ₂) (by rw [hB] at h2; linarith)
        linarith [hnn1 (t - n * η - (A + δ₁))]
      · intro n
        have h1 : (n : ℝ) * η ≤ n * η + B := by linarith
        have h2 : (n : ℝ) * η + B ≤ n * η + η := by linarith
        rw [hx2, hy1 n _ h1 h2, hy2 n _ h1 h2, cl_neg (by linarith),
          show (n : ℝ) * η + B - n * η - δ₂ = B - δ₂ by ring, hcl2top]
        ring
      · intro n t h1 h2
        rw [hx3, hy3 n t (by linarith) h2.le]
        have := fs_pos (u := t - n * η) hτ₃ hτ3 hP3 (by linarith) (by linarith)
        linarith
      · intro n
        rw [hx3, hy3 n _ (by linarith) le_rfl, show (n : ℝ) * η + η - n * η - (B + δ₃) =
          η - (B + δ₃) by ring, fs_top hτ₃ hP3 hη]
        ring
      · rw [hx3, hy0]; ring
      · intro n
        refine Or.inl ?_
        rw [hx2, hy1 n _ le_rfl (by linarith), hy2 n _ le_rfl (by linarith), sub_self,
          cl_neg (by linarith), cl_neg (by linarith)]
        simp; exact hη
      · intro n
        exact Or.inr (fun σ hσ => by rw [ex_in₃, ex_in₃]; exact hσ)

end Ex2
end KS2
end KumarSeidman.TwoType


open KumarSeidman.TwoType KumarSeidman.TwoType.Example2 KumarSeidman.TwoType.KS2 in
theorem solution (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h8 : (δ₁ + δ₄) / (1 - τ₁ - τ₄) = (δ₂ + δ₃) / (1 - τ₂ - τ₃))
    (h9 : δ₄ < (1 - τ₃ - τ₄) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h10 : δ₂ < (1 - τ₁ - τ₂) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    let η := (δ₁ + δ₄) / (1 - τ₁ - τ₄)
    ∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃) :=
  periodic_exists τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄ hδ₁ hδ₂ hδ₃ hδ₄ h8 h9 h10 h1₁ h1₂
