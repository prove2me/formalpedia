-- Prove2me | solution 1 for KumarSeidman.TwoType.case2_stage8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:47:59.967897+00:00
-- url     : https://prove2.me/submissions/b7f26ecf-6d1f-49e1-a7d0-c1e2cd353837

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
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory

namespace KS2

section Ex2
variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}
end Ex2

set_option maxHeartbeats 2000000 in
theorem stage8_arith (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ ξ K t3 t4 t5 t6 t7 t8 t9 L : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1)
    (hK : K = δ₄ + τ₄ * δ₁ + δ₁) (hξ : δ₁ + K + 1 ≤ (τ₂ - τ₁) * ξ)
    (ht9 : t9 = (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1))
    (ht3 : t3 = δ₁ + δ₂) (ht4 : t4 = (ξ * τ₁ + δ₁) / (1 - τ₁)) (ht5 : t5 = t4 + δ₄)
    (ht6 : t6 = t5 + τ₄ * δ₁) (ht7 : t7 = t6 + δ₁) (ht8 : t8 = t7 + K * τ₁ / (1 - τ₁))
    (hL : L = t3 + τ₂ * (ξ + t4)) :
    τ₁ < τ₂ ∧ τ₂ < 1 ∧ τ₁ < 1 ∧ τ₄ < 1 ∧ τ₃ < 1 ∧ 0 < ξ ∧ 0 < K ∧
    (t4 - δ₁) * (1 / τ₁ - 1) = ξ + δ₁ ∧ (t4 - δ₁) / τ₁ = ξ + t4 ∧ δ₁ < t4 ∧ t7 - t4 = K ∧
    (t8 - t7) * (1 / τ₁ - 1) = t7 - t4 ∧ (t6 - t5) * (1 / τ₄ - 0) = δ₁ ∧
    t7 < t8 ∧ t8 < L ∧ L < t9 ∧ t3 < L ∧ δ₁ < t3 ∧ t4 < t5 ∧ t5 < t6 ∧ t6 < t7 ∧
    (∀ s, s < t9 → 0 < ξ + s - (s - t3) / τ₂) ∧
    (∀ t, δ₁ < t → max (t - t3) 0 / τ₂ < (t - δ₁) / τ₁) ∧
    (∀ t, t < L → max (t - t3) 0 / τ₂ < ξ + t4) ∧
    1 < 1 / τ₁ ∧ 1 < 1 / τ₄ ∧ 1 < 1 / τ₂ ∧ ξ + t9 = (t9 - t3) / τ₂ := by
  have hτ12 : τ₁ < τ₂ := by linarith
  have hτ2 : τ₂ < 1 := by linarith
  have hτ1' : τ₁ < 1 := by linarith
  have hτ4' : τ₄ < 1 := by linarith
  have hτ3' : τ₃ < 1 := by linarith
  have hK0 : 0 < K := by rw [hK]; positivity
  have hξ0 : 0 < ξ := by
    by_contra h; push Not at h
    have : (τ₂ - τ₁) * ξ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    linarith
  have hD : 0 < 1 - τ₁ := by linarith
  have ht4m : t4 * (1 - τ₁) = ξ * τ₁ + δ₁ := by rw [ht4]; field_simp
  have hR4 : (t4 - δ₁) * (1 / τ₁ - 1) = ξ + δ₁ := by
    have e : (t4 - δ₁) * (1 / τ₁ - 1) = (t4 * (1 - τ₁) - δ₁ * (1 - τ₁)) / τ₁ := by
      field_simp
    rw [e, ht4m]; field_simp; ring
  have hξt4 : (ξ + t4) * (1 - τ₁) = ξ + δ₁ := by linear_combination ht4m
  have hinv1 : 0 < 1 / τ₁ - 1 := by
    rw [sub_pos, lt_div_iff₀ hτ₁]; linarith
  have ht4δ : δ₁ < t4 := by
    have : 0 < (t4 - δ₁) * (1 / τ₁ - 1) := by rw [hR4]; linarith
    have := pos_of_mul_pos_left this hinv1.le
    linarith
  have ht7K : t7 - t4 = K := by rw [ht7, ht6, ht5, hK]; ring
  have hR8 : (t8 - t7) * (1 / τ₁ - 1) = t7 - t4 := by
    rw [ht7K, ht8]; field_simp; ring
  have hR6 : (t6 - t5) * (1 / τ₄ - 0) = δ₁ := by rw [ht6]; field_simp; ring
  have ht78 : t7 < t8 := by
    rw [ht8]; have : 0 < K * τ₁ / (1 - τ₁) := by positivity
    linarith
  have ht8m : t8 * (1 - τ₁) = t4 * (1 - τ₁) + K := by
    rw [ht8, show t7 = t4 + K by linarith]; field_simp; ring
  have hLt8 : t8 < L := by
    have e : (L - t8) * (1 - τ₁) = t3 * (1 - τ₁) + τ₂ * (ξ + δ₁) - (ξ * τ₁ + δ₁) - K := by
      rw [hL]; linear_combination τ₂ * hξt4 - ht8m - ht4m
    have : 0 < (L - t8) * (1 - τ₁) := by
      rw [e, ht3]; nlinarith
    nlinarith
  have hτ2inv : τ₂⁻¹ - 1 ≠ 0 := by
    have : 1 < τ₂⁻¹ := (one_lt_inv₀ hτ₂).mpr hτ2
    linarith
  have ht9m : t9 * (1 - τ₂) = ξ * τ₂ + t3 := by
    have h1 : τ₂⁻¹ - 1 = (1 - τ₂) / τ₂ := by field_simp
    have h2 : 1 - τ₂ ≠ 0 := by linarith
    rw [ht9, h1, ← ht3]
    field_simp
  have hR9 : ξ + t9 = (t9 - t3) / τ₂ := by
    rw [eq_div_iff hτ₂.ne']; linear_combination -ht9m
  have hinv2 : 0 < 1 / τ₂ - 1 := by
    rw [sub_pos, lt_div_iff₀ hτ₂]; linarith
  have hgeq : ∀ s, ξ + s - (s - t3) / τ₂ = (t9 - s) * (1 / τ₂ - 1) := by
    intro s
    have e1 : (t9 - t3) / τ₂ - (s - t3) / τ₂ = (t9 - s) / τ₂ := by ring
    have e2 : (t9 - s) * (1 / τ₂ - 1) = (t9 - s) / τ₂ - (t9 - s) := by ring
    rw [e2]; linarith
  have hg : ∀ s, s < t9 → 0 < ξ + s - (s - t3) / τ₂ := by
    intro s hs; rw [hgeq]
    exact mul_pos (by linarith) hinv2
  have hLt9 : L < t9 := by
    by_contra h; push Not at h
    have e0 : (L - t3) / τ₂ = ξ + t4 := by rw [hL]; field_simp; ring
    have e : ξ + L - (L - t3) / τ₂ = L - t4 := by rw [e0]; ring
    have h1 : 0 < L - t4 := by linarith
    have : (t9 - L) * (1 / τ₂ - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hinv2.le
    linarith [hgeq L]
  have ht3L : t3 < L := by
    have : 0 < τ₂ * (ξ + t4) := by
      have : 0 < ξ + t4 := by linarith
      positivity
    linarith
  have ht3δ : δ₁ < t3 := by rw [ht3]; linarith
  have ht45 : t4 < t5 := by rw [ht5]; linarith
  have ht56 : t5 < t6 := by rw [ht6]; have := mul_pos hτ₄ hδ₁; linarith
  have ht67 : t6 < t7 := by rw [ht7]; linarith
  have hR4' : (t4 - δ₁) / τ₁ = ξ + t4 := by
    have e : (t4 - δ₁) / τ₁ = (t4 - δ₁) * (1 / τ₁ - 1) + (t4 - δ₁) := by field_simp; ring
    rw [e, hR4]; ring
  have hi1 : 1 < 1 / τ₁ := by rw [lt_div_iff₀ hτ₁]; linarith
  have hi4 : 1 < 1 / τ₄ := by rw [lt_div_iff₀ hτ₄]; linarith
  have hi2 : 1 < 1 / τ₂ := by rw [lt_div_iff₀ hτ₂]; linarith
  refine ⟨hτ12, hτ2, hτ1', hτ4', hτ3', hξ0, hK0, hR4, hR4', ht4δ, ht7K, hR8, hR6, ht78, hLt8, hLt9,
    ht3L, ht3δ, ht45, ht56, ht67, hg, ?_, ?_, hi1, hi4, hi2, hR9⟩
  · intro t ht
    rcases le_total (t - t3) 0 with h | h
    · rw [max_eq_right h, zero_div]; exact div_pos (by linarith) hτ₁
    · rw [max_eq_left h]
      calc (t - t3) / τ₂ ≤ (t - t3) / τ₁ := div_le_div_of_nonneg_left h hτ₁ hτ12.le
        _ < (t - δ₁) / τ₁ := div_lt_div_of_pos_right (by linarith) hτ₁
  · intro t ht
    have hpos : 0 < ξ + t4 := by linarith
    rcases le_total (t - t3) 0 with h | h
    · rw [max_eq_right h, zero_div]; exact hpos
    · rw [max_eq_left h, div_lt_iff₀ hτ₂]; linarith

set_option maxHeartbeats 4000000 in
theorem stage8_traj (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) (ξ : ℝ)
    (hξ : δ₁ + (δ₄ + τ₄ * δ₁ + δ₁) + 1 ≤ (τ₂ - τ₁) * ξ)
    (T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule)
    (hcl : T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃)) :
    let t₉ := (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1)
    (∀ b, T.x b t₉ = levels 0 0 (t₉ - δ₁) 0 b) ∧ T.SetupFor m₁ t₉ b₁ ∧
      T.SetupFor m₂ t₉ b₂ := by
  intro t9
  have ht9 : t9 = (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1) := rfl
  clear_value t9
  obtain ⟨hT, ⟨hx0, hβ0⟩, hC⟩ := hcl
  have hδ := ex_hδ (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) hδ₁ hδ₂ hδ₃ hδ₄
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = δ₄ + τ₄ * δ₁ + δ₁ := ⟨_, rfl⟩
  obtain ⟨t3, ht3⟩ : ∃ t : ℝ, t = δ₁ + δ₂ := ⟨_, rfl⟩
  obtain ⟨t4, ht4⟩ : ∃ t : ℝ, t = (ξ * τ₁ + δ₁) / (1 - τ₁) := ⟨_, rfl⟩
  obtain ⟨t5, ht5⟩ : ∃ t : ℝ, t = t4 + δ₄ := ⟨_, rfl⟩
  obtain ⟨t6, ht6⟩ : ∃ t : ℝ, t = t5 + τ₄ * δ₁ := ⟨_, rfl⟩
  obtain ⟨t7, ht7⟩ : ∃ t : ℝ, t = t6 + δ₁ := ⟨_, rfl⟩
  obtain ⟨t8, ht8⟩ : ∃ t : ℝ, t = t7 + K * τ₁ / (1 - τ₁) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ t : ℝ, t = t3 + τ₂ * (ξ + t4) := ⟨_, rfl⟩
  obtain ⟨hτ12, hτ2, hτ1', hτ4', hτ3', hξ0, hK0, hR4, hR4', ht4δ, ht7K, hR8, hR6, ht78, hLt8, hLt9,
    ht3L, ht3δ, ht45, ht56, ht67, hg, hlo1, hlo2, hi1, hi4, hi2, hR9⟩ :=
    stage8_arith τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ ξ K t3 t4 t5 t6 t7 t8 t9 L hτ₁ hτ₂ hτ₃ hτ₄ hδ₁ hδ₂ hδ₃ hδ₄
      h7 h1₁ h1₂ hK (by rw [hK]; exact hξ) ht9 ht3 ht4 ht5 ht6 ht7 ht8 hL
  have hx1 : T.x b₁ 0 = ξ := hx0 b₁
  have hx2 : T.x b₂ 0 = 0 := hx0 b₂
  have hx3 : T.x b₃ 0 = 0 := hx0 b₃
  have hx4 : T.x b₄ 0 = 0 := hx0 b₄
  have hβ01 : T.β m₁ 0 = b₄ := hβ0 m₁
  have hβ02 : T.β m₂ 0 = b₃ := hβ0 m₂
  have hy0 := tr_y0 hT
  have hmono : ∀ b u v, 0 ≤ u → u ≤ v → T.y b u ≤ T.y b v := fun b u v hu huv =>
    tr_mono hT b hu huv
  have hnn : ∀ b t, 0 ≤ t → 0 ≤ T.x b t := fun b t ht => tr_nonneg hT b ht
  have hbal1 : ∀ t, 0 ≤ t → T.x b₁ t = ξ + t - T.y b₁ t := by
    intro t ht; rw [tr_bal hT b₁ ht, hx1, ex_in₁]
  have hbal2 : ∀ t, 0 ≤ t → T.x b₂ t = T.y b₁ t - T.y b₂ t := by
    intro t ht; rw [tr_bal hT b₂ ht, hx2, ex_in₂]; ring
  have hbal3 : ∀ t, 0 ≤ t → T.x b₃ t = t - T.y b₃ t := by
    intro t ht; rw [tr_bal hT b₃ ht, hx3, ex_in₃]; ring
  have hbal4 : ∀ t, 0 ≤ t → T.x b₄ t = T.y b₃ t - T.y b₄ t := by
    intro t ht; rw [tr_bal hT b₄ ht, hx4, ex_in₄]; ring
  have hr0₁ := (tr_run0 hT m₁).1
  have hr0₂ := (tr_run0 hT m₂).1
  have hs0₁ : T.s m₁ 0 = 0 := (tr_run0 hT m₁).2
  have hs0₂ : T.s m₂ 0 = 0 := (tr_run0 hT m₂).2
  have hpp0₂ : T.procStart m₂ 0 = 0 := hs0₂
  have hpp0₁ : T.procStart m₁ 0 = 0 := hs0₁
  have hsnn : ∀ m k, T.RunExists m k → 0 ≤ T.s m k := by
    intro m k h
    have := s_mono hT hδ h (Nat.zero_le k)
    rw [(tr_run0 hT m).2] at this; exact this
  -- S1: machine 1 cannot process buffer 1 before δ₁
  have hβ1m1 : T.RunExists m₁ 1 → T.β m₁ 1 = b₁ := fun h => other_buf hT hC ex_only₁ h hβ01
  have hps1 : T.RunExists m₁ 1 → T.procStart m₁ 1 = T.s m₁ 1 + δ₁ := by
    intro h; show T.s m₁ 1 + _ = _; rw [hβ01, hβ1m1 h, ex_δ41]
  have hproc1_early : ∀ σ, T.ProcessingBuffer m₁ b₁ σ → δ₁ ≤ σ := by
    intro σ ⟨k, hk, hkp⟩
    rcases k with _ | k
    · exact absurd (hβ01.symm.trans hk) (Ne.symm ex_b14)
    · have h1 : T.RunExists m₁ 1 := run_mono hkp.1 (by omega)
      have := procStart_mono hT hδ hkp.1 (show 1 ≤ k + 1 by omega)
      rw [hps1 h1] at this
      linarith [hkp.2.1, hsnn m₁ 1 h1]
  have hy1_0 : ∀ t, 0 ≤ t → t ≤ δ₁ → T.y b₁ t = 0 := by
    intro t ht htd
    have := cap hT b₁ (s := 0) (t := t) (a := δ₁) le_rfl ht hτ₁
      (fun σ _ hp => hproc1_early σ hp)
    rw [max_eq_right (by linarith), zero_div, hy0] at this
    linarith [hmono b₁ 0 t le_rfl ht, hy0 b₁]
  -- S2: machine 2 cannot leave buffer 3 before δ₁
  have hβ1m2 : T.RunExists m₂ 1 → T.β m₂ 1 = b₂ := fun h => other_buf' hT hC ex_only₂ h hβ02
  have hs1m2_low : T.RunExists m₂ 1 → δ₁ ≤ T.s m₂ 1 := by
    intro h
    have hex := ((hC m₂ 0 hr0₂).2 h).2.2
    rw [hβ1m2 h] at hex
    by_contra hlt; push Not at hlt
    have hs := hsnn m₂ 1 h
    rcases hex with hx | hin
    · rw [hbal2 _ hs, hy1_0 _ hs hlt.le] at hx
      linarith [hmono b₂ 0 (T.s m₂ 1) le_rfl hs, hy0 b₂]
    · have := hin δ₁ hlt
      rw [ex_in₂, ex_in₂, hy1_0 _ hs hlt.le, hy1_0 δ₁ hδ₁.le le_rfl] at this
      exact lt_irrefl _ this
  -- S3: buffer 3 empty on [0, δ₁]
  have hx3_0 : ∀ t, 0 ≤ t → t ≤ δ₁ → T.x b₃ t = 0 := by
    intro t ht htd
    refine stays_zero' hT b₃ (p := 0) (r := 1) le_rfl ht hτ₃ zero_le_one
      (show (1:ℝ) ≤ 1 / τ₃ by rw [le_div_iff₀ hτ₃]; linarith)
      (fun u v _ _ _ => by rw [ex_in₃, ex_in₃]; linarith)
      (fun σ hσ => show T.ProcessingBuffer m₂ b₃ σ from ⟨0, hβ02, hr0₂, by rw [hpp0₂]; exact hσ.1,
        fun h1 => by linarith [hσ.2, hs1m2_low h1]⟩) hx3
  have hy3_0 : ∀ t, 0 ≤ t → t ≤ δ₁ → T.y b₃ t = t := by
    intro t ht htd; have := hbal3 t ht; rw [hx3_0 t ht htd] at this; linarith
  -- S4: machine 1 switches to buffer 1 at time 0
  obtain ⟨hr1, hs1, hβ1⟩ := first_switch' (m := m₁) (bX := b₄) (bY := b₁) hT hC hδ rfl rfl
    (Ne.symm ex_b14) ex_only₁r hβ01 hx4 hτ₄ hτ4'.le hδ₁
    (fun u v hu huv hv => by
      rw [ex_in₄, ex_in₄, hy3_0 v (by linarith) hv, hy3_0 u hu (by linarith)]; linarith)
    (by rw [hx1]; exact hξ0) (fun u v _ huv => by rw [ex_in₁, ex_in₁]; exact huv) hτ₁
  have hp1 : T.procStart m₁ 1 = δ₁ := by rw [hps1 hr1, hs1]; ring
  -- S5: buffer 1 is cleared at t4, and not before
  have hX1 : T.x b₁ δ₁ = ξ + δ₁ := by
    rw [hbal1 δ₁ hδ₁.le, hy1_0 δ₁ hδ₁.le le_rfl]; ring
  obtain ⟨hlow4, hx1t4, -, hpos1, -⟩ := clear_low (m := m₁) (bA := b₁) (k := 1) (r := 1) hT hC rfl
    hr1 hβ1 hp1 hδ₁.le hτ₁ hX1 (by linarith) hi1 hR4
    (fun u v _ _ _ => by rw [ex_in₁, ex_in₁]; ring)
  have hy1_lin : ∀ t, δ₁ ≤ t → t ≤ t4 → T.y b₁ t = (t - δ₁) / τ₁ := by
    intro t h1 h2
    have := tr_full hT b₁ (s := δ₁) (t := t) hδ₁.le h1 (fun σ hσ =>
      ⟨show T.ProcessingBuffer m₁ b₁ σ from
        ⟨1, hβ1, hr1, by rw [hp1]; exact hσ.1, fun h2' => by linarith [hσ.2, hlow4 h2']⟩,
        hpos1 σ hσ.1 (by linarith [hσ.2])⟩)
    rw [hy1_0 δ₁ hδ₁.le le_rfl, ex_pt₁] at this
    linarith
  have hy1t4 : T.y b₁ t4 = ξ + t4 := by rw [hy1_lin t4 ht4δ.le le_rfl, hR4']
  -- S6: machine 2 switches to buffer 2 exactly at δ₁
  have claim6 : ∀ t, δ₁ < t → t < t4 → (T.RunExists m₂ 1 → t < T.s m₂ 1) → False := by
    intro t h1 h2 hlt
    have hx3t : T.x b₃ t = 0 := by
      refine stays_zero' hT b₃ (p := 0) (r := 1) le_rfl (by linarith) hτ₃ zero_le_one
        (show (1:ℝ) ≤ 1 / τ₃ by rw [le_div_iff₀ hτ₃]; linarith)
        (fun u v _ _ _ => by rw [ex_in₃, ex_in₃]; linarith)
        (fun σ hσ => show T.ProcessingBuffer m₂ b₃ σ from ⟨0, hβ02, hr0₂, by rw [hpp0₂]; exact hσ.1,
          fun h1' => lt_trans hσ.2 (hlt h1')⟩) hx3
    have hdem : T.Demanding b₂ t := by
      refine Or.inr (fun σ hσ => ?_)
      rw [ex_in₂, ex_in₂, hy1_lin t h1.le h2.le]
      rcases le_total σ t4 with h | h
      · rw [hy1_lin σ (by linarith) h]
        exact div_lt_div_of_pos_right (by linarith) hτ₁
      · have := hmono b₁ t4 σ (by linarith) h
        rw [hy1t4] at this
        have : (t - δ₁) / τ₁ < ξ + t4 := by
          rw [← hR4']; exact div_lt_div_of_pos_right (by linarith) hτ₁
        linarith
    have hc := (hC m₂ 0 hr0₂).1 t (by rw [hpp0₂]; linarith) hlt
    apply hc
    rw [hβ02]
    exact ⟨hx3t, b₂, rfl, Ne.symm ex_b32, hdem⟩
  have hr1' : T.RunExists m₂ 1 := by
    by_contra h
    exact claim6 ((δ₁ + t4) / 2) (by linarith) (by linarith) (fun h' => absurd h' h)
  have hs1' : T.s m₂ 1 = δ₁ := by
    refine le_antisymm ?_ (hs1m2_low hr1')
    by_contra hgt; push Not at hgt
    have := lt_min hgt ht4δ
    exact claim6 ((δ₁ + min (T.s m₂ 1) t4) / 2) (by linarith)
      (by linarith [min_le_right (T.s m₂ 1) t4])
      (fun _ => by linarith [min_le_left (T.s m₂ 1) t4])
  have hβ1' : T.β m₂ 1 = b₂ := hβ1m2 hr1'
  have hp1' : T.procStart m₂ 1 = t3 := by
    show T.s m₂ 1 + _ = _; rw [hs1', hβ02, hβ1', ex_δ32, ht3]
  -- S7: lower bound L for the end of machine 2's run on buffer 2
  have hβ2m2 : T.RunExists m₂ 2 → T.β m₂ 2 = b₃ := fun h => other_buf hT hC ex_only₂ h hβ1'
  have hy2cap : ∀ t, 0 ≤ t → T.y b₂ t ≤ max (t - t3) 0 / τ₂ := by
    intro t ht
    have := cap hT b₂ (s := 0) (t := t) (a := t3) le_rfl ht hτ₂ (fun σ _ hp => by
      have := (procY_cases hT hδ (bX := b₃) (bY := b₂) ex_b32 hβ02 hr1' hβ2m2
        (show T.ProcessingBuffer m₂ b₂ σ from hp)).1
      rw [hp1'] at this; exact this)
    rw [hy0, ex_pt₂] at this
    linarith
  have hpos2 : ∀ t, δ₁ < t → t < L → 0 < T.x b₂ t := by
    intro t h1 h2
    have ht0 : 0 ≤ t := by linarith
    rw [hbal2 t ht0]
    have hc := hy2cap t ht0
    rcases le_total t t4 with h | h
    · rw [hy1_lin t h1.le h]; linarith [hlo1 t h1]
    · have := hmono b₁ t4 t (by linarith) h
      rw [hy1t4] at this
      linarith [hlo2 t h2]
  have hlowL : T.RunExists m₂ 2 → L ≤ T.s m₂ 2 := by
    intro h2
    have hex := ((hC m₂ 1 hr1').2 h2).1
    rw [hβ1'] at hex
    have : t3 ≤ T.s m₂ 2 := by rw [← hp1']; exact tr_setup hT h2
    by_contra hlt; push Not at hlt
    have := hpos2 _ (by linarith) hlt
    linarith
  have hps2' : T.RunExists m₂ 2 → T.procStart m₂ 2 = T.s m₂ 2 + δ₃ := by
    intro h; show T.s m₂ 2 + _ = _; rw [hβ1', hβ2m2 h, ex_δ23]
  -- S8: buffer 3 is not processed between δ₁ and machine 2's next processing start
  have hy3c : ∀ t, δ₁ ≤ t → (T.RunExists m₂ 2 → t ≤ T.procStart m₂ 2) → T.y b₃ t = δ₁ := by
    intro t h1 h2
    have := cap hT b₃ (s := δ₁) (t := t) (a := t) hδ₁.le h1 hτ₃ (fun σ hσ hp => by
      obtain ⟨k, hk, hkp⟩ := (show T.ProcessingBuffer m₂ b₃ σ from hp)
      rcases k with _ | _ | k
      · have := hkp.2.2 hr1'; linarith [hσ.1]
      · exact absurd (hβ1'.symm.trans hk) ex_b32.symm
      · have hr2 : T.RunExists m₂ 2 := run_mono hkp.1 (by omega)
        have := procStart_mono hT hδ hkp.1 (show 2 ≤ k + 2 by omega)
        linarith [h2 hr2, hkp.2.1])
    rw [max_eq_right (by linarith), zero_div, hy3_0 δ₁ hδ₁.le le_rfl] at this
    linarith [hmono b₃ δ₁ t hδ₁.le h1, hy3_0 δ₁ hδ₁.le le_rfl]
  have hy3cL : ∀ t, δ₁ ≤ t → t ≤ L + δ₃ → T.y b₃ t = δ₁ := fun t h1 h2 =>
    hy3c t h1 (fun hr => by rw [hps2' hr]; linarith [hlowL hr])
  -- S9: machine 1 switches to buffer 4 at t4
  obtain ⟨hr2, hs2, hβ2⟩ := clear_switch (m := m₁) (bA := b₁) (bB := b₄) (k := 1) (r := 1)
    (W := t4 + 1) hT hC rfl rfl ex_b14 ex_only₁ hr1 hβ1 hp1 hδ₁.le hτ₁ hX1 (by linarith) hi1
    zero_le_one hR4 (by linarith) (fun u v _ _ _ => by rw [ex_in₁, ex_in₁]; ring)
    (fun t h1 _ hlt => by
      refine Or.inl ?_
      have ht0 : 0 ≤ t := by linarith
      rw [hbal4 t ht0]
      have hy4 : T.y b₄ t = T.y b₄ 0 := cap_zero hT b₄ le_rfl ht0 hτ₄ (fun σ hσ hp => by
        exfalso
        obtain ⟨k, hk, hkp⟩ := (show T.ProcessingBuffer m₁ b₄ σ from hp)
        rcases k with _ | _ | k
        · have := hkp.2.2 hr1; linarith [hσ.1]
        · exact ex_b14 (hβ1.symm.trans hk)
        · have hr2 : T.RunExists m₁ 2 := run_mono hkp.1 (by omega)
          have := s_mono hT hδ hkp.1 (show 2 ≤ k + 2 by omega)
          linarith [hlt hr2, hkp.2.1, s_le_procStart (T := T) hδ m₁ (k + 2), hσ.2])
      rw [hy4, hy0]
      have := hmono b₃ δ₁ t hδ₁.le (by linarith)
      rw [hy3_0 δ₁ hδ₁.le le_rfl] at this
      linarith)
  have hp2 : T.procStart m₁ 2 = t5 := by
    show T.s m₁ 2 + _ = _; rw [hs2, hβ1, hβ2, ex_δ14, ht5]
  -- S10: machine 1 clears buffer 4 at t6 and returns to buffer 1
  have hx4t5 : T.x b₄ t5 = δ₁ := by
    have ht5' : 0 ≤ t5 := by linarith
    rw [hbal4 t5 ht5', hy3cL t5 (by linarith) (by linarith)]
    have := cap hT b₄ (s := 0) (t := t5) (a := t5) le_rfl ht5' hτ₄ (fun σ hσ hp => by
      obtain ⟨k, hk, hkp⟩ := (show T.ProcessingBuffer m₁ b₄ σ from hp)
      rcases k with _ | _ | k
      · have := hkp.2.2 hr1; linarith [hσ.1]
      · exact absurd (hβ1.symm.trans hk) ex_b14
      · have := procStart_mono hT hδ hkp.1 (show 2 ≤ k + 2 by omega)
        linarith [hkp.2.1])
    rw [max_eq_right (by linarith), zero_div, hy0] at this
    linarith [hmono b₄ 0 t5 le_rfl ht5', hy0 b₄]
  have hin4 : ∀ u v, t5 ≤ u → u ≤ v → v ≤ t8 →
      (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).inflow T.y b₄ v - (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).inflow T.y b₄ u = 0 * (v - u) := by
    intro u v hu huv hv
    rw [ex_in₄, ex_in₄, hy3cL v (by linarith) (by linarith), hy3cL u (by linarith) (by linarith)]
    ring
  obtain ⟨-, hx4t6, -, -, -⟩ := clear_low (m := m₁) (bA := b₄) (k := 2) (r := 0) (c := t6) hT hC
    rfl hr2 hβ2 hp2 (by linarith) hτ₄ hx4t5 hδ₁ (by positivity) hR6
    (fun u v hu huv hv => hin4 u v hu huv (by linarith))
  obtain ⟨hr3, hs3, hβ3⟩ := clear_switch (m := m₁) (bA := b₄) (bB := b₁) (k := 2) (r := 0)
    (W := t8) hT hC rfl rfl (Ne.symm ex_b14) ex_only₁r hr2 hβ2 hp2 (by linarith) hτ₄ hx4t5 hδ₁
    (by positivity) le_rfl hR6 (by linarith) hin4
    (fun t _ _ _ => Or.inr (fun σ hσ => by rw [ex_in₁, ex_in₁]; exact hσ))
  have hp3 : T.procStart m₁ 3 = t7 := by
    show T.s m₁ 3 + _ = _; rw [hs3, hβ2, hβ3, ex_δ41, ht7]
  -- S11: buffer 4 stays empty from t6 until machine 2 resumes buffer 3
  have hx4z : ∀ t, t6 ≤ t → (T.RunExists m₂ 2 → t ≤ T.procStart m₂ 2) → T.x b₄ t = 0 := by
    intro t h1 h2
    have h6 : (T.RunExists m₂ 2 → t6 ≤ T.procStart m₂ 2) := fun hr => le_trans h1 (h2 hr)
    have := xdiff hT b₄ (s := t6) (t := t) (by linarith) (by linarith)
    rw [ex_in₄, ex_in₄, hy3c t (by linarith) h2, hy3c t6 (by linarith) h6, hx4t6] at this
    have := hmono b₄ t6 t (by linarith) h1
    linarith [hnn b₄ t (by linarith)]
  -- S12: machine 1 clears buffer 1 again at t8
  have hx1t7 : T.x b₁ t7 = K := by
    have := xdiff hT b₁ (s := t4) (t := t7) (by linarith) (by linarith)
    rw [ex_in₁, ex_in₁, hx1t4] at this
    have hc := cap hT b₁ (s := t4) (t := t7) (a := t7) (by linarith) (by linarith) hτ₁
      (fun σ hσ hp => by
        obtain ⟨k, hk, hkp⟩ := (show T.ProcessingBuffer m₁ b₁ σ from hp)
        rcases k with _ | _ | _ | k
        · exact absurd (hβ01.symm.trans hk) (Ne.symm ex_b14)
        · have := hkp.2.2 hr2; linarith [hσ.1]
        · exact absurd (hβ2.symm.trans hk) (Ne.symm ex_b14)
        · have := procStart_mono hT hδ hkp.1 (show 3 ≤ k + 3 by omega)
          linarith [hkp.2.1])
    rw [max_eq_right (by linarith), zero_div] at hc
    linarith [hmono b₁ t4 t7 (by linarith) (by linarith)]
  obtain ⟨hlow8, hx1t8, -, -, -⟩ := clear_low (m := m₁) (bA := b₁) (k := 3) (r := 1) (c := t8) hT hC
    rfl hr3 hβ3 hp3 (by linarith) hτ₁ hx1t7 hK0 hi1
    (show (t8 - t7) * (1 / τ₁ - 1) = K by rw [hR8, ht7K])
    (fun u v _ _ _ => by rw [ex_in₁, ex_in₁]; ring)
  have hβ4 : T.RunExists m₁ 4 → T.β m₁ 4 = b₄ := fun h => other_buf' hT hC ex_only₁ h hβ3
  -- S13: machine 1 cannot leave buffer 1 before machine 2 leaves buffer 2
  have lemA : T.RunExists m₁ 4 → T.RunExists m₂ 2 ∧ T.s m₂ 2 < T.s m₁ 4 := by
    intro h4
    by_contra hneg
    have hle : T.RunExists m₂ 2 → T.s m₁ 4 ≤ T.s m₂ 2 := fun h2 => by
      by_contra hh; push Not at hh; exact hneg ⟨h2, hh⟩
    have hex := ((hC m₁ 3 hr3).2 h4).2.2
    rw [hβ4 h4] at hex
    have h8 := hlow8 h4
    have hpre : T.RunExists m₂ 2 → T.s m₁ 4 + δ₃ / 2 ≤ T.procStart m₂ 2 := fun h2 => by
      rw [hps2' h2]; linarith [hle h2]
    rcases hex with hx | hin
    · rw [hx4z (T.s m₁ 4) (by linarith) (fun h2 => by linarith [hpre h2])] at hx
      exact lt_irrefl _ hx
    · have := hin (T.s m₁ 4 + δ₃ / 2) (by linarith)
      rw [ex_in₄, ex_in₄, hy3c (T.s m₁ 4) (by linarith) (fun h2 => by linarith [hpre h2]),
        hy3c (T.s m₁ 4 + δ₃ / 2) (by linarith) hpre] at this
      exact lt_irrefl _ this
  -- S14: machine 2 keeps processing buffer 2 until t9
  have hx1z : ∀ t, t8 ≤ t → (T.RunExists m₁ 4 → t < T.s m₁ 4) → T.x b₁ t = 0 := by
    intro t h1 h2
    refine stays_zero' hT b₁ (p := t8) (r := 1) (by linarith) h1 hτ₁ zero_le_one hi1.le
      (fun u v _ _ _ => by rw [ex_in₁, ex_in₁]; linarith)
      (fun σ hσ => show T.ProcessingBuffer m₁ b₁ σ from
        ⟨3, hβ3, hr3, by rw [hp3]; linarith [hσ.1], fun h4 => lt_trans hσ.2 (h2 h4)⟩) hx1t8
  have lemB : T.RunExists m₂ 2 → t9 ≤ T.s m₂ 2 := by
    intro h2
    by_contra hlt; push Not at hlt
    have hL2 := hlowL h2
    have hex := ((hC m₂ 1 hr1').2 h2).1
    rw [hβ1'] at hex
    have hs0 : 0 ≤ T.s m₂ 2 := by linarith
    have hx1s : T.x b₁ (T.s m₂ 2) = 0 :=
      hx1z _ (by linarith) (fun h4 => (lemA h4).2)
    have h1 := hbal1 _ hs0
    have h2' := hbal2 _ hs0
    have h3 := hy2cap _ hs0
    rw [max_eq_left (by linarith)] at h3
    have := hg _ hlt
    linarith
  have hs4 : T.RunExists m₁ 4 → t9 ≤ T.s m₁ 4 := fun h4 =>
    le_trans (lemB (lemA h4).1) (lemA h4).2.le
  have hpt9 : T.RunExists m₂ 2 → t9 ≤ T.procStart m₂ 2 := fun h2 => by
    rw [hps2' h2]; linarith [lemB h2]
  -- S15: the state at t9
  have hy2t3 : T.y b₂ t3 = 0 := by
    have := hy2cap t3 (by linarith)
    rw [sub_self, max_self, zero_div] at this
    linarith [hmono b₂ 0 t3 le_rfl (by linarith), hy0 b₂]
  have hfull2 := tr_full hT b₂ (s := t3) (t := t9) (by linarith) (by linarith) (fun σ hσ => by
    refine ⟨show T.ProcessingBuffer m₂ b₂ σ from
      ⟨1, hβ1', hr1', by rw [hp1']; exact hσ.1, fun h2 => lt_of_lt_of_le hσ.2 (lemB h2)⟩, ?_⟩
    rcases lt_or_ge σ L with h | h
    · exact hpos2 σ (by linarith [hσ.1]) h
    · have hσ0 : 0 ≤ σ := by linarith
      have hx1σ := hx1z σ (by linarith) (fun h4 => lt_of_lt_of_le hσ.2 (hs4 h4))
      rw [hbal2 σ hσ0]
      have h1 := hbal1 σ hσ0
      have h3 := hy2cap σ hσ0
      rw [max_eq_left (by linarith)] at h3
      have := hg σ hσ.2
      linarith)
  rw [hy2t3, ex_pt₂] at hfull2
  have ht90 : 0 ≤ t9 := by linarith
  have hx1t9 : T.x b₁ t9 = 0 := hx1z t9 (by linarith) (fun h4 =>
    lt_of_le_of_lt (lemB (lemA h4).1) (lemA h4).2)
  have hy3t9 : T.y b₃ t9 = δ₁ := hy3c t9 (by linarith) hpt9
  have hx4t9 : T.x b₄ t9 = 0 := hx4z t9 (by linarith) hpt9
  refine ⟨ex_cases _ ?_ ?_ ?_ ?_, Or.inr ⟨3, hr3, hβ3, by rw [hs3]; linarith, hs4⟩,
    Or.inr ⟨1, hr1', hβ1', by rw [hs1']; linarith, lemB⟩⟩
  · show T.x b₁ t9 = 0; exact hx1t9
  · show T.x b₂ t9 = 0
    rw [hbal2 t9 ht90]
    have := hbal1 t9 ht90
    rw [hx1t9] at this
    linarith [hR9]
  · show T.x b₃ t9 = t9 - δ₁
    rw [hbal3 t9 ht90, hy3t9]
  · show T.x b₄ t9 = 0; exact hx4t9

end KS2
end KumarSeidman.TwoType

open KumarSeidman.TwoType KumarSeidman.TwoType.Example2 KumarSeidman.TwoType.KS2 in
theorem solution (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    ∃ ξ₀ : ℝ, ∀ ξ ≥ ξ₀, ∀ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃) →
        let t₉ := (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1)
        (∀ b, T.x b t₉ = levels 0 0 (t₉ - δ₁) 0 b) ∧ T.SetupFor m₁ t₉ b₁ ∧
          T.SetupFor m₂ t₉ b₂ := by
  refine ⟨(δ₁ + (δ₄ + τ₄ * δ₁ + δ₁) + 1) / (τ₂ - τ₁), fun ξ hξ T hcl => ?_⟩
  have hτ12 : 0 < τ₂ - τ₁ := by linarith
  have h := (div_le_iff₀ hτ12).mp hξ
  exact stage8_traj τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄ hδ₁ hδ₂ hδ₃ hδ₄ h7 h1₁ h1₂ ξ
    (by linarith [mul_comm ξ (τ₂ - τ₁)]) T hcl
