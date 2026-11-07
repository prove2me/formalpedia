-- Prove2me | solution 1 for KumarSeidman.TwoType.case1_periodic
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:27:03.530992+00:00
-- url     : https://prove2.me/submissions/ca771bba-94bf-4652-b869-5446cf5572dd

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
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1)
    (T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule) :
    let η := (δ₁ + δ₄) / (1 - τ₁ - τ₄)
    T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃) →
      (∀ b, T.x b η = levels 0 η 0 η b) ∧ T.SetupFor m₁ η b₁ ∧ T.SetupFor m₂ η b₃ := by
  intro η hcl
  obtain ⟨hT, ⟨hx0, hβ0⟩, hC⟩ := hcl
  have hδ := ex_hδ (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) hδ₁ hδ₂ hδ₃ hδ₄
  have hD1 : 0 < 1 - τ₁ - τ₄ := by linarith
  have hD2 : 0 < 1 - τ₂ - τ₃ := by linarith
  have hηdef : η = (δ₁ + δ₄) / (1 - τ₁ - τ₄) := rfl
  have hη0 : 0 < η := by positivity
  have hηa : η * (1 - τ₁ - τ₄) = δ₁ + δ₄ := by rw [hηdef]; field_simp
  have hηb : η * (1 - τ₂ - τ₃) = δ₂ + δ₃ := by rw [hηdef, h8]; field_simp
  rw [← hηdef] at h9 h10
  have hP1 : δ₄ + τ₄ * η + δ₁ = η * (1 - τ₁) := by linear_combination -hηa
  have hP3 : δ₂ + τ₂ * η + δ₃ = η * (1 - τ₃) := by linear_combination -hηb
  have hA : δ₄ + τ₄ * η < δ₂ + τ₂ * η + δ₃ := by nlinarith
  have hB : δ₂ + τ₂ * η < δ₄ + τ₄ * η + δ₁ := by nlinarith
  have hAη : δ₄ + τ₄ * η < η := by nlinarith
  have hBη : δ₂ + τ₂ * η < η := by nlinarith
  have hx1 : T.x b₁ 0 = 0 := hx0 b₁
  have hx2 : T.x b₂ 0 = η := hx0 b₂
  have hx3 : T.x b₃ 0 = 0 := hx0 b₃
  have hx4 : T.x b₄ 0 = η := hx0 b₄
  have hβ01 : T.β m₁ 0 = b₁ := hβ0 m₁
  have hβ02 : T.β m₂ 0 = b₃ := hβ0 m₂
  have hmono : ∀ b u v, 0 ≤ u → u ≤ v → T.y b u ≤ T.y b v := fun b u v hu huv =>
    tr_mono hT b hu huv
  -- first switches
  obtain ⟨hr1, hs1, hβ1⟩ := first_switch (m := m₁) (bX := b₁) (bY := b₄) hT hC hδ rfl rfl ex_b14 ex_only₁
    hβ01 hx1 hτ₁ (show τ₁ ≤ 1 by linarith) (ex_in₁ T.y) (by rw [hx4]; exact hη0)
    (fun u v hu huv => by rw [ex_in₄, ex_in₄]; exact hmono _ u v hu huv) hτ₄
  obtain ⟨hr1', hs1', hβ1'⟩ := first_switch (m := m₂) (bX := b₃) (bY := b₂) hT hC hδ rfl rfl ex_b32 ex_only₂
    hβ02 hx3 hτ₃ (show τ₃ ≤ 1 by linarith) (ex_in₃ T.y) (by rw [hx2]; exact hη0)
    (fun u v hu huv => by rw [ex_in₂, ex_in₂]; exact hmono _ u v hu huv) hτ₂
  have hd1 : T.procStart m₁ 1 = δ₄ := by
    show T.s m₁ 1 + _ = _; rw [hs1, hβ01, hβ1, ex_δ14]; ring
  have hd2 : T.procStart m₂ 1 = δ₂ := by
    show T.s m₂ 1 + _ = _; rw [hs1', hβ02, hβ1', ex_δ32]; ring
  have he1 : T.RunExists m₁ 2 → T.procStart m₁ 2 = T.s m₁ 2 + δ₁ := by
    intro h2
    show T.s m₁ 2 + _ = _
    rw [hβ1, other_buf hT hC ex_only₁ h2 hβ1, ex_δ41]
  have he2 : T.RunExists m₂ 2 → T.procStart m₂ 2 = T.s m₂ 2 + δ₃ := by
    intro h2
    show T.s m₂ 2 + _ = _
    rw [hβ1', other_buf hT hC ex_only₂ h2 hβ1', ex_δ23]
  obtain ⟨-, -, hyX1⟩ := machine_low (m := m₁) (bX := b₁) (bY := b₄) hT hC hδ rfl rfl ex_b14 ex_only₁ hβ01
    hr1 hs1 hβ1 hd1 he1 hτ₁ hτ₄ (by rw [hx4]; exact hη0)
    (fun u v hu huv => by rw [ex_in₄, ex_in₄]; exact hmono _ u v hu huv)
  obtain ⟨-, -, hyX2⟩ := machine_low (m := m₂) (bX := b₃) (bY := b₂) hT hC hδ rfl rfl ex_b32 ex_only₂ hβ02
    hr1' hs1' hβ1' hd2 he2 hτ₃ hτ₂ (by rw [hx2]; exact hη0)
    (fun u v hu huv => by rw [ex_in₂, ex_in₂]; exact hmono _ u v hu huv)
  rw [hx4] at hyX1
  rw [hx2] at hyX2
  obtain ⟨hr2, hs2, hβ2, hs3, hyη1, hxη1, hyη4⟩ := machine_rest (m := m₁) (bX := b₁) (bY := b₄)
    (Q := δ₂ + τ₂ * η + δ₃) (η := η) hT hC hδ rfl rfl ex_b14 ex_only₁ hβ01
    hr1 hs1 hβ1 hd1 hδ₄.le he1 hτ₁ (show τ₁ < 1 by linarith) hτ₄ (by rw [hx4]; exact hη0) hx1
    (fun u v hu huv => by rw [ex_in₄, ex_in₄]; exact hmono _ u v hu huv)
    (by rw [hx4]; exact hA)
    (fun t ht htQ => by rw [ex_in₄, ex_in₄]; exact hyX2 t ht htQ)
    (ex_in₁ T.y) (by rw [hx4]; exact hP1) hη0
  obtain ⟨hr2', hs2', hβ2', hs3', hyη3, hxη3, hyη2⟩ := machine_rest (m := m₂) (bX := b₃) (bY := b₂)
    (Q := δ₄ + τ₄ * η + δ₁) (η := η) hT hC hδ rfl rfl ex_b32 ex_only₂ hβ02
    hr1' hs1' hβ1' hd2 hδ₂.le he2 hτ₃ (show τ₃ < 1 by linarith) hτ₂ (by rw [hx2]; exact hη0) hx3
    (fun u v hu huv => by rw [ex_in₂, ex_in₂]; exact hmono _ u v hu huv)
    (by rw [hx2]; exact hB)
    (fun t ht htQ => by rw [ex_in₂, ex_in₂]; exact hyX1 t ht htQ)
    (ex_in₃ T.y) (by rw [hx2]; exact hP3) hη0
  have hy0 := tr_y0 hT
  refine ⟨?_, ?_, ?_⟩
  · refine ex_cases _ ?_ ?_ ?_ ?_
    · rw [hxη1]; rfl
    · have := xdiff hT b₂ (s := 0) (t := η) le_rfl hη0.le
      rw [ex_in₂, ex_in₂] at this
      show T.x b₂ η = η
      rw [hx2] at hyη2
      linarith
    · rw [hxη3]; rfl
    · have := xdiff hT b₄ (s := 0) (t := η) le_rfl hη0.le
      rw [ex_in₄, ex_in₄] at this
      show T.x b₄ η = η
      rw [hx4] at hyη4
      linarith
  · refine Or.inr ⟨2, hr2, hβ2, ?_, hs3⟩
    rw [hs2, hx4]; exact hAη
  · refine Or.inr ⟨2, hr2', hβ2', ?_, hs3'⟩
    rw [hs2', hx2]; exact hBη

