-- Prove2me | solution 1 for KumarSeidman.TwoType.example2_modes_coexist
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T09:21:07.952495+00:00
-- url     : https://prove2.me/submissions/c03c0ba5-a4cd-451b-aa26-b8369fa05f11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2
import Theorems.Thm_KumarSeidman_TwoType_example2_periodic_trajectory_exists
import Theorems.Thm_KumarSeidman_TwoType_example2_unstable_trajectory_exists

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

theorem case1_traj (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h8 : (δ₁ + δ₄) / (1 - τ₁ - τ₄) = (δ₂ + δ₃) / (1 - τ₂ - τ₃))
    (h9 : δ₄ < (1 - τ₃ - τ₄) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h10 : δ₂ < (1 - τ₁ - τ₂) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1)
    (T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule) :
    let η := (δ₁ + δ₄) / (1 - τ₁ - τ₄)
    T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃) →
      (∀ b, T.x b η = levels 0 η 0 η b) ∧ T.SetupFor m₁ η b₁ ∧ T.SetupFor m₂ η b₃ ∧
      (∃ k, T.RunExists m₁ k ∧ T.β m₁ k = b₁ ∧ T.procStart m₁ k ≤ η ∧
        (T.RunExists m₁ (k + 1) → η ≤ T.s m₁ (k + 1))) ∧
      (∃ k, T.RunExists m₂ k ∧ T.β m₂ k = b₃ ∧ T.procStart m₂ k ≤ η ∧
        (T.RunExists m₂ (k + 1) → η ≤ T.s m₂ (k + 1))) := by
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
  refine ⟨?_, ?_, ?_, ⟨2, hr2, hβ2, ?_, hs3⟩, ⟨2, hr2', hβ2', ?_, hs3'⟩⟩
  rotate_left 3
  · rw [he1 hr2, hs2, hx4]; show δ₄ + τ₄ * η + δ₁ ≤ η; linarith [mul_pos hη0 hτ₁]
  · rw [he2 hr2', hs2', hx2]; show δ₂ + τ₂ * η + δ₃ ≤ η; linarith [mul_pos hη0 hτ₃]
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
      T.SetupFor m₂ t₉ b₂ ∧
      (∃ k, T.RunExists m₁ k ∧ T.β m₁ k = b₁ ∧ T.procStart m₁ k ≤ t₉ ∧
        (T.RunExists m₁ (k + 1) → t₉ ≤ T.s m₁ (k + 1))) ∧
      (∃ k, T.RunExists m₂ k ∧ T.β m₂ k = b₂ ∧ T.procStart m₂ k ≤ t₉ ∧
        (T.RunExists m₂ (k + 1) → t₉ ≤ T.s m₂ (k + 1))) := by
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
    Or.inr ⟨1, hr1', hβ1', by rw [hs1']; linarith, lemB⟩,
    ⟨3, hr3, hβ3, by rw [hp3]; linarith, hs4⟩, ⟨1, hr1', hβ1', by rw [hp1']; linarith, lemB⟩⟩
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


namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory

namespace KS2

section Ex2
variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}
theorem ex_casesM (P : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer → Prop) (h3 : P b₃) (h4 : P b₄)
    (h1 : P b₁) (h2 : P b₂) : ∀ b, P b := ex_cases P h1 h2 h3 h4
end Ex2

set_option maxHeartbeats 4000000 in
theorem stage8_trajM (τ₃ τ₄ τ₁ τ₂ δ₃ δ₄ δ₁ δ₂ : ℝ)
    (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (h7 : τ₄ + τ₂ > 1) (h1₁ : τ₃ + τ₂ < 1) (h1₂ : τ₄ + τ₁ < 1) (ξ : ℝ)
    (hξ : δ₃ + (δ₂ + τ₂ * δ₃ + δ₃) + 1 ≤ (τ₄ - τ₃) * ξ)
    (T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule)
    (hcl : T.IsClearingFrom (levels 0 0 ξ 0) (setups b₁ b₂)) :
    let t₉ := (ξ + τ₄⁻¹ * (δ₃ + δ₄)) / (τ₄⁻¹ - 1)
    (∀ b, T.x b t₉ = levels (t₉ - δ₃) 0 0 0 b) ∧ T.SetupFor m₂ t₉ b₃ ∧
      T.SetupFor m₁ t₉ b₄ ∧
      (∃ k, T.RunExists m₂ k ∧ T.β m₂ k = b₃ ∧ T.procStart m₂ k ≤ t₉ ∧
        (T.RunExists m₂ (k + 1) → t₉ ≤ T.s m₂ (k + 1))) ∧
      (∃ k, T.RunExists m₁ k ∧ T.β m₁ k = b₄ ∧ T.procStart m₁ k ≤ t₉ ∧
        (T.RunExists m₁ (k + 1) → t₉ ≤ T.s m₁ (k + 1))) := by
  intro t9
  have ht9 : t9 = (ξ + τ₄⁻¹ * (δ₃ + δ₄)) / (τ₄⁻¹ - 1) := rfl
  clear_value t9
  obtain ⟨hT, ⟨hx0, hβ0⟩, hC⟩ := hcl
  have hδ := ex_hδ (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) hδ₁ hδ₂ hδ₃ hδ₄
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = δ₂ + τ₂ * δ₃ + δ₃ := ⟨_, rfl⟩
  obtain ⟨t3, ht3⟩ : ∃ t : ℝ, t = δ₃ + δ₄ := ⟨_, rfl⟩
  obtain ⟨t4, ht4⟩ : ∃ t : ℝ, t = (ξ * τ₃ + δ₃) / (1 - τ₃) := ⟨_, rfl⟩
  obtain ⟨t5, ht5⟩ : ∃ t : ℝ, t = t4 + δ₂ := ⟨_, rfl⟩
  obtain ⟨t6, ht6⟩ : ∃ t : ℝ, t = t5 + τ₂ * δ₃ := ⟨_, rfl⟩
  obtain ⟨t7, ht7⟩ : ∃ t : ℝ, t = t6 + δ₃ := ⟨_, rfl⟩
  obtain ⟨t8, ht8⟩ : ∃ t : ℝ, t = t7 + K * τ₃ / (1 - τ₃) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ t : ℝ, t = t3 + τ₄ * (ξ + t4) := ⟨_, rfl⟩
  obtain ⟨hτ12, hτ2, hτ1', hτ4', hτ3', hξ0, hK0, hR4, hR4', ht4δ, ht7K, hR8, hR6, ht78, hLt8, hLt9,
    ht3L, ht3δ, ht45, ht56, ht67, hg, hlo1, hlo2, hi1, hi4, hi2, hR9⟩ :=
    stage8_arith τ₃ τ₄ τ₁ τ₂ δ₃ δ₄ δ₁ δ₂ ξ K t3 t4 t5 t6 t7 t8 t9 L hτ₃ hτ₄ hτ₁ hτ₂ hδ₃ hδ₄ hδ₁ hδ₂
      h7 h1₁ h1₂ hK (by rw [hK]; exact hξ) ht9 ht3 ht4 ht5 ht6 ht7 ht8 hL
  have hx1 : T.x b₃ 0 = ξ := hx0 b₃
  have hx2 : T.x b₄ 0 = 0 := hx0 b₄
  have hx3 : T.x b₁ 0 = 0 := hx0 b₁
  have hx4 : T.x b₂ 0 = 0 := hx0 b₂
  have hβ01 : T.β m₂ 0 = b₂ := hβ0 m₂
  have hβ02 : T.β m₁ 0 = b₁ := hβ0 m₁
  have hy0 := tr_y0 hT
  have hmono : ∀ b u v, 0 ≤ u → u ≤ v → T.y b u ≤ T.y b v := fun b u v hu huv =>
    tr_mono hT b hu huv
  have hnn : ∀ b t, 0 ≤ t → 0 ≤ T.x b t := fun b t ht => tr_nonneg hT b ht
  have hbal1 : ∀ t, 0 ≤ t → T.x b₃ t = ξ + t - T.y b₃ t := by
    intro t ht; rw [tr_bal hT b₃ ht, hx1, ex_in₃]
  have hbal2 : ∀ t, 0 ≤ t → T.x b₄ t = T.y b₃ t - T.y b₄ t := by
    intro t ht; rw [tr_bal hT b₄ ht, hx2, ex_in₄]; ring
  have hbal3 : ∀ t, 0 ≤ t → T.x b₁ t = t - T.y b₁ t := by
    intro t ht; rw [tr_bal hT b₁ ht, hx3, ex_in₁]; ring
  have hbal4 : ∀ t, 0 ≤ t → T.x b₂ t = T.y b₁ t - T.y b₂ t := by
    intro t ht; rw [tr_bal hT b₂ ht, hx4, ex_in₂]; ring
  have hr0₁ := (tr_run0 hT m₂).1
  have hr0₂ := (tr_run0 hT m₁).1
  have hs0₁ : T.s m₂ 0 = 0 := (tr_run0 hT m₂).2
  have hs0₂ : T.s m₁ 0 = 0 := (tr_run0 hT m₁).2
  have hpp0₂ : T.procStart m₁ 0 = 0 := hs0₂
  have hpp0₁ : T.procStart m₂ 0 = 0 := hs0₁
  have hsnn : ∀ m k, T.RunExists m k → 0 ≤ T.s m k := by
    intro m k h
    have := s_mono hT hδ h (Nat.zero_le k)
    rw [(tr_run0 hT m).2] at this; exact this
  -- S1: machine 1 cannot process buffer 1 before δ₃
  have hβ1m1 : T.RunExists m₂ 1 → T.β m₂ 1 = b₃ := fun h => other_buf hT hC ex_only₂ h hβ01
  have hps1 : T.RunExists m₂ 1 → T.procStart m₂ 1 = T.s m₂ 1 + δ₃ := by
    intro h; show T.s m₂ 1 + _ = _; rw [hβ01, hβ1m1 h, ex_δ23]
  have hproc1_early : ∀ σ, T.ProcessingBuffer m₂ b₃ σ → δ₃ ≤ σ := by
    intro σ ⟨k, hk, hkp⟩
    rcases k with _ | k
    · exact absurd (hβ01.symm.trans hk) (Ne.symm ex_b32)
    · have h1 : T.RunExists m₂ 1 := run_mono hkp.1 (by omega)
      have := procStart_mono hT hδ hkp.1 (show 1 ≤ k + 1 by omega)
      rw [hps1 h1] at this
      linarith [hkp.2.1, hsnn m₂ 1 h1]
  have hy1_0 : ∀ t, 0 ≤ t → t ≤ δ₃ → T.y b₃ t = 0 := by
    intro t ht htd
    have := cap hT b₃ (s := 0) (t := t) (a := δ₃) le_rfl ht hτ₃
      (fun σ _ hp => hproc1_early σ hp)
    rw [max_eq_right (by linarith), zero_div, hy0] at this
    linarith [hmono b₃ 0 t le_rfl ht, hy0 b₃]
  -- S2: machine 2 cannot leave buffer 3 before δ₃
  have hβ1m2 : T.RunExists m₁ 1 → T.β m₁ 1 = b₄ := fun h => other_buf' hT hC ex_only₁ h hβ02
  have hs1m2_low : T.RunExists m₁ 1 → δ₃ ≤ T.s m₁ 1 := by
    intro h
    have hex := ((hC m₁ 0 hr0₂).2 h).2.2
    rw [hβ1m2 h] at hex
    by_contra hlt; push Not at hlt
    have hs := hsnn m₁ 1 h
    rcases hex with hx | hin
    · rw [hbal2 _ hs, hy1_0 _ hs hlt.le] at hx
      linarith [hmono b₄ 0 (T.s m₁ 1) le_rfl hs, hy0 b₄]
    · have := hin δ₃ hlt
      rw [ex_in₄, ex_in₄, hy1_0 _ hs hlt.le, hy1_0 δ₃ hδ₃.le le_rfl] at this
      exact lt_irrefl _ this
  -- S3: buffer 3 empty on [0, δ₃]
  have hx3_0 : ∀ t, 0 ≤ t → t ≤ δ₃ → T.x b₁ t = 0 := by
    intro t ht htd
    refine stays_zero' hT b₁ (p := 0) (r := 1) le_rfl ht hτ₁ zero_le_one
      (show (1:ℝ) ≤ 1 / τ₁ by rw [le_div_iff₀ hτ₁]; linarith)
      (fun u v _ _ _ => by rw [ex_in₁, ex_in₁]; linarith)
      (fun σ hσ => show T.ProcessingBuffer m₁ b₁ σ from ⟨0, hβ02, hr0₂, by rw [hpp0₂]; exact hσ.1,
        fun h1 => by linarith [hσ.2, hs1m2_low h1]⟩) hx3
  have hy3_0 : ∀ t, 0 ≤ t → t ≤ δ₃ → T.y b₁ t = t := by
    intro t ht htd; have := hbal3 t ht; rw [hx3_0 t ht htd] at this; linarith
  -- S4: machine 1 switches to buffer 1 at time 0
  obtain ⟨hr1, hs1, hβ1⟩ := first_switch' (m := m₂) (bX := b₂) (bY := b₃) hT hC hδ rfl rfl
    (Ne.symm ex_b32) ex_only₂r hβ01 hx4 hτ₂ hτ4'.le hδ₃
    (fun u v hu huv hv => by
      rw [ex_in₂, ex_in₂, hy3_0 v (by linarith) hv, hy3_0 u hu (by linarith)]; linarith)
    (by rw [hx1]; exact hξ0) (fun u v _ huv => by rw [ex_in₃, ex_in₃]; exact huv) hτ₃
  have hp1 : T.procStart m₂ 1 = δ₃ := by rw [hps1 hr1, hs1]; ring
  -- S5: buffer 1 is cleared at t4, and not before
  have hX1 : T.x b₃ δ₃ = ξ + δ₃ := by
    rw [hbal1 δ₃ hδ₃.le, hy1_0 δ₃ hδ₃.le le_rfl]; ring
  obtain ⟨hlow4, hx1t4, -, hpos1, -⟩ := clear_low (m := m₂) (bA := b₃) (k := 1) (r := 1) hT hC rfl
    hr1 hβ1 hp1 hδ₃.le hτ₃ hX1 (by linarith) hi1 hR4
    (fun u v _ _ _ => by rw [ex_in₃, ex_in₃]; ring)
  have hy1_lin : ∀ t, δ₃ ≤ t → t ≤ t4 → T.y b₃ t = (t - δ₃) / τ₃ := by
    intro t h1 h2
    have := tr_full hT b₃ (s := δ₃) (t := t) hδ₃.le h1 (fun σ hσ =>
      ⟨show T.ProcessingBuffer m₂ b₃ σ from
        ⟨1, hβ1, hr1, by rw [hp1]; exact hσ.1, fun h2' => by linarith [hσ.2, hlow4 h2']⟩,
        hpos1 σ hσ.1 (by linarith [hσ.2])⟩)
    rw [hy1_0 δ₃ hδ₃.le le_rfl, ex_pt₃] at this
    linarith
  have hy1t4 : T.y b₃ t4 = ξ + t4 := by rw [hy1_lin t4 ht4δ.le le_rfl, hR4']
  -- S6: machine 2 switches to buffer 2 exactly at δ₃
  have claim6 : ∀ t, δ₃ < t → t < t4 → (T.RunExists m₁ 1 → t < T.s m₁ 1) → False := by
    intro t h1 h2 hlt
    have hx3t : T.x b₁ t = 0 := by
      refine stays_zero' hT b₁ (p := 0) (r := 1) le_rfl (by linarith) hτ₁ zero_le_one
        (show (1:ℝ) ≤ 1 / τ₁ by rw [le_div_iff₀ hτ₁]; linarith)
        (fun u v _ _ _ => by rw [ex_in₁, ex_in₁]; linarith)
        (fun σ hσ => show T.ProcessingBuffer m₁ b₁ σ from ⟨0, hβ02, hr0₂, by rw [hpp0₂]; exact hσ.1,
          fun h1' => lt_trans hσ.2 (hlt h1')⟩) hx3
    have hdem : T.Demanding b₄ t := by
      refine Or.inr (fun σ hσ => ?_)
      rw [ex_in₄, ex_in₄, hy1_lin t h1.le h2.le]
      rcases le_total σ t4 with h | h
      · rw [hy1_lin σ (by linarith) h]
        exact div_lt_div_of_pos_right (by linarith) hτ₃
      · have := hmono b₃ t4 σ (by linarith) h
        rw [hy1t4] at this
        have : (t - δ₃) / τ₃ < ξ + t4 := by
          rw [← hR4']; exact div_lt_div_of_pos_right (by linarith) hτ₃
        linarith
    have hc := (hC m₁ 0 hr0₂).1 t (by rw [hpp0₂]; linarith) hlt
    apply hc
    rw [hβ02]
    exact ⟨hx3t, b₄, rfl, Ne.symm ex_b14, hdem⟩
  have hr1' : T.RunExists m₁ 1 := by
    by_contra h
    exact claim6 ((δ₃ + t4) / 2) (by linarith) (by linarith) (fun h' => absurd h' h)
  have hs1' : T.s m₁ 1 = δ₃ := by
    refine le_antisymm ?_ (hs1m2_low hr1')
    by_contra hgt; push Not at hgt
    have := lt_min hgt ht4δ
    exact claim6 ((δ₃ + min (T.s m₁ 1) t4) / 2) (by linarith)
      (by linarith [min_le_right (T.s m₁ 1) t4])
      (fun _ => by linarith [min_le_left (T.s m₁ 1) t4])
  have hβ1' : T.β m₁ 1 = b₄ := hβ1m2 hr1'
  have hp1' : T.procStart m₁ 1 = t3 := by
    show T.s m₁ 1 + _ = _; rw [hs1', hβ02, hβ1', ex_δ14, ht3]
  -- S7: lower bound L for the end of machine 2's run on buffer 2
  have hβ2m2 : T.RunExists m₁ 2 → T.β m₁ 2 = b₁ := fun h => other_buf hT hC ex_only₁ h hβ1'
  have hy2cap : ∀ t, 0 ≤ t → T.y b₄ t ≤ max (t - t3) 0 / τ₄ := by
    intro t ht
    have := cap hT b₄ (s := 0) (t := t) (a := t3) le_rfl ht hτ₄ (fun σ _ hp => by
      have := (procY_cases hT hδ (bX := b₁) (bY := b₄) ex_b14 hβ02 hr1' hβ2m2
        (show T.ProcessingBuffer m₁ b₄ σ from hp)).1
      rw [hp1'] at this; exact this)
    rw [hy0, ex_pt₄] at this
    linarith
  have hpos2 : ∀ t, δ₃ < t → t < L → 0 < T.x b₄ t := by
    intro t h1 h2
    have ht0 : 0 ≤ t := by linarith
    rw [hbal2 t ht0]
    have hc := hy2cap t ht0
    rcases le_total t t4 with h | h
    · rw [hy1_lin t h1.le h]; linarith [hlo1 t h1]
    · have := hmono b₃ t4 t (by linarith) h
      rw [hy1t4] at this
      linarith [hlo2 t h2]
  have hlowL : T.RunExists m₁ 2 → L ≤ T.s m₁ 2 := by
    intro h2
    have hex := ((hC m₁ 1 hr1').2 h2).1
    rw [hβ1'] at hex
    have : t3 ≤ T.s m₁ 2 := by rw [← hp1']; exact tr_setup hT h2
    by_contra hlt; push Not at hlt
    have := hpos2 _ (by linarith) hlt
    linarith
  have hps2' : T.RunExists m₁ 2 → T.procStart m₁ 2 = T.s m₁ 2 + δ₁ := by
    intro h; show T.s m₁ 2 + _ = _; rw [hβ1', hβ2m2 h, ex_δ41]
  -- S8: buffer 3 is not processed between δ₃ and machine 2's next processing start
  have hy3c : ∀ t, δ₃ ≤ t → (T.RunExists m₁ 2 → t ≤ T.procStart m₁ 2) → T.y b₁ t = δ₃ := by
    intro t h1 h2
    have := cap hT b₁ (s := δ₃) (t := t) (a := t) hδ₃.le h1 hτ₁ (fun σ hσ hp => by
      obtain ⟨k, hk, hkp⟩ := (show T.ProcessingBuffer m₁ b₁ σ from hp)
      rcases k with _ | _ | k
      · have := hkp.2.2 hr1'; linarith [hσ.1]
      · exact absurd (hβ1'.symm.trans hk) ex_b14.symm
      · have hr2 : T.RunExists m₁ 2 := run_mono hkp.1 (by omega)
        have := procStart_mono hT hδ hkp.1 (show 2 ≤ k + 2 by omega)
        linarith [h2 hr2, hkp.2.1])
    rw [max_eq_right (by linarith), zero_div, hy3_0 δ₃ hδ₃.le le_rfl] at this
    linarith [hmono b₁ δ₃ t hδ₃.le h1, hy3_0 δ₃ hδ₃.le le_rfl]
  have hy3cL : ∀ t, δ₃ ≤ t → t ≤ L + δ₁ → T.y b₁ t = δ₃ := fun t h1 h2 =>
    hy3c t h1 (fun hr => by rw [hps2' hr]; linarith [hlowL hr])
  -- S9: machine 1 switches to buffer 4 at t4
  obtain ⟨hr2, hs2, hβ2⟩ := clear_switch (m := m₂) (bA := b₃) (bB := b₂) (k := 1) (r := 1)
    (W := t4 + 1) hT hC rfl rfl ex_b32 ex_only₂ hr1 hβ1 hp1 hδ₃.le hτ₃ hX1 (by linarith) hi1
    zero_le_one hR4 (by linarith) (fun u v _ _ _ => by rw [ex_in₃, ex_in₃]; ring)
    (fun t h1 _ hlt => by
      refine Or.inl ?_
      have ht0 : 0 ≤ t := by linarith
      rw [hbal4 t ht0]
      have hy4 : T.y b₂ t = T.y b₂ 0 := cap_zero hT b₂ le_rfl ht0 hτ₂ (fun σ hσ hp => by
        exfalso
        obtain ⟨k, hk, hkp⟩ := (show T.ProcessingBuffer m₂ b₂ σ from hp)
        rcases k with _ | _ | k
        · have := hkp.2.2 hr1; linarith [hσ.1]
        · exact ex_b32 (hβ1.symm.trans hk)
        · have hr2 : T.RunExists m₂ 2 := run_mono hkp.1 (by omega)
          have := s_mono hT hδ hkp.1 (show 2 ≤ k + 2 by omega)
          linarith [hlt hr2, hkp.2.1, s_le_procStart (T := T) hδ m₂ (k + 2), hσ.2])
      rw [hy4, hy0]
      have := hmono b₁ δ₃ t hδ₃.le (by linarith)
      rw [hy3_0 δ₃ hδ₃.le le_rfl] at this
      linarith)
  have hp2 : T.procStart m₂ 2 = t5 := by
    show T.s m₂ 2 + _ = _; rw [hs2, hβ1, hβ2, ex_δ32, ht5]
  -- S10: machine 1 clears buffer 4 at t6 and returns to buffer 1
  have hx4t5 : T.x b₂ t5 = δ₃ := by
    have ht5' : 0 ≤ t5 := by linarith
    rw [hbal4 t5 ht5', hy3cL t5 (by linarith) (by linarith)]
    have := cap hT b₂ (s := 0) (t := t5) (a := t5) le_rfl ht5' hτ₂ (fun σ hσ hp => by
      obtain ⟨k, hk, hkp⟩ := (show T.ProcessingBuffer m₂ b₂ σ from hp)
      rcases k with _ | _ | k
      · have := hkp.2.2 hr1; linarith [hσ.1]
      · exact absurd (hβ1.symm.trans hk) ex_b32
      · have := procStart_mono hT hδ hkp.1 (show 2 ≤ k + 2 by omega)
        linarith [hkp.2.1])
    rw [max_eq_right (by linarith), zero_div, hy0] at this
    linarith [hmono b₂ 0 t5 le_rfl ht5', hy0 b₂]
  have hin4 : ∀ u v, t5 ≤ u → u ≤ v → v ≤ t8 →
      (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).inflow T.y b₂ v - (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).inflow T.y b₂ u = 0 * (v - u) := by
    intro u v hu huv hv
    rw [ex_in₂, ex_in₂, hy3cL v (by linarith) (by linarith), hy3cL u (by linarith) (by linarith)]
    ring
  obtain ⟨-, hx4t6, -, -, -⟩ := clear_low (m := m₂) (bA := b₂) (k := 2) (r := 0) (c := t6) hT hC
    rfl hr2 hβ2 hp2 (by linarith) hτ₂ hx4t5 hδ₃ (by positivity) hR6
    (fun u v hu huv hv => hin4 u v hu huv (by linarith))
  obtain ⟨hr3, hs3, hβ3⟩ := clear_switch (m := m₂) (bA := b₂) (bB := b₃) (k := 2) (r := 0)
    (W := t8) hT hC rfl rfl (Ne.symm ex_b32) ex_only₂r hr2 hβ2 hp2 (by linarith) hτ₂ hx4t5 hδ₃
    (by positivity) le_rfl hR6 (by linarith) hin4
    (fun t _ _ _ => Or.inr (fun σ hσ => by rw [ex_in₃, ex_in₃]; exact hσ))
  have hp3 : T.procStart m₂ 3 = t7 := by
    show T.s m₂ 3 + _ = _; rw [hs3, hβ2, hβ3, ex_δ23, ht7]
  -- S11: buffer 4 stays empty from t6 until machine 2 resumes buffer 3
  have hx4z : ∀ t, t6 ≤ t → (T.RunExists m₁ 2 → t ≤ T.procStart m₁ 2) → T.x b₂ t = 0 := by
    intro t h1 h2
    have h6 : (T.RunExists m₁ 2 → t6 ≤ T.procStart m₁ 2) := fun hr => le_trans h1 (h2 hr)
    have := xdiff hT b₂ (s := t6) (t := t) (by linarith) (by linarith)
    rw [ex_in₂, ex_in₂, hy3c t (by linarith) h2, hy3c t6 (by linarith) h6, hx4t6] at this
    have := hmono b₂ t6 t (by linarith) h1
    linarith [hnn b₂ t (by linarith)]
  -- S12: machine 1 clears buffer 1 again at t8
  have hx1t7 : T.x b₃ t7 = K := by
    have := xdiff hT b₃ (s := t4) (t := t7) (by linarith) (by linarith)
    rw [ex_in₃, ex_in₃, hx1t4] at this
    have hc := cap hT b₃ (s := t4) (t := t7) (a := t7) (by linarith) (by linarith) hτ₃
      (fun σ hσ hp => by
        obtain ⟨k, hk, hkp⟩ := (show T.ProcessingBuffer m₂ b₃ σ from hp)
        rcases k with _ | _ | _ | k
        · exact absurd (hβ01.symm.trans hk) (Ne.symm ex_b32)
        · have := hkp.2.2 hr2; linarith [hσ.1]
        · exact absurd (hβ2.symm.trans hk) (Ne.symm ex_b32)
        · have := procStart_mono hT hδ hkp.1 (show 3 ≤ k + 3 by omega)
          linarith [hkp.2.1])
    rw [max_eq_right (by linarith), zero_div] at hc
    linarith [hmono b₃ t4 t7 (by linarith) (by linarith)]
  obtain ⟨hlow8, hx1t8, -, -, -⟩ := clear_low (m := m₂) (bA := b₃) (k := 3) (r := 1) (c := t8) hT hC
    rfl hr3 hβ3 hp3 (by linarith) hτ₃ hx1t7 hK0 hi1
    (show (t8 - t7) * (1 / τ₃ - 1) = K by rw [hR8, ht7K])
    (fun u v _ _ _ => by rw [ex_in₃, ex_in₃]; ring)
  have hβ4 : T.RunExists m₂ 4 → T.β m₂ 4 = b₂ := fun h => other_buf' hT hC ex_only₂ h hβ3
  -- S13: machine 1 cannot leave buffer 1 before machine 2 leaves buffer 2
  have lemA : T.RunExists m₂ 4 → T.RunExists m₁ 2 ∧ T.s m₁ 2 < T.s m₂ 4 := by
    intro h4
    by_contra hneg
    have hle : T.RunExists m₁ 2 → T.s m₂ 4 ≤ T.s m₁ 2 := fun h2 => by
      by_contra hh; push Not at hh; exact hneg ⟨h2, hh⟩
    have hex := ((hC m₂ 3 hr3).2 h4).2.2
    rw [hβ4 h4] at hex
    have h8 := hlow8 h4
    have hpre : T.RunExists m₁ 2 → T.s m₂ 4 + δ₁ / 2 ≤ T.procStart m₁ 2 := fun h2 => by
      rw [hps2' h2]; linarith [hle h2]
    rcases hex with hx | hin
    · rw [hx4z (T.s m₂ 4) (by linarith) (fun h2 => by linarith [hpre h2])] at hx
      exact lt_irrefl _ hx
    · have := hin (T.s m₂ 4 + δ₁ / 2) (by linarith)
      rw [ex_in₂, ex_in₂, hy3c (T.s m₂ 4) (by linarith) (fun h2 => by linarith [hpre h2]),
        hy3c (T.s m₂ 4 + δ₁ / 2) (by linarith) hpre] at this
      exact lt_irrefl _ this
  -- S14: machine 2 keeps processing buffer 2 until t9
  have hx1z : ∀ t, t8 ≤ t → (T.RunExists m₂ 4 → t < T.s m₂ 4) → T.x b₃ t = 0 := by
    intro t h1 h2
    refine stays_zero' hT b₃ (p := t8) (r := 1) (by linarith) h1 hτ₃ zero_le_one hi1.le
      (fun u v _ _ _ => by rw [ex_in₃, ex_in₃]; linarith)
      (fun σ hσ => show T.ProcessingBuffer m₂ b₃ σ from
        ⟨3, hβ3, hr3, by rw [hp3]; linarith [hσ.1], fun h4 => lt_trans hσ.2 (h2 h4)⟩) hx1t8
  have lemB : T.RunExists m₁ 2 → t9 ≤ T.s m₁ 2 := by
    intro h2
    by_contra hlt; push Not at hlt
    have hL2 := hlowL h2
    have hex := ((hC m₁ 1 hr1').2 h2).1
    rw [hβ1'] at hex
    have hs0 : 0 ≤ T.s m₁ 2 := by linarith
    have hx1s : T.x b₃ (T.s m₁ 2) = 0 :=
      hx1z _ (by linarith) (fun h4 => (lemA h4).2)
    have h1 := hbal1 _ hs0
    have h2' := hbal2 _ hs0
    have h3 := hy2cap _ hs0
    rw [max_eq_left (by linarith)] at h3
    have := hg _ hlt
    linarith
  have hs4 : T.RunExists m₂ 4 → t9 ≤ T.s m₂ 4 := fun h4 =>
    le_trans (lemB (lemA h4).1) (lemA h4).2.le
  have hpt9 : T.RunExists m₁ 2 → t9 ≤ T.procStart m₁ 2 := fun h2 => by
    rw [hps2' h2]; linarith [lemB h2]
  -- S15: the state at t9
  have hy2t3 : T.y b₄ t3 = 0 := by
    have := hy2cap t3 (by linarith)
    rw [sub_self, max_self, zero_div] at this
    linarith [hmono b₄ 0 t3 le_rfl (by linarith), hy0 b₄]
  have hfull2 := tr_full hT b₄ (s := t3) (t := t9) (by linarith) (by linarith) (fun σ hσ => by
    refine ⟨show T.ProcessingBuffer m₁ b₄ σ from
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
  rw [hy2t3, ex_pt₄] at hfull2
  have ht90 : 0 ≤ t9 := by linarith
  have hx1t9 : T.x b₃ t9 = 0 := hx1z t9 (by linarith) (fun h4 =>
    lt_of_le_of_lt (lemB (lemA h4).1) (lemA h4).2)
  have hy3t9 : T.y b₁ t9 = δ₃ := hy3c t9 (by linarith) hpt9
  have hx4t9 : T.x b₂ t9 = 0 := hx4z t9 (by linarith) hpt9
  refine ⟨ex_casesM _ ?_ ?_ ?_ ?_, Or.inr ⟨3, hr3, hβ3, by rw [hs3]; linarith, hs4⟩,
    Or.inr ⟨1, hr1', hβ1', by rw [hs1']; linarith, lemB⟩,
    ⟨3, hr3, hβ3, by rw [hp3]; linarith, hs4⟩, ⟨1, hr1', hβ1', by rw [hp1']; linarith, lemB⟩⟩
  · show T.x b₃ t9 = 0; exact hx1t9
  · show T.x b₄ t9 = 0
    rw [hbal2 t9 ht90]
    have := hbal1 t9 ht90
    rw [hx1t9] at this
    linarith [hR9]
  · show T.x b₁ t9 = t9 - δ₃
    rw [hbal3 t9 ht90, hy3t9]
  · show T.x b₂ t9 = 0; exact hx4t9

end KS2
end KumarSeidman.TwoType


namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory Filter

namespace KS2
variable {S : KumarSeidman.TwoType.System}

/-- The schedule seen from time `t0` on, with the runs of machine `m` re-indexed from `off m`. -/
noncomputable def shiftS (T : S.Schedule) (t0 : ℝ) (off : Fin S.M → ℕ) : S.Schedule where
  x b t := T.x b (t0 + t)
  y b t := T.y b (t0 + t) - T.y b t0
  nruns m := T.nruns m - (off m : ℕ∞)
  β m i := T.β m (off m + i)
  s m i := if i = 0 then 0 else T.s m (off m + i) - t0

theorem enat_shift (n : ℕ∞) (o i : ℕ) :
    (i : ℕ∞) < n - (o : ℕ∞) ↔ ((o + i : ℕ) : ℕ∞) < n := by
  induction n using ENat.recTopCoe with
  | top => simp [ENat.top_sub_natCast]
  | coe N =>
    rw [← ENat.natCast_sub]
    simp only [Nat.cast_lt]
    omega

theorem tr_traj_tendsto {T : S.Schedule} (hT : T.IsTrajectory) (m : Fin S.M) (hm : T.nruns m = ⊤) :
    Tendsto (T.s m) atTop atTop := hT.2.2.2.2.2.2.2.1 m hm

variable {T : S.Schedule} {t0 : ℝ} {off : Fin S.M → ℕ}

theorem shift_run (m : Fin S.M) (i : ℕ) :
    (shiftS T t0 off).RunExists m i ↔ T.RunExists m (off m + i) := by
  unfold RunExists; exact enat_shift _ _ _

theorem shift_s_succ (m : Fin S.M) (i : ℕ) :
    (shiftS T t0 off).s m (i + 1) = T.s m (off m + (i + 1)) - t0 := by
  simp [shiftS]

theorem shift_procStart_succ (m : Fin S.M) (i : ℕ) :
    (shiftS T t0 off).procStart m (i + 1) = T.procStart m (off m + (i + 1)) - t0 := by
  show (shiftS T t0 off).s m (i + 1) + S.δ (T.β m (off m + i)) (T.β m (off m + (i + 1))) = _
  rw [shift_s_succ]
  show _ = T.s m (off m + i + 1) + S.δ (T.β m (off m + i)) (T.β m (off m + i + 1)) - t0
  ring

theorem shift_procStart_zero (m : Fin S.M) : (shiftS T t0 off).procStart m 0 = 0 := by
  show (shiftS T t0 off).s m 0 = 0
  simp [shiftS]

theorem shift_inflow (b : S.Buffer) (t : ℝ) :
    S.inflow (shiftS T t0 off).y b t = S.inflow T.y b (t0 + t) - S.inflow T.y b t0 := by
  unfold System.inflow
  split_ifs
  · ring
  · rfl

/-- Hypotheses making the shift legitimate: `t0 ≥ 0` lies in the processing phase of run `off m`
of every machine `m`. -/
structure ShiftOK (T : S.Schedule) (t0 : ℝ) (off : Fin S.M → ℕ) : Prop where
  t0nn : 0 ≤ t0
  run : ∀ m, T.RunExists m (off m)
  pst : ∀ m, T.procStart m (off m) ≤ t0
  nxt : ∀ m, T.RunExists m (off m + 1) → t0 ≤ T.s m (off m + 1)

theorem shift_inproc (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') (hok : ShiftOK T t0 off)
    (m : Fin S.M) (i : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (shiftS T t0 off).InProcessing m i σ ↔ T.InProcessing m (off m + i) (t0 + σ) := by
  unfold InProcessing
  rw [shift_run, shift_run]
  rcases i with _ | i
  · rw [shift_procStart_zero, shift_s_succ]
    simp only [add_zero]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, by linarith [hok.pst m], fun h => by have := h3 h; linarith⟩
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, hσ, fun h => by have := h3 h; simp only [zero_add] at this ⊢; linarith⟩
  · rw [shift_procStart_succ, shift_s_succ]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, fun h => by have := h3 (by rw [← add_assoc]; exact h); rw [← add_assoc] at this; linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, fun h => by rw [← add_assoc] at h; have := h3 h; rw [← add_assoc]; linarith⟩

theorem shift_proc (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') (hok : ShiftOK T t0 off)
    (m : Fin S.M) (b : S.Buffer) {σ : ℝ} (hσ : 0 ≤ σ) :
    (shiftS T t0 off).ProcessingBuffer m b σ ↔ T.ProcessingBuffer m b (t0 + σ) := by
  constructor
  · rintro ⟨i, hi, hp⟩
    exact ⟨off m + i, hi, (shift_inproc hT hδ hok m i hσ).1 hp⟩
  · rintro ⟨k, hk, hp⟩
    have hge : off m ≤ k := idx_ge hT hδ hp (hok.run m)
      (le_trans (s_le_procStart hδ m (off m)) (by linarith [hok.pst m]))
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hge
    exact ⟨i, hk, (shift_inproc hT hδ hok m i hσ).2 hp⟩

theorem shift_traj (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') (hok : ShiftOK T t0 off) :
    (shiftS T t0 off).IsTrajectory := by
  have h0 := hok.t0nn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b; simp [shiftS]
  · intro b u hu v hv huv
    simp only [shiftS]
    have := tr_mono hT b (s := t0 + u) (t := t0 + v) (by simp at hu; linarith) (by linarith)
    linarith
  · intro b t ht
    rw [shift_inflow]
    simp only [shiftS, add_zero]
    have h1 := tr_bal hT b (t := t0 + t) (by linarith)
    have h2 := tr_bal hT b (t := t0) h0
    linarith
  · intro b t ht; exact tr_nonneg hT b (show 0 ≤ t0 + t by linarith)
  · intro m
    refine ⟨(shift_run m 0).2 (by simpa using hok.run m), by simp [shiftS]⟩
  · intro m i h
    exact tr_mach hT ((shift_run m i).1 h)
  · intro m i h
    rcases i with _ | i
    · rw [shift_procStart_zero, show (0 + 1 : ℕ) = 1 from rfl, shift_s_succ]
      have := hok.nxt m (by have := (shift_run m 1).1 h; simpa using this)
      simp only [zero_add]; linarith
    · rw [shift_procStart_succ, shift_s_succ]
      have hr : T.RunExists m (off m + i + 1 + 1) := by
        have := (shift_run m (i + 1 + 1)).1 h
        rwa [show off m + (i + 1 + 1) = off m + i + 1 + 1 by omega] at this
      have := tr_setup hT hr
      rw [show off m + (i + 1 + 1) = off m + i + 1 + 1 by omega,
        show off m + (i + 1) = off m + i + 1 by omega]
      linarith
  · intro m hm
    have hm' : T.nruns m = ⊤ := by
      by_contra hne
      obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.1 hne
      have : (shiftS T t0 off).nruns m = ((N - off m : ℕ) : ℕ∞) := by
        show T.nruns m - _ = _; rw [← hN, ENat.natCast_sub]; rfl
      rw [this] at hm; exact ENat.natCast_ne_top _ hm
    have h1 := (tr_traj_tendsto hT m hm')
    have h2 : Tendsto (fun i => T.s m (i + off m) + -t0) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-t0) (h1.comp (tendsto_add_atTop_nat (off m)))
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
    rw [shift_s_succ, add_comm (j + 1) (off m)]; ring
  · intro b u v hu huv
    have e : {σ | σ ∈ Set.Icc u v ∧ (shiftS T t0 off).ProcessingBuffer (S.mach b) b σ} =
        (fun σ => σ + t0) ⁻¹' {σ | σ ∈ Set.Icc (t0 + u) (t0 + v) ∧
          T.ProcessingBuffer (S.mach b) b σ} := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [add_comm]; exact (shift_proc hT hδ hok _ b (by linarith)).1 h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [add_comm] at h3; exact (shift_proc hT hδ hok _ b (by linarith)).2 h3
    rw [e, measure_preimage_add_right]
    simp only [shiftS]
    have := tr_cap hT b (s := t0 + u) (t := t0 + v) (by linarith) (by linarith)
    linarith
  · intro b u v hu huv hall
    simp only [shiftS]
    have := tr_full hT b (s := t0 + u) (t := t0 + v) (by linarith) (by linarith) (fun σ hσ => by
      have hσ' : σ - t0 ∈ Set.Ico u v := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
      obtain ⟨h1, h2⟩ := hall _ hσ'
      have h1' := (shift_proc hT hδ hok _ b (by linarith [hσ'.1])).1 h1
      simp only [add_sub_cancel] at h1'
      refine ⟨h1', ?_⟩
      have : (shiftS T t0 off).x b (σ - t0) = T.x b σ := by simp [shiftS]
      rw [this] at h2; exact h2)
    rw [show t0 + v - (t0 + u) = v - u by ring] at this
    linarith

theorem shift_dem_to {b : S.Buffer} {t : ℝ} (h : (shiftS T t0 off).Demanding b t) :
    T.Demanding b (t0 + t) := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr (fun σ hσ => ?_)
    have := h (σ - t0) (by linarith)
    rw [shift_inflow, shift_inflow, add_sub_cancel] at this
    linarith

theorem shift_dem_from {b : S.Buffer} {t : ℝ} (h : T.Demanding b (t0 + t)) :
    (shiftS T t0 off).Demanding b t := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr (fun σ hσ => ?_)
    have := h (t0 + σ) (by linarith)
    rw [shift_inflow, shift_inflow]
    linarith

theorem shift_clear (hT : T.IsTrajectory) (hδ : ∀ b b', 0 ≤ S.δ b b') (hok : ShiftOK T t0 off)
    (hC : T.IsClearing) : (shiftS T t0 off).IsClearing := by
  intro m i hi
  have hk : T.RunExists m (off m + i) := (shift_run m i).1 hi
  have hnext : T.RunExists m (off m + i + 1) → (shiftS T t0 off).RunExists m (i + 1) :=
    fun h => (shift_run m (i + 1)).2 h
  refine ⟨fun t ht hlt => ?_, fun h1 => ?_⟩
  · rintro ⟨hx, b', hb'm, hb'ne, hdem⟩
    refine (hC m (off m + i) hk).1 (t0 + t) ?_ ?_ ⟨hx, b', hb'm, hb'ne, shift_dem_to hdem⟩
    · rcases i with _ | j
      · rw [shift_procStart_zero] at ht; show T.procStart m (off m) < t0 + t; linarith [hok.pst m]
      · rw [shift_procStart_succ] at ht; linarith
    · intro h
      have := hlt (hnext h)
      rw [shift_s_succ, ← add_assoc] at this
      linarith
  · have h1' : T.RunExists m (off m + i + 1) := (shift_run m (i + 1)).1 h1
    obtain ⟨hx, hne, hdem⟩ := (hC m (off m + i) hk).2 h1'
    have e : t0 + (shiftS T t0 off).s m (i + 1) = T.s m (off m + i + 1) := by
      rw [shift_s_succ]; ring
    refine ⟨?_, hne, ?_⟩
    · show T.x _ (t0 + _) = 0; rw [e]; exact hx
    · apply shift_dem_from; rw [e]; exact hdem

theorem shift_x (b : S.Buffer) (t : ℝ) : (shiftS T t0 off).x b t = T.x b (t0 + t) := rfl
theorem shift_β (m : Fin S.M) (i : ℕ) : (shiftS T t0 off).β m i = T.β m (off m + i) := rfl

end KS2
end KumarSeidman.TwoType


namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory

namespace KS2

section ShiftBack
variable {S : KumarSeidman.TwoType.System} {T : S.Schedule} {t0 : ℝ} {off : Fin S.M → ℕ}

theorem shift_setupFor (hδ : ∀ b b', 0 ≤ S.δ b b') (hok : ShiftOK T t0 off) {m : Fin S.M}
    {b : S.Buffer} {t : ℝ} (ht : 0 < t) (h : (shiftS T t0 off).SetupFor m t b) :
    T.SetupFor m (t0 + t) b := by
  rcases h with ⟨h0, _⟩ | ⟨i, hi, hb, hs, hn⟩
  · linarith
  · refine Or.inr ⟨off m + i, (shift_run m i).1 hi, hb, ?_, fun h1 => ?_⟩
    · rcases i with _ | j
      · have h1 := s_le_procStart (T := T) hδ m (off m)
        have h2 := hok.pst m
        show T.s m (off m) < t0 + t
        linarith
      · rw [shift_s_succ] at hs; linarith
    · have := hn ((shift_run m (i + 1)).2 h1)
      rw [shift_s_succ, ← add_assoc] at this
      linarith

theorem shift_phase (hok : ShiftOK T t0 off) {m : Fin S.M} {b : S.Buffer} {t : ℝ}
    (h : ∃ k, (shiftS T t0 off).RunExists m k ∧ (shiftS T t0 off).β m k = b ∧
      (shiftS T t0 off).procStart m k ≤ t ∧
      ((shiftS T t0 off).RunExists m (k + 1) → t ≤ (shiftS T t0 off).s m (k + 1))) (ht : 0 ≤ t) :
    ∃ k, T.RunExists m k ∧ T.β m k = b ∧ T.procStart m k ≤ t0 + t ∧
      (T.RunExists m (k + 1) → t0 + t ≤ T.s m (k + 1)) := by
  obtain ⟨i, hi, hb, hp, hn⟩ := h
  refine ⟨off m + i, (shift_run m i).1 hi, hb, ?_, fun h1 => ?_⟩
  · rcases i with _ | j
    · have := hok.pst m; show T.procStart m (off m) ≤ t0 + t; linarith
    · rw [shift_procStart_succ] at hp; linarith
  · have := hn ((shift_run m (i + 1)).2 h1)
    rw [shift_s_succ, ← add_assoc] at this
    linarith

end ShiftBack

section Ex2
variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}

theorem ex_mcases (P : Fin (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).M → Prop) (h1 : P m₁) (h2 : P m₂) :
    ∀ m, P m := by
  intro m
  fin_cases m
  exacts [h1, h2]

/-- Shifting a clearing trajectory of Example 2 to a time `t0` at which machine 1 is in the
processing phase of run `k1` and machine 2 in that of run `k2`. -/
theorem ex_shift_ok {T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule} {t0 : ℝ} (ht0 : 0 ≤ t0)
    {c₁ c₂ : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Buffer}
    (h1 : ∃ k, T.RunExists m₁ k ∧ T.β m₁ k = c₁ ∧ T.procStart m₁ k ≤ t0 ∧
        (T.RunExists m₁ (k + 1) → t0 ≤ T.s m₁ (k + 1)))
    (h2 : ∃ k, T.RunExists m₂ k ∧ T.β m₂ k = c₂ ∧ T.procStart m₂ k ≤ t0 ∧
        (T.RunExists m₂ (k + 1) → t0 ≤ T.s m₂ (k + 1))) :
    ∃ off : Fin (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).M → ℕ, ShiftOK T t0 off ∧
      ∀ m, (shiftS T t0 off).β m 0 = setups c₁ c₂ m := by
  obtain ⟨k1, hr1, hb1, hp1, hn1⟩ := h1
  obtain ⟨k2, hr2, hb2, hp2, hn2⟩ := h2
  refine ⟨![k1, k2], ⟨ht0, ex_mcases _ hr1 hr2, ex_mcases _ hp1 hp2, ex_mcases _ hn1 hn2⟩,
    ex_mcases _ hb1 hb2⟩

end Ex2

theorem t9_mul {τ ξ d t9 : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (ht9 : t9 = (ξ + τ⁻¹ * d) / (τ⁻¹ - 1)) :
    t9 * (1 - τ) = ξ * τ + d := by
  have h1 : τ⁻¹ - 1 = (1 - τ) / τ := by field_simp
  have h2 : 1 - τ ≠ 0 := by linarith
  rw [ht9, h1]
  field_simp

set_option maxHeartbeats 4000000 in
theorem cycle_traj (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) (ξ : ℝ)
    (hξA : δ₁ + (δ₄ + τ₄ * δ₁ + δ₁) + 1 ≤ (τ₂ - τ₁) * ξ)
    (hξB : δ₃ + (δ₂ + τ₂ * δ₃ + δ₃) + 1 ≤
      (τ₄ - τ₃) * ((ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1) - δ₁))
    (T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule)
    (hcl : T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃)) :
    let t₉ := (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1)
    let u := (t₉ - δ₁ + τ₄⁻¹ * (δ₃ + δ₄)) / (τ₄⁻¹ - 1)
    (∀ b, T.x b (t₉ + u) = levels (u - δ₃) 0 0 0 b) ∧ T.SetupFor m₁ (t₉ + u) b₄ ∧
      T.SetupFor m₂ (t₉ + u) b₃ ∧
      (∃ k, T.RunExists m₁ k ∧ T.β m₁ k = b₄ ∧ T.procStart m₁ k ≤ t₉ + u ∧
        (T.RunExists m₁ (k + 1) → t₉ + u ≤ T.s m₁ (k + 1))) ∧
      (∃ k, T.RunExists m₂ k ∧ T.β m₂ k = b₃ ∧ T.procStart m₂ k ≤ t₉ + u ∧
        (T.RunExists m₂ (k + 1) → t₉ + u ≤ T.s m₂ (k + 1))) ∧ 0 < t₉ + u := by
  intro t9 u
  obtain ⟨hT, hst, hC⟩ := hcl
  have hδ := ex_hδ (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) hδ₁ hδ₂ hδ₃ hδ₄
  have h8 := stage8_traj τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄ hδ₁ hδ₂ hδ₃ hδ₄ h7 h1₁ h1₂ ξ hξA T
    ⟨hT, hst, hC⟩
  obtain ⟨hlev, -, -, hph1, hph2⟩ := h8
  have hτ34 : 0 < τ₄ - τ₃ := by linarith
  have hB : δ₃ + (δ₂ + τ₂ * δ₃ + δ₃) + 1 ≤ (τ₄ - τ₃) * (t9 - δ₁) := hξB
  have hξ' : 0 < t9 - δ₁ := pos_of_mul_pos_right (by linarith [mul_pos hτ₂ hδ₃]) hτ34.le
  have ht9nn : 0 ≤ t9 := by linarith
  obtain ⟨off, hok, hβ'⟩ := ex_shift_ok (t0 := t9) ht9nn hph1 hph2
  have hT' := shift_traj hT hδ hok
  have hC' := shift_clear hT hδ hok hC
  have hstart : (shiftS T t9 off).StartsAt (levels 0 0 (t9 - δ₁) 0) (setups b₁ b₂) :=
    ⟨fun b => by rw [shift_x, add_zero]; exact hlev b, hβ'⟩
  have hm := stage8_trajM τ₃ τ₄ τ₁ τ₂ δ₃ δ₄ δ₁ δ₂ hτ₃ hτ₄ hτ₁ hτ₂ hδ₃ hδ₄ hδ₁ hδ₂ (by linarith)
    (by linarith) (by linarith) (t9 - δ₁) hξB (shiftS T t9 off) ⟨hT', hstart, hC'⟩
  obtain ⟨hlev', hsu2, hsu1, hph2', hph1'⟩ := hm
  have hτ4 : τ₄ < 1 := by linarith
  have hu : 0 < u := by
    have hm4 := t9_mul (τ := τ₄) (ξ := t9 - δ₁) (d := δ₃ + δ₄) (t9 := u) hτ₄ hτ4 rfl
    have : 0 < u * (1 - τ₄) := by rw [hm4]; positivity
    exact pos_of_mul_pos_left this (by linarith)
  refine ⟨fun b => hlev' b, shift_setupFor hδ hok hu hsu1, shift_setupFor hδ hok hu hsu2,
    shift_phase hok hph1' hu.le, shift_phase hok hph2' hu.le, by linarith⟩

end KS2
end KumarSeidman.TwoType


namespace KumarSeidman.TwoType
open Example2 KumarSeidman.TwoType.System KumarSeidman.TwoType.System.Schedule MeasureTheory

namespace KS2

theorem fc_arith (ξ τ₂ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ) (hτ₂ : 0 < τ₂) (hτ2 : τ₂ < 1) (hτ₄ : 0 < τ₄)
    (hτ4 : τ₄ < 1) :
    ((ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1) - δ₁ + τ₄⁻¹ * (δ₃ + δ₄)) / (τ₄⁻¹ - 1) - δ₃ =
      τ₂ * τ₄ / ((1 - τ₂) * (1 - τ₄)) * ξ +
        (((δ₁ + δ₂) / (1 - τ₂) - δ₁ + (1 / τ₄) * (δ₃ + δ₄)) * ((1 / τ₄) - 1)⁻¹ - δ₃) := by
  have h2 : 1 - τ₂ ≠ 0 := by linarith
  have h4 : 1 - τ₄ ≠ 0 := by linarith
  rw [show τ₂⁻¹ - 1 = (1 - τ₂) / τ₂ by field_simp, show τ₄⁻¹ - 1 = (1 - τ₄) / τ₄ by field_simp,
    show (1 / τ₄) - 1 = (1 - τ₄) / τ₄ by field_simp]
  field_simp
  ring

/-- The two thresholds of the full cycle hold for every `ξ ≥ max A (B/τ₂)`. -/
theorem fc_thresh (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ ξ : ℝ)
    (hτ₂ : 0 < τ₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (h12 : τ₁ < τ₂) (h34 : τ₃ < τ₄) (hτ2 : τ₂ < 1)
    (hξ : max ((δ₁ + (δ₄ + τ₄ * δ₁ + δ₁) + 1) / (τ₂ - τ₁))
      ((δ₃ + (δ₂ + τ₂ * δ₃ + δ₃) + 1) / (τ₄ - τ₃) / τ₂) ≤ ξ) :
    δ₁ + (δ₄ + τ₄ * δ₁ + δ₁) + 1 ≤ (τ₂ - τ₁) * ξ ∧
    δ₃ + (δ₂ + τ₂ * δ₃ + δ₃) + 1 ≤ (τ₄ - τ₃) * ((ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1) - δ₁) := by
  have hτ12 : 0 < τ₂ - τ₁ := by linarith
  have hτ34 : 0 < τ₄ - τ₃ := by linarith
  have hA := (div_le_iff₀ hτ12).mp (le_trans (le_max_left _ _) hξ)
  have hB := (div_le_iff₀ hτ₂).mp (le_trans (le_max_right _ _) hξ)
  have hBpos : 0 < (δ₃ + (δ₂ + τ₂ * δ₃ + δ₃) + 1) / (τ₄ - τ₃) := by
    have := mul_pos hτ₂ hδ₃; positivity
  have hξ0 : 0 ≤ ξ := by nlinarith
  have hm := t9_mul (τ := τ₂) (ξ := ξ) (d := δ₁ + δ₂)
    (t9 := (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1)) hτ₂ hτ2 rfl
  have hge : τ₂ * ξ ≤ (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1) - δ₁ := by
    have h1 : 0 ≤ ((ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1) - δ₁ - τ₂ * ξ) * (1 - τ₂) := by
      have e : ((ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1) - δ₁ - τ₂ * ξ) * (1 - τ₂) =
          δ₂ + δ₁ * τ₂ + τ₂ ^ 2 * ξ := by linear_combination hm
      rw [e]; positivity
    have := nonneg_of_mul_nonneg_left h1 (by linarith)
    linarith
  refine ⟨by linarith, ?_⟩
  have h0 : (δ₃ + (δ₂ + τ₂ * δ₃ + δ₃) + 1) / (τ₄ - τ₃) ≤
      (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1) - δ₁ := by linarith
  have h1 := (div_le_iff₀ hτ34).mp h0
  linarith

section Ex2
variable {τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ}

/-- Levels grow at most linearly: `x_b(t) ≤ x_b(0) + t (1 + 1/τ₁ + 1/τ₃)`. -/
theorem ex_inc_bound (hτ₁ : 0 < τ₁) (hτ₃ : 0 < τ₃)
    {T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule} (hT : T.IsTrajectory) {t : ℝ} (ht : 0 ≤ t) :
    ∀ b, T.x b t ≤ T.x b 0 + t * (1 + 1 / τ₁ + 1 / τ₃) := by
  have h1 : 0 ≤ t * (1 / τ₁) := by positivity
  have h3 : 0 ≤ t * (1 / τ₃) := by positivity
  have hR : t * (1 + 1 / τ₁ + 1 / τ₃) = t + t * (1 / τ₁) + t * (1 / τ₃) := by ring
  refine ex_cases _ ?_ ?_ ?_ ?_
  · have := xdiff hT b₁ (s := 0) (t := t) le_rfl ht
    rw [ex_in₁, ex_in₁] at this
    have := tr_mono hT b₁ le_rfl ht
    linarith
  · have := xdiff hT b₂ (s := 0) (t := t) le_rfl ht
    rw [ex_in₂, ex_in₂] at this
    have := tr_mono hT b₂ le_rfl ht
    have hc := cap_rate hT b₁ le_rfl ht hτ₁
    rw [ex_pt₁, sub_zero, div_eq_mul_one_div] at hc
    linarith
  · have := xdiff hT b₃ (s := 0) (t := t) le_rfl ht
    rw [ex_in₃, ex_in₃] at this
    have := tr_mono hT b₃ le_rfl ht
    linarith
  · have := xdiff hT b₄ (s := 0) (t := t) le_rfl ht
    rw [ex_in₄, ex_in₄] at this
    have := tr_mono hT b₄ le_rfl ht
    have hc := cap_rate hT b₃ le_rfl ht hτ₃
    rw [ex_pt₃, sub_zero, div_eq_mul_one_div] at hc
    linarith

end Ex2

theorem stable_bounded (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h8 : (δ₁ + δ₄) / (1 - τ₁ - τ₄) = (δ₂ + δ₃) / (1 - τ₂ - τ₃))
    (h9 : δ₄ < (1 - τ₃ - τ₄) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h10 : δ₂ < (1 - τ₁ - τ₂) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1)
    (T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule)
    (hcl : T.IsClearingFrom (levels 0 ((δ₁ + δ₄) / (1 - τ₁ - τ₄)) 0 ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
      (setups b₁ b₃)) : T.IsBounded := by
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (δ₁ + δ₄) / (1 - τ₁ - τ₄) := ⟨_, rfl⟩
  rw [← hη] at hcl
  have hδ := ex_hδ (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) hδ₁ hδ₂ hδ₃ hδ₄
  have hη0 : 0 < η := by rw [hη]; exact div_pos (by linarith) (by linarith)
  obtain ⟨hT, hst, hC⟩ := hcl
  have hlevη : ∀ b, levels (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) (δ₁ := δ₁) (δ₂ := δ₂)
      (δ₃ := δ₃) (δ₄ := δ₄) 0 η 0 η b ≤ η :=
    ex_cases _ hη0.le le_rfl hη0.le le_rfl
  have P : ∀ n : ℕ, (∀ b, T.x b (n * η) = levels 0 η 0 η b) ∧
      (∃ k, T.RunExists m₁ k ∧ T.β m₁ k = b₁ ∧ T.procStart m₁ k ≤ n * η ∧
        (T.RunExists m₁ (k + 1) → n * η ≤ T.s m₁ (k + 1))) ∧
      (∃ k, T.RunExists m₂ k ∧ T.β m₂ k = b₃ ∧ T.procStart m₂ k ≤ n * η ∧
        (T.RunExists m₂ (k + 1) → n * η ≤ T.s m₂ (k + 1))) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      have hs := fun m k (h : T.RunExists m (k + 1)) => by
        have := s_mono hT hδ h (Nat.zero_le (k + 1))
        rw [(tr_run0 hT m).2] at this; exact this
      refine ⟨hst.1, ⟨0, (tr_run0 hT m₁).1, hst.2 m₁, le_of_eq (tr_run0 hT m₁).2, hs m₁ 0⟩,
        ⟨0, (tr_run0 hT m₂).1, hst.2 m₂, le_of_eq (tr_run0 hT m₂).2, hs m₂ 0⟩⟩
    | succ n ih =>
      have hn0 : 0 ≤ (n : ℝ) * η := by positivity
      obtain ⟨off, hok, hβ'⟩ := ex_shift_ok hn0 ih.2.1 ih.2.2
      have hT' := shift_traj hT hδ hok
      have hC' := shift_clear hT hδ hok hC
      have hstart : (shiftS T (n * η) off).StartsAt (levels 0 η 0 η) (setups b₁ b₃) :=
        ⟨fun b => by rw [shift_x, add_zero]; exact ih.1 b, hβ'⟩
      have hc := case1_traj τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄ hδ₁ hδ₂ hδ₃ hδ₄ h8 h9 h10 h1₁
        h1₂ (shiftS T (n * η) off) (by rw [← hη]; exact ⟨hT', hstart, hC'⟩)
      rw [← hη] at hc
      obtain ⟨hlev, -, -, hp1, hp2⟩ := hc
      have e : ((n + 1 : ℕ) : ℝ) * η = n * η + η := by push_cast; ring
      rw [e]
      exact ⟨fun b => hlev b, shift_phase hok hp1 hη0.le, shift_phase hok hp2 hη0.le⟩
  intro b
  refine ⟨η + η * (1 + 1 / τ₁ + 1 / τ₃), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have ht0 : (0 : ℝ) ≤ t := ht
  set n := ⌊t / η⌋₊ with hn
  have hn1 : (n : ℝ) * η ≤ t := by
    have := Nat.floor_le (div_nonneg ht0 hη0.le)
    rw [← hn] at this
    calc (n : ℝ) * η ≤ t / η * η := mul_le_mul_of_nonneg_right this hη0.le
      _ = t := by field_simp
  have hn2 : t < (n : ℝ) * η + η := by
    have := Nat.lt_floor_add_one (t / η)
    rw [← hn] at this
    have : t / η * η < ((n : ℝ) + 1) * η := mul_lt_mul_of_pos_right this hη0
    rw [div_mul_cancel₀ _ hη0.ne'] at this
    linarith
  have hn0 : 0 ≤ (n : ℝ) * η := by positivity
  obtain ⟨off, hok, -⟩ := ex_shift_ok hn0 (P n).2.1 (P n).2.2
  have hT' := shift_traj hT hδ hok
  have hb := ex_inc_bound hτ₁ hτ₃ hT' (t := t - n * η) (by linarith) b
  rw [shift_x, shift_x, add_zero, add_sub_cancel, (P n).1 b] at hb
  have h1 := hlevη b
  have h2 : (t - n * η) * (1 + 1 / τ₁ + 1 / τ₃) ≤ η * (1 + 1 / τ₁ + 1 / τ₃) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  show T.x b t ≤ _
  linarith

theorem unstable_unbounded (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    ∃ ξ₀ : ℝ, ∀ ξ ≥ ξ₀, ∀ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃) → ¬ BddAbove (T.x b₁ '' Set.Ici 0) := by
  have hτ2 : τ₂ < 1 := by linarith
  have hτ4 : τ₄ < 1 := by linarith
  have h12 : τ₁ < τ₂ := by linarith
  have h34 : τ₃ < τ₄ := by linarith
  have hδ := ex_hδ (τ₁ := τ₁) (τ₂ := τ₂) (τ₃ := τ₃) (τ₄ := τ₄) hδ₁ hδ₂ hδ₃ hδ₄
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = τ₂ * τ₄ / ((1 - τ₂) * (1 - τ₄)) := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ a : ℝ,
      a = ((δ₁ + δ₂) / (1 - τ₂) - δ₁ + (1 / τ₄) * (δ₃ + δ₄)) * ((1 / τ₄) - 1)⁻¹ - δ₃ := ⟨_, rfl⟩
  have hlam1 : 1 < lam := by
    rw [hlam, one_lt_div (by apply mul_pos <;> linarith)]
    nlinarith
  set ξA := max ((δ₁ + (δ₄ + τ₄ * δ₁ + δ₁) + 1) / (τ₂ - τ₁))
      ((δ₃ + (δ₂ + τ₂ * δ₃ + δ₃) + 1) / (τ₄ - τ₃) / τ₂) with hξA
  refine ⟨max ξA ((1 - α) / (lam - 1)), fun ξ hξ T hcl => ?_⟩
  have hgrow : ∀ ζ, ξ ≤ ζ → ζ + 1 ≤ lam * ζ + α := by
    intro ζ hζ
    have h1 : (1 - α) / (lam - 1) ≤ ζ := le_trans (le_trans (le_max_right _ _) hξ) hζ
    have := (div_le_iff₀ (by linarith : 0 < lam - 1)).mp h1
    nlinarith
  have Q : ∀ n : ℕ, ∃ t : ℝ, 0 ≤ t ∧ ∃ ζ : ℝ, ξ + n ≤ ζ ∧
      (∀ b, T.x b t = levels ζ 0 0 0 b) ∧
      (∃ k, T.RunExists m₁ k ∧ T.β m₁ k = b₄ ∧ T.procStart m₁ k ≤ t ∧
        (T.RunExists m₁ (k + 1) → t ≤ T.s m₁ (k + 1))) ∧
      (∃ k, T.RunExists m₂ k ∧ T.β m₂ k = b₃ ∧ T.procStart m₂ k ≤ t ∧
        (T.RunExists m₂ (k + 1) → t ≤ T.s m₂ (k + 1))) := by
    obtain ⟨hT, hst, hC⟩ := hcl
    intro n
    induction n with
    | zero =>
      have hs := fun m k (h : T.RunExists m (k + 1)) => by
        have := s_mono hT hδ h (Nat.zero_le (k + 1))
        rw [(tr_run0 hT m).2] at this; exact this
      refine ⟨0, le_rfl, ξ, by simp, hst.1,
        ⟨0, (tr_run0 hT m₁).1, hst.2 m₁, le_of_eq (tr_run0 hT m₁).2, hs m₁ 0⟩,
        ⟨0, (tr_run0 hT m₂).1, hst.2 m₂, le_of_eq (tr_run0 hT m₂).2, hs m₂ 0⟩⟩
    | succ n ih =>
      obtain ⟨t, ht, ζ, hζ, hlev, hp1, hp2⟩ := ih
      obtain ⟨off, hok, hβ'⟩ := ex_shift_ok ht hp1 hp2
      have hT' := shift_traj hT hδ hok
      have hC' := shift_clear hT hδ hok hC
      have hstart : (shiftS T t off).StartsAt (levels ζ 0 0 0) (setups b₄ b₃) :=
        ⟨fun b => by rw [shift_x, add_zero]; exact hlev b, hβ'⟩
      have hζA : ξA ≤ ζ := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith [le_trans (le_max_left _ _) hξ]
      obtain ⟨hA, hB⟩ := fc_thresh τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ ζ hτ₂ hδ₁ hδ₂ hδ₃ h12 h34 hτ2 hζA
      obtain ⟨hlev', -, -, hq1, hq2, hpos⟩ := cycle_traj τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄
        hδ₁ hδ₂ hδ₃ hδ₄ h7 h1₁ h1₂ ζ hA hB (shiftS T t off) ⟨hT', hstart, hC'⟩
      have hval := fc_arith ζ τ₂ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₂ hτ2 hτ₄ hτ4
      rw [← hlam, ← hα] at hval
      refine ⟨t + _, by linarith, _, ?_, fun b => (hlev' b).trans (by rw [hval]),
        shift_phase hok hq1 hpos.le, shift_phase hok hq2 hpos.le⟩
      have := hgrow ζ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      push_cast
      linarith
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (M - ξ)
  obtain ⟨t, ht, ζ, hζ, hlev, -⟩ := Q n
  have := hM ⟨t, ht, rfl⟩
  rw [hlev b₁] at this
  change ζ ≤ M at this
  linarith

end KS2
end KumarSeidman.TwoType


open KumarSeidman.TwoType KumarSeidman.TwoType.Example2 KumarSeidman.TwoType.KS2 in
theorem solution (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1)
    (h8 : (δ₁ + δ₄) / (1 - τ₁ - τ₄) = (δ₂ + δ₃) / (1 - τ₂ - τ₃))
    (h9 : δ₄ < (1 - τ₃ - τ₄) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h10 : δ₂ < (1 - τ₁ - τ₂) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    let η := (δ₁ + δ₄) / (1 - τ₁ - τ₄)
    ((∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
        T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃)) ∧
      ∀ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
        T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃) → T.IsBounded) ∧
    ∃ ξ₀ : ℝ, ∀ ξ ≥ ξ₀,
      (∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
          T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃)) ∧
        ∀ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
          T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃) →
            ¬ BddAbove (T.x b₁ '' Set.Ici 0) := by
  intro η
  refine ⟨⟨example2_periodic_trajectory_exists τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄
      hδ₁ hδ₂ hδ₃ hδ₄ h8 h9 h10 h1₁ h1₂,
    fun T hT => stable_bounded τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄ hδ₁ hδ₂ hδ₃ hδ₄ h8 h9 h10
      h1₁ h1₂ T hT⟩, ?_⟩
  obtain ⟨ξ₁, hξ₁⟩ := example2_unstable_trajectory_exists τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄
    hδ₁ hδ₂ hδ₃ hδ₄ h7 h1₁ h1₂
  obtain ⟨ξ₂, hξ₂⟩ := unstable_unbounded τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ hτ₁ hτ₂ hτ₃ hτ₄ hδ₁ hδ₂ hδ₃ hδ₄
    h7 h1₁ h1₂
  exact ⟨max ξ₁ ξ₂, fun ξ hξ => ⟨hξ₁ ξ (le_trans (le_max_left _ _) hξ),
    hξ₂ ξ (le_trans (le_max_right _ _) hξ)⟩⟩
