-- Prove2me | solution 1 for KumarSeidman.Reentrant.case2_magnification
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:51:03.37885+00:00
-- url     : https://prove2.me/submissions/3f8def3f-dbd4-4e5f-b500-8f84c5e331c7

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1

namespace KSR
open KumarSeidman.Reentrant MeasureTheory

/-! ### Abstract fluid-buffer lemmas -/

/-- Fill: a buffer served at rate `r` with inflow rate `ρ > r` grows linearly. -/
theorem abs_fill {X Y : ℝ → ℝ} {a b ρ r : ℝ} (hr : r < ρ)
    (h1 : ∀ s t, a ≤ s → s ≤ t → t ≤ b → X t = X s + ρ * (t - s) - (Y t - Y s))
    (h3 : ∀ s t, a ≤ s → s ≤ t → t ≤ b → Y t - Y s ≤ r * (t - s))
    (h4 : 0 ≤ X a)
    (h5 : ∀ s t, a ≤ s → s ≤ t → t ≤ b → (∀ σ, s < σ → σ < t → 0 < X σ) →
      Y t - Y s = r * (t - s)) :
    ∀ t, a ≤ t → t ≤ b → X t = X a + (ρ - r) * (t - a) := by
  intro t hat htb
  have key : Y t - Y a = r * (t - a) := by
    apply h5 a t le_rfl hat htb
    intro σ h1σ h2σ
    have e := h1 a σ le_rfl h1σ.le (h2σ.le.trans htb)
    have := h3 a σ le_rfl h1σ.le (h2σ.le.trans htb)
    nlinarith
  have e := h1 a t le_rfl hat htb
  linarith

/-- Drain: a buffer served at rate `r` with inflow rate `0 ≤ ρ < r` drains linearly and then
stays empty. -/
theorem abs_drain {X Y : ℝ → ℝ} {a b ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ < r)
    (h1 : ∀ s t, a ≤ s → s ≤ t → t ≤ b → X t = X s + ρ * (t - s) - (Y t - Y s))
    (h2 : ∀ s t, a ≤ s → s ≤ t → t ≤ b → Y s ≤ Y t)
    (h3 : ∀ s t, a ≤ s → s ≤ t → t ≤ b → Y t - Y s ≤ r * (t - s))
    (h4 : ∀ t, a ≤ t → t ≤ b → 0 ≤ X t)
    (h5 : ∀ s t, a ≤ s → s ≤ t → t ≤ b → (∀ σ, s < σ → σ < t → 0 < X σ) →
      Y t - Y s = r * (t - s)) :
    ∀ t, a ≤ t → t ≤ b → X t = max (X a - (r - ρ) * (t - a)) 0 := by
  intro t hat htb
  have lb : X a - (r - ρ) * (t - a) ≤ X t := by
    have e := h1 a t le_rfl hat htb
    have := h3 a t le_rfl hat htb
    nlinarith
  rcases (h4 t hat htb).lt_or_eq with hpos | hzero
  · by_contra hne
    set Z : Set ℝ := {σ | a ≤ σ ∧ σ ≤ t ∧ X σ = 0} with hZ
    have hZne : Z.Nonempty := by
      by_contra hZe
      rw [Set.not_nonempty_iff_eq_empty] at hZe
      have hY := h5 a t le_rfl hat htb (by
        intro σ h1σ h2σ
        rcases (h4 σ h1σ.le (h2σ.le.trans htb)).lt_or_eq with h | h
        · exact h
        · have : σ ∈ Z := ⟨h1σ.le, h2σ.le, h.symm⟩
          rw [hZe] at this; exact absurd this (Set.notMem_empty _))
      have e := h1 a t le_rfl hat htb
      have : X t = X a - (r - ρ) * (t - a) := by linarith
      exact hne (by rw [this]; exact (max_eq_left (by linarith)).symm)
    have hZbdd : BddAbove Z := ⟨t, fun σ hσ => hσ.2.1⟩
    set s := sSup Z with hs
    have hsle : s ≤ t := csSup_le hZne (fun σ hσ => hσ.2.1)
    obtain ⟨z0, hz0⟩ := hZne
    have has : a ≤ s := le_trans hz0.1 (le_csSup hZbdd hz0)
    have hXs : X s ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have hρ1 : 0 < ρ + 1 := by linarith
      have hε : s - X s / (ρ + 1) < s := by
        have : 0 < X s / (ρ + 1) := div_pos hcon hρ1
        linarith
      obtain ⟨z, hzZ, hz⟩ := exists_lt_of_lt_csSup ⟨z0, hz0⟩ hε
      have hzs : z ≤ s := le_csSup hZbdd hzZ
      have e := h1 z s hzZ.1 hzs (hsle.trans htb)
      have := h2 z s hzZ.1 hzs (hsle.trans htb)
      rw [hzZ.2.2] at e
      have h6 : s - z < X s / (ρ + 1) := by linarith
      have h7 : ρ * (s - z) ≤ ρ * (X s / (ρ + 1)) :=
        mul_le_mul_of_nonneg_left h6.le hρ
      have h8 : ρ * (X s / (ρ + 1)) < X s := by
        rw [mul_div_assoc', div_lt_iff₀ hρ1]
        nlinarith
      linarith
    have hXs0 : X s = 0 := le_antisymm hXs (h4 s has (hsle.trans htb))
    have hst : s < t := by
      rcases lt_or_eq_of_le hsle with h | h
      · exact h
      · rw [h] at hXs0; linarith
    have hY := h5 s t has hst.le htb (by
      intro σ h1σ h2σ
      rcases (h4 σ (has.trans h1σ.le) (h2σ.le.trans htb)).lt_or_eq with h | h
      · exact h
      · have hmem : σ ∈ Z := ⟨has.trans h1σ.le, h2σ.le, h.symm⟩
        have := le_csSup hZbdd hmem
        linarith)
    have e := h1 s t has hst.le htb
    have h9 : X t = (ρ - r) * (t - s) := by rw [hXs0] at e; linarith
    have : (ρ - r) * (t - s) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  · rw [← hzero]
    have : X a - (r - ρ) * (t - a) ≤ 0 := by rw [← hzero] at lb; exact lb
    exact (max_eq_right this).symm

/-! ### Run structure -/

variable {P M : ℕ} {n : Fin P → ℕ} {S : System P M n}

theorem runExists_mono {T : Trajectory S} {m : Fin M} {i j : ℕ} (hij : i ≤ j)
    (h : T.RunExists m j) : T.RunExists m i :=
  lt_of_le_of_lt (by exact_mod_cast hij) h

theorem setupTime_nonneg (T : Trajectory S) (m : Fin M) (k : ℕ) : 0 ≤ T.setupTime m k := by
  cases k with
  | zero => simp [Trajectory.setupTime]
  | succ k => simp only [Trajectory.setupTime]; exact S.δ_nonneg _ _

theorem s_le_procStart (T : Trajectory S) (m : Fin M) (k : ℕ) : T.s m k ≤ T.procStart m k := by
  have := setupTime_nonneg T m k
  simp only [Trajectory.procStart]; linarith

theorem s_mono {T : Trajectory S} (hT : IsTrajectory S T) (m : Fin M) {i j : ℕ} (hij : i ≤ j)
    (hj : T.RunExists m j) : T.s m i ≤ T.s m j := by
  obtain ⟨-, -, -, -, -, -, -, hsetup, -⟩ := hT
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h1 := ih (runExists_mono (Nat.le_succ j) hj)
    have h2 := hsetup m j hj
    have h3 := s_le_procStart T m j
    linarith

theorem current_run {T : Trajectory S} (hT : IsTrajectory S T) (m : Fin M) (t : ℝ)
    (ht : 0 ≤ t) : ∃ k, T.RunExists m k ∧ T.s m k ≤ t ∧
      (T.RunExists m (k + 1) → t < T.s m (k + 1)) := by
  obtain ⟨-, -, -, -, hrun0, hs0, -, -, hfin, -⟩ := hT
  set F := {k : ℕ | T.RunExists m k ∧ T.s m k ≤ t}
  have hF : F.Finite := hfin m t
  have h0 : (0 : ℕ) ∈ F := ⟨hrun0 m, by rw [hs0 m]; exact ht⟩
  have hne : hF.toFinset.Nonempty := ⟨0, by simpa using h0⟩
  set k := hF.toFinset.max' hne
  have hk : k ∈ F := by simpa using hF.toFinset.max'_mem hne
  refine ⟨k, hk.1, hk.2, fun hk1 => ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem' : k + 1 ∈ F := ⟨hk1, hcon⟩
  have hmem : k + 1 ∈ hF.toFinset := hF.mem_toFinset.mpr hmem'
  have := hF.toFinset.le_max' _ hmem
  omega

/-- In a window `[a, w)` covered by run `k`, processing is decided by run `k`. -/
theorem processing_iff {T : Trajectory S} (hT : IsTrajectory S T) {m : Fin M} {k : ℕ}
    (hk : T.RunExists m k) {a w σ : ℝ} (hka : T.s m k ≤ a)
    (hkw : T.RunExists m (k + 1) → w ≤ T.s m (k + 1)) (h1 : a ≤ σ) (h2 : σ < w)
    (b : Buffer P n) :
    T.Processing m b σ ↔ T.β m k = b ∧ T.procStart m k ≤ σ := by
  constructor
  · rintro ⟨j, hj, hjb, hjs, hjn⟩
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · exfalso
      have hj1 : T.RunExists m (j + 1) := runExists_mono hjk hk
      have := hjn hj1
      have := s_mono hT m hjk hk
      linarith
    · subst hjk; exact ⟨hjb, hjs⟩
    · exfalso
      have hk1 : T.RunExists m (k + 1) := runExists_mono hjk hj
      have := hkw hk1
      have := s_mono hT m hjk hj
      have := s_le_procStart T m j
      linarith
  · rintro ⟨hb, hs⟩
    exact ⟨k, hk, hb, hs, fun h => lt_of_lt_of_le h2 (hkw h)⟩

/-! ### Output bounds -/

theorem y_mono {T : Trajectory S} (hT : IsTrajectory S T) (b : Buffer P n) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : T.y b s ≤ T.y b t :=
  hT.2.1 b hs (le_trans hs hst : (0:ℝ) ≤ t) hst

theorem y_lip {T : Trajectory S} (hT : IsTrajectory S T) (b : Buffer P n) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : T.y b t - T.y b s ≤ (1 / S.τ b) * (t - s) := by
  have hcap := hT.2.2.2.2.2.2.2.2.2.1 b s t hs hst
  have hτ := S.τ_pos b
  have hm : (volume (Set.Icc s t ∩ {σ | T.Processing (S.route b) b σ})).toReal ≤ t - s := by
    have h1 : volume (Set.Icc s t ∩ {σ | T.Processing (S.route b) b σ}) ≤
        volume (Set.Icc s t) := measure_mono Set.inter_subset_left
    rw [Real.volume_Icc] at h1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  calc T.y b t - T.y b s ≤ _ := hcap
    _ ≤ (t - s) / S.τ b := div_le_div_of_nonneg_right hm hτ.le
    _ = (1 / S.τ b) * (t - s) := by ring

theorem y_idle {T : Trajectory S} (hT : IsTrajectory S T) (b : Buffer P n) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hnp : ∀ σ, s ≤ σ → σ < t → ¬ T.Processing (S.route b) b σ) : T.y b t = T.y b s := by
  have hcap := hT.2.2.2.2.2.2.2.2.2.1 b s t hs hst
  have hsub : Set.Icc s t ∩ {σ | T.Processing (S.route b) b σ} ⊆ {t} := by
    rintro σ ⟨⟨h1, h2⟩, h3⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact absurd h3 (hnp σ h1 h)
    · exact h
  have h0 : volume (Set.Icc s t ∩ {σ | T.Processing (S.route b) b σ}) = 0 :=
    measure_mono_null hsub (Real.volume_singleton)
  rw [h0] at hcap
  simp at hcap
  have := y_mono hT b hs hst
  linarith

theorem y_full_open {T : Trajectory S} (hT : IsTrajectory S T) (b : Buffer P n) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hfull : ∀ σ, s < σ → σ < t → T.Processing (S.route b) b σ ∧ 0 < T.x b σ) :
    T.y b t - T.y b s = (1 / S.τ b) * (t - s) := by
  have hτ := S.τ_pos b
  have hr : 0 < 1 / S.τ b := by positivity
  apply le_antisymm (y_lip hT b hs hst)
  by_contra hcon
  push Not at hcon
  set D := (1 / S.τ b) * (t - s) - (T.y b t - T.y b s) with hD
  have hDpos : 0 < D := by linarith
  have hts : s < t := by
    rcases lt_or_eq_of_le hst with h | h
    · exact h
    · subst h; simp at hcon
  set μ := min (D / (1 / S.τ b) / 2) ((t - s) / 2) with hμ
  have hm1 : 0 < μ := lt_min (by positivity) (by linarith)
  have hm2 : μ ≤ D / (1 / S.τ b) / 2 := min_le_left _ _
  have hm3 : μ ≤ (t - s) / 2 := min_le_right _ _
  have hfr := hT.2.2.2.2.2.2.2.2.2.2 b (s + μ) t (by linarith) (by linarith) (by
    intro σ hσ
    exact hfull σ (by linarith [hσ.1]) hσ.2)
  have hmono := y_mono hT b hs (show s ≤ s + μ by linarith)
  have h1 : (1 / S.τ b) * (t - (s + μ)) ≤ T.y b t - T.y b s := by
    rw [show (t - (s + μ)) / S.τ b = (1 / S.τ b) * (t - (s + μ)) by ring] at hfr
    linarith
  have h2 : (1 / S.τ b) * μ ≤ D / 2 := by
    have : (1 / S.τ b) * μ ≤ (1 / S.τ b) * (D / (1 / S.τ b) / 2) :=
      mul_le_mul_of_nonneg_left hm2 hr.le
    have e : (1 / S.τ b) * (D / (1 / S.τ b) / 2) = D / 2 := by field_simp
    linarith
  have : (1 / S.τ b) * (t - s) = (1 / S.τ b) * (t - (s + μ)) + (1 / S.τ b) * μ := by ring
  linarith

end KSR

namespace KSR
open KumarSeidman.Reentrant MeasureTheory

variable {P M : ℕ} {n : Fin P → ℕ} {S : System P M n}

theorem bal_diff {T : Trajectory S} (hT : IsTrajectory S T) (b : Buffer P n) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.x b t = T.x b s + (S.input T.y b t - S.input T.y b s) - (T.y b t - T.y b s) := by
  have h1 := hT.2.2.1 b t ht
  have h2 := hT.2.2.1 b s hs
  linarith

theorem traj_drain {T : Trajectory S} (hT : IsTrajectory S T) (bb : Buffer P n) {a w ρ : ℝ}
    (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (hr : ρ < 1 / S.τ bb)
    (hP : ∀ σ, a ≤ σ → σ < w → T.Processing (S.route bb) bb σ)
    (hu : ∀ t, a ≤ t → t ≤ w → S.input T.y bb t = S.input T.y bb a + ρ * (t - a)) :
    ∀ t, a ≤ t → t ≤ w → T.x bb t = max (T.x bb a - (1 / S.τ bb - ρ) * (t - a)) 0 := by
  apply abs_drain (Y := T.y bb) hρ hr
  · intro s t has hst htw
    rw [bal_diff hT bb (ha.trans has) (ha.trans (has.trans hst)), hu t (has.trans hst) htw,
      hu s has (hst.trans htw)]
    ring
  · intro s t has hst htw; exact y_mono hT bb (ha.trans has) hst
  · intro s t has hst htw; exact y_lip hT bb (ha.trans has) hst
  · intro t hat htw; exact hT.2.2.2.1 bb t (ha.trans hat)
  · intro s t has hst htw hpos
    exact y_full_open hT bb (ha.trans has) hst (fun σ h1 h2 =>
      ⟨hP σ (by linarith) (by linarith), hpos σ h1 h2⟩)

theorem traj_fill {T : Trajectory S} (hT : IsTrajectory S T) (bb : Buffer P n) {a w ρ : ℝ}
    (ha : 0 ≤ a) (hr : 1 / S.τ bb < ρ)
    (hP : ∀ σ, a ≤ σ → σ < w → T.Processing (S.route bb) bb σ)
    (hu : ∀ t, a ≤ t → t ≤ w → S.input T.y bb t = S.input T.y bb a + ρ * (t - a)) :
    ∀ t, a ≤ t → t ≤ w → T.x bb t = T.x bb a + (ρ - 1 / S.τ bb) * (t - a) := by
  apply abs_fill (Y := T.y bb) hr
  · intro s t has hst htw
    rw [bal_diff hT bb (ha.trans has) (ha.trans (has.trans hst)), hu t (has.trans hst) htw,
      hu s has (hst.trans htw)]
    ring
  · intro s t has hst htw; exact y_lip hT bb (ha.trans has) hst
  · exact hT.2.2.2.1 bb a ha
  · intro s t has hst htw hpos
    exact y_full_open hT bb (ha.trans has) hst (fun σ h1 h2 =>
      ⟨hP σ (by linarith) (by linarith), hpos σ h1 h2⟩)

theorem traj_idle {T : Trajectory S} (hT : IsTrajectory S T) (bb : Buffer P n) {a w : ℝ}
    (ha : 0 ≤ a) (hnp : ∀ σ, a ≤ σ → σ < w → ¬ T.Processing (S.route bb) bb σ) :
    ∀ t, a ≤ t → t ≤ w → T.y bb t = T.y bb a := by
  intro t hat htw
  exact y_idle hT bb ha hat (fun σ h1 h2 => hnp σ h1 (lt_of_lt_of_le h2 htw))

/-- Demanding from strict increase of the input on a short interval. -/
theorem demanding_of_incr {T : Trajectory S} (hT : IsTrajectory S T) (b : Buffer P n) {t w : ℝ}
    (ht : 0 ≤ t) (htw : t < w) (hinc : ∀ σ, t < σ → σ ≤ w → S.input T.y b t < S.input T.y b σ)
    (hmono : ∀ σ σ', 0 ≤ σ → σ ≤ σ' → S.input T.y b σ ≤ S.input T.y b σ') :
    T.Demanding b t := by
  right
  intro σ hσ
  rcases le_or_gt σ w with h | h
  · exact hinc σ hσ h
  · exact lt_of_lt_of_le (hinc w htw le_rfl) (hmono w σ (by linarith) h.le)

end KSR

namespace KSR
open KumarSeidman.Reentrant

section Ex1
variable {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k} {δ : Fin 4 → ℝ} {hδ : ∀ k, 0 ≤ δ k}

theorem ex1_route (k : Fin 4) : (ex1 τ hτ δ hδ).route (ex1Buf k) = ![0, 1, 1, 0] k := rfl
theorem ex1_τ (k : Fin 4) : (ex1 τ hτ δ hδ).τ (ex1Buf k) = τ k := rfl
theorem ex1_input0 (y : Ex1Buffer → ℝ → ℝ) (t : ℝ) :
    (ex1 τ hτ δ hδ).input y (ex1Buf 0) t = t := by
  simp [System.input, ex1Buf, ex1]
theorem ex1_input1 (y : Ex1Buffer → ℝ → ℝ) (t : ℝ) :
    (ex1 τ hτ δ hδ).input y (ex1Buf 1) t = y (ex1Buf 0) t := by
  simp [System.input, ex1Buf]
theorem ex1_input2 (y : Ex1Buffer → ℝ → ℝ) (t : ℝ) :
    (ex1 τ hτ δ hδ).input y (ex1Buf 2) t = y (ex1Buf 1) t := by
  simp [System.input, ex1Buf]
theorem ex1_input3 (y : Ex1Buffer → ℝ → ℝ) (t : ℝ) :
    (ex1 τ hτ δ hδ).input y (ex1Buf 3) t = y (ex1Buf 2) t := by
  simp [System.input, ex1Buf]

theorem ex1_buf_eq (b : Ex1Buffer) : b = ex1Buf b.2 := by
  obtain ⟨p, i⟩ := b
  have : p = 0 := Subsingleton.elim _ _
  subst this; rfl

theorem ex1_m0 {b : Ex1Buffer} (h : (ex1 τ hτ δ hδ).route b = 0) :
    b = ex1Buf 0 ∨ b = ex1Buf 3 := by
  rw [ex1_buf_eq b] at h ⊢
  rw [ex1_route] at h
  generalize b.2 = k at h ⊢
  fin_cases k <;> simp_all

theorem ex1_m1 {b : Ex1Buffer} (h : (ex1 τ hτ δ hδ).route b = 1) :
    b = ex1Buf 1 ∨ b = ex1Buf 2 := by
  rw [ex1_buf_eq b] at h ⊢
  rw [ex1_route] at h
  generalize b.2 = k at h ⊢
  fin_cases k <;> simp_all

theorem ex1Buf_inj {i j : Fin 4} (h : ex1Buf i = ex1Buf j) : i = j := by
  simp [ex1Buf] at h; exact h

end Ex1

theorem ex1_zero_setup {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k}
    (T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0))) (m : Fin 2) (k : ℕ) :
    T.procStart m k = T.s m k := by
  cases k with
  | zero => simp [Trajectory.procStart, Trajectory.setupTime]
  | succ k =>
    simp only [Trajectory.procStart, Trajectory.setupTime, ex1]
    split_ifs <;> simp

end KSR

namespace KSR
open KumarSeidman.Reentrant

section Ex1b
variable {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k} {δ : Fin 4 → ℝ} {hδ : ∀ k, 0 ≤ δ k}
variable {T : Trajectory (ex1 τ hτ δ hδ)}

theorem bal0 (hT : IsTrajectory _ T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.x (ex1Buf 0) t = T.x (ex1Buf 0) s + (t - s) - (T.y (ex1Buf 0) t - T.y (ex1Buf 0) s) := by
  rw [bal_diff hT _ hs ht, ex1_input0, ex1_input0]
theorem bal1 (hT : IsTrajectory _ T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.x (ex1Buf 1) t = T.x (ex1Buf 1) s + (T.y (ex1Buf 0) t - T.y (ex1Buf 0) s) -
      (T.y (ex1Buf 1) t - T.y (ex1Buf 1) s) := by
  rw [bal_diff hT _ hs ht, ex1_input1, ex1_input1]
theorem bal2 (hT : IsTrajectory _ T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.x (ex1Buf 2) t = T.x (ex1Buf 2) s + (T.y (ex1Buf 1) t - T.y (ex1Buf 1) s) -
      (T.y (ex1Buf 2) t - T.y (ex1Buf 2) s) := by
  rw [bal_diff hT _ hs ht, ex1_input2, ex1_input2]
theorem bal3 (hT : IsTrajectory _ T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.x (ex1Buf 3) t = T.x (ex1Buf 3) s + (T.y (ex1Buf 2) t - T.y (ex1Buf 2) s) -
      (T.y (ex1Buf 3) t - T.y (ex1Buf 3) s) := by
  rw [bal_diff hT _ hs ht, ex1_input3, ex1_input3]

theorem dem0 (t : ℝ) : T.Demanding (ex1Buf 0) t :=
  Or.inr (fun σ h => by rw [ex1_input0, ex1_input0]; exact h)

theorem notdem {b : Ex1Buffer} {t t' : ℝ} (hx : T.x b t = 0) (htt' : t < t')
    (hc : (ex1 τ hτ δ hδ).input T.y b t' = (ex1 τ hτ δ hδ).input T.y b t) :
    ¬ T.Demanding b t := by
  rintro (h | h)
  · rw [hx] at h; exact lt_irrefl _ h
  · have := h t' htt'; rw [hc] at this; exact lt_irrefl _ this

theorem input_mono (hT : IsTrajectory _ T) (b : Ex1Buffer) :
    ∀ σ σ', 0 ≤ σ → σ ≤ σ' → (ex1 τ hτ δ hδ).input T.y b σ ≤ (ex1 τ hτ δ hδ).input T.y b σ' := by
  intro σ σ' h0 h1
  rw [ex1_buf_eq b]
  generalize b.2 = k
  fin_cases k
  · simp only [Fin.zero_eta, ex1_input0]; exact h1
  · simp only [Fin.mk_one, ex1_input1]; exact y_mono hT _ h0 h1
  · show (ex1 τ hτ δ hδ).input T.y (ex1Buf 2) σ ≤ (ex1 τ hτ δ hδ).input T.y (ex1Buf 2) σ'
    rw [ex1_input2, ex1_input2]; exact y_mono hT _ h0 h1
  · show (ex1 τ hτ δ hδ).input T.y (ex1Buf 3) σ ≤ (ex1 τ hτ δ hδ).input T.y (ex1Buf 3) σ'
    rw [ex1_input3, ex1_input3]; exact y_mono hT _ h0 h1

/-- A buffer that is empty at `a` and receives no input on `[a, w]` stays empty, with constant
output. -/
theorem zero_chain (hT : IsTrajectory _ T) (b : Ex1Buffer) {a w : ℝ} (ha : 0 ≤ a)
    (hx : T.x b a = 0)
    (hc : ∀ t, a ≤ t → t ≤ w → (ex1 τ hτ δ hδ).input T.y b t = (ex1 τ hτ δ hδ).input T.y b a) :
    ∀ t, a ≤ t → t ≤ w → T.x b t = 0 ∧ T.y b t = T.y b a := by
  intro t h1 h2
  have e := bal_diff hT b ha (ha.trans h1)
  rw [hc t h1 h2, hx] at e
  have hm := y_mono hT b ha h1
  have hn := hT.2.2.2.1 b t (ha.trans h1)
  constructor <;> linarith

end Ex1b

theorem window {P M : ℕ} {n : Fin P → ℕ} {S : System P M n} {T : Trajectory S}
    (hT : IsTrajectory S T) (m : Fin M) {t : ℝ} (ht : 0 ≤ t) (C : ℝ) (hC : t < C) :
    ∃ k w, T.RunExists m k ∧ T.s m k ≤ t ∧ t < w ∧ w ≤ C ∧
      (T.RunExists m (k + 1) → w ≤ T.s m (k + 1)) ∧
      (w < C → T.RunExists m (k + 1) ∧ T.s m (k + 1) = w) := by
  obtain ⟨k, hk, hks, hkn⟩ := current_run hT m t ht
  by_cases h : T.RunExists m (k + 1)
  · refine ⟨k, min C (T.s m (k + 1)), hk, hks, lt_min hC (hkn h), min_le_left _ _,
      fun _ => min_le_right _ _, fun hw => ⟨h, ?_⟩⟩
    rcases le_total C (T.s m (k + 1)) with h' | h'
    · rw [min_eq_left h'] at hw; exact absurd hw (lt_irrefl _)
    · rw [min_eq_right h']
  · exact ⟨k, C, hk, hks, hC, le_rfl, fun h' => absurd h' h, fun hw => absurd hw (lt_irrefl _)⟩

/-! ### Zero set-up times -/

abbrev S2 (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k) := ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)

section C2
variable {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k} {T : Trajectory (S2 τ hτ)}

theorem pw (hT : IsTrajectory _ T) {m : Fin 2} {k : ℕ} (hk : T.RunExists m k) {a w σ : ℝ}
    (hka : T.s m k ≤ a) (hkw : T.RunExists m (k + 1) → w ≤ T.s m (k + 1)) (h1 : a ≤ σ)
    (h2 : σ < w) (b : Ex1Buffer) : T.Processing m b σ ↔ T.β m k = b := by
  rw [processing_iff hT hk hka hkw h1 h2, ex1_zero_setup]
  exact ⟨fun h => h.1, fun h => ⟨h, hka.trans h1⟩⟩

theorem nx (hC : IsClearing _ T) {m : Fin 2} {k : ℕ} (hk : T.RunExists m k) {a w t : ℝ}
    (hka : T.s m k ≤ a) (hkw : T.RunExists m (k + 1) → w ≤ T.s m (k + 1)) (h1 : a < t)
    (h2 : t < w) :
    ¬ (T.x (T.β m k) t = 0 ∧
      ∃ b', (S2 τ hτ).route b' = m ∧ b' ≠ T.β m k ∧ T.Demanding b' t) :=
  (hC.2 m k hk).1 t (by rw [ex1_zero_setup]; linarith) (fun h => lt_of_lt_of_le h2 (hkw h))

end C2
end KSR


namespace KSR
open KumarSeidman.Reentrant

section C2
variable {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k} {T : Trajectory (S2 τ hτ)}

theorem ne01 : ex1Buf 0 ≠ ex1Buf 1 := fun h => absurd (ex1Buf_inj h) (by decide)
theorem ne03 : ex1Buf 0 ≠ ex1Buf 3 := fun h => absurd (ex1Buf_inj h) (by decide)
theorem ne12 : ex1Buf 1 ≠ ex1Buf 2 := fun h => absurd (ex1Buf_inj h) (by decide)

/-- Phase A of Case 2: from `x(a) = (ξ,0,0,0)`, at `a + ξτ₂/(1-τ₂)` the state is
`(0, 0, ξ/(1-τ₂), 0)`. -/
theorem phaseA (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    (hC : IsClearing (S2 τ hτ) T) {a ξ : ℝ} (ha : 0 ≤ a) (hξ : 0 < ξ)
    (hx0 : T.x (ex1Buf 0) a = ξ) (hx1 : T.x (ex1Buf 1) a = 0) (hx2 : T.x (ex1Buf 2) a = 0)
    (hx3 : T.x (ex1Buf 3) a = 0) :
    T.x (ex1Buf 0) (a + ξ * τ 1 / (1 - τ 1)) = 0 ∧
    T.x (ex1Buf 1) (a + ξ * τ 1 / (1 - τ 1)) = 0 ∧
    T.x (ex1Buf 2) (a + ξ * τ 1 / (1 - τ 1)) = ξ / (1 - τ 1) ∧
    T.x (ex1Buf 3) (a + ξ * τ 1 / (1 - τ 1)) = 0 := by
  have hT := hC.1
  have ht0 := hτ 0
  have ht1 := hτ 1
  have ht2 := hτ 2
  have ht3 := hτ 3
  have h01 : τ 0 < τ 1 := by linarith
  have h1lt : τ 1 < 1 := by linarith
  have h0lt : τ 0 < 1 := by linarith
  set r0 := 1 / τ 0 with hr0
  set r1 := 1 / τ 1 with hr1
  have hr01 : r1 < r0 := one_div_lt_one_div_of_lt ht0 h01
  have hr1g : 1 < r1 := by rw [hr1, lt_one_div (by norm_num) ht1]; simpa using h1lt
  have hr0ne : r0 - 1 ≠ 0 := by linarith
  have hr1ne : r1 - 1 ≠ 0 := by linarith
  set p2 := ξ / (r0 - 1) with hp2
  set A := (r0 - r1) * p2 with hA
  set p3 := ξ * τ 1 / (1 - τ 1) with hp3
  have hp2pos : 0 < p2 := div_pos hξ (by linarith)
  have hApos : 0 < A := mul_pos (by linarith) hp2pos
  have hp3e : p3 = p2 + A / (r1 - 1) := by
    rw [hp3, hA, hp2, hr0, hr1]
    have : (1 - τ 0) ≠ 0 := by linarith
    have : (1 - τ 1) ≠ 0 := by linarith
    have : 1 / τ 0 - 1 ≠ 0 := by
      rw [div_sub_one (ne_of_gt ht0)]; exact div_ne_zero (by linarith) (ne_of_gt ht0)
    have : 1 / τ 1 - 1 ≠ 0 := by
      rw [div_sub_one (ne_of_gt ht1)]; exact div_ne_zero (by linarith) (ne_of_gt ht1)
    field_simp
    ring
  have hp23 : p2 < p3 := by
    rw [hp3e]; have : 0 < A / (r1 - 1) := div_pos hApos (by linarith); linarith
  set C := a + p3 + 1 with hCdef
  obtain ⟨k1, w1, hk1, hk1a, haw1, hw1C, hk1w, hw1e⟩ := window hT 0 ha C (by linarith)
  obtain ⟨k2, w2, hk2, hk2a, haw2, hw2C, hk2w, hw2e⟩ := window hT 1 ha C (by linarith)
  have hroute := hT.2.2.2.2.2.2.1
  -- machine 0 is on buffer 1 (Lean `ex1Buf 0`)
  have hb1 : T.β 0 k1 = ex1Buf 0 := by
    rcases ex1_m0 (hroute 0 k1 hk1) with h | h
    · exact h
    exfalso
    have hy0 : ∀ t, a ≤ t → t ≤ w1 → T.y (ex1Buf 0) t = T.y (ex1Buf 0) a :=
      traj_idle hT _ ha (fun σ h1 h2 hp => by
        rw [show (S2 τ hτ).route (ex1Buf 0) = 0 from rfl, pw hT hk1 hk1a hk1w h1 h2, h] at hp
        exact ne03 hp.symm)
    have z1 := zero_chain hT (ex1Buf 1) ha hx1 (fun t h1 h2 => by
      rw [ex1_input1, ex1_input1, hy0 t h1 h2])
    have z2 := zero_chain hT (ex1Buf 2) ha hx2 (fun t h1 h2 => by
      rw [ex1_input2, ex1_input2, (z1 t h1 h2).2])
    have z3 := zero_chain hT (ex1Buf 3) ha hx3 (fun t h1 h2 => by
      rw [ex1_input3, ex1_input3, (z2 t h1 h2).2])
    apply nx hC hk1 hk1a hk1w (show a < (a + w1) / 2 by linarith)
      (show (a + w1) / 2 < w1 by linarith)
    rw [h]
    exact ⟨(z3 _ (by linarith) (by linarith)).1, ex1Buf 0, rfl, ne03, dem0 _⟩
  -- formulas for buffer 1 on [a, w1]
  have hP0 : ∀ σ, a ≤ σ → σ < w1 → T.Processing ((S2 τ hτ).route (ex1Buf 0)) (ex1Buf 0) σ :=
    fun σ h1 h2 => (pw hT hk1 hk1a hk1w h1 h2 _).2 hb1
  have fx0 : ∀ t, a ≤ t → t ≤ w1 → T.x (ex1Buf 0) t = max (ξ - (r0 - 1) * (t - a)) 0 := by
    have := traj_drain hT (ex1Buf 0) (ρ := 1) ha zero_le_one (by
        show (1:ℝ) < 1 / τ 0; rw [lt_one_div (by norm_num) ht0]; simpa using h0lt) hP0
      (fun t _ _ => by rw [ex1_input0, ex1_input0]; ring)
    intro t h1 h2
    rw [this t h1 h2, hx0]; rfl
  have fy0 : ∀ t, a ≤ t → t ≤ w1 →
      T.y (ex1Buf 0) t = T.y (ex1Buf 0) a + (t - a) + ξ - max (ξ - (r0 - 1) * (t - a)) 0 := by
    intro t h1 h2
    have e := bal0 hT ha (ha.trans h1)
    rw [fx0 t h1 h2, hx0] at e
    linarith
  -- y0 strictly increasing on [a, w1]
  have y0inc : ∀ t σ, a ≤ t → t < σ → σ ≤ w1 → T.y (ex1Buf 0) t < T.y (ex1Buf 0) σ := by
    intro t σ h1 h2 h3
    rw [fy0 t h1 (h2.le.trans h3), fy0 σ (h1.trans h2.le) h3]
    have : max (ξ - (r0 - 1) * (σ - a)) 0 ≤ max (ξ - (r0 - 1) * (t - a)) 0 :=
      max_le_max (by nlinarith) le_rfl
    linarith
  -- machine 1 is on buffer 2 (Lean `ex1Buf 1`)
  have hb2 : T.β 1 k2 = ex1Buf 1 := by
    rcases ex1_m1 (hroute 1 k2 hk2) with h | h
    · exact h
    exfalso
    have hy1 : ∀ t, a ≤ t → t ≤ w2 → T.y (ex1Buf 1) t = T.y (ex1Buf 1) a :=
      traj_idle hT _ ha (fun σ h1 h2 hp => by
        rw [show (S2 τ hτ).route (ex1Buf 1) = 1 from rfl, pw hT hk2 hk2a hk2w h1 h2, h] at hp
        exact ne12 hp.symm)
    have z2 : ∀ t, a ≤ t → t ≤ w2 → T.x (ex1Buf 2) t = 0 := by
      intro t h1 h2
      have e := bal2 hT ha (ha.trans h1)
      rw [hy1 t h1 h2, hx2] at e
      have hm := y_mono hT (ex1Buf 2) ha h1
      have hn := hT.2.2.2.1 (ex1Buf 2) t (ha.trans h1)
      linarith
    set V := min w1 w2
    have hV1 : V ≤ w1 := min_le_left _ _
    have hV2 : V ≤ w2 := min_le_right _ _
    have haV : a < V := lt_min haw1 haw2
    apply nx hC hk2 hk2a hk2w (show a < (a + V) / 2 by linarith)
      (show (a + V) / 2 < w2 by linarith)
    rw [h]
    refine ⟨z2 _ (by linarith) (by linarith), ex1Buf 1, rfl, ne12, ?_⟩
    apply demanding_of_incr hT _ (by linarith) (show (a + V) / 2 < w1 by linarith)
      (fun σ h1 h2 => by rw [ex1_input1, ex1_input1]; exact y0inc _ _ (by linarith) h1 h2)
      (input_mono hT _)
  have hP1 : ∀ σ, a ≤ σ → σ < w2 → T.Processing ((S2 τ hτ).route (ex1Buf 1)) (ex1Buf 1) σ :=
    fun σ h1 h2 => (pw hT hk2 hk2a hk2w h1 h2 _).2 hb2
  set V := min w1 w2 with hVdef
  have hV1 : V ≤ w1 := min_le_left _ _
  have hV2 : V ≤ w2 := min_le_right _ _
  have haV : a < V := lt_min haw1 haw2
  -- buffer 1 before it empties
  have fx0a : ∀ t, a ≤ t → t ≤ a + p2 → max (ξ - (r0 - 1) * (t - a)) 0 = ξ - (r0 - 1) * (t - a) := by
    intro t h1 h2
    apply max_eq_left
    have : (r0 - 1) * (t - a) ≤ (r0 - 1) * p2 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e : (r0 - 1) * p2 = ξ := by rw [hp2]; field_simp
    linarith
  have fx0b : ∀ t, a + p2 ≤ t → max (ξ - (r0 - 1) * (t - a)) 0 = 0 := by
    intro t h1
    apply max_eq_right
    have : (r0 - 1) * p2 ≤ (r0 - 1) * (t - a) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e : (r0 - 1) * p2 = ξ := by rw [hp2]; field_simp
    linarith
  -- fill of buffer 2 on [a, min (a+p2) V]
  have fx1a : ∀ t, a ≤ t → t ≤ min (a + p2) V → T.x (ex1Buf 1) t = (r0 - r1) * (t - a) := by
    have := traj_fill hT (ex1Buf 1) (ρ := r0) (w := min (a + p2) V) ha
      (show 1 / τ 1 < r0 from hr01)
      (fun σ h1 h2 => hP1 σ h1 (lt_of_lt_of_le h2 ((min_le_right _ _).trans hV2)))
      (fun t h1 h2 => by
        have h2' : t ≤ a + p2 := h2.trans (min_le_left _ _)
        have h2'' : t ≤ w1 := h2.trans ((min_le_right _ _).trans hV1)
        rw [ex1_input1, ex1_input1, fy0 t h1 h2'', fy0 a le_rfl haw1.le, fx0a t h1 h2',
          fx0a a le_rfl (by linarith)]
        ring)
    intro t h1 h2
    rw [this t h1 h2, hx1]; simp only [zero_add]; rfl
  -- drain of buffer 2 on [a+p2, V]
  have fx1b : ∀ t, a + p2 ≤ t → t ≤ V →
      T.x (ex1Buf 1) t = max (T.x (ex1Buf 1) (a + p2) - (r1 - 1) * (t - (a + p2))) 0 := by
    have := traj_drain hT (ex1Buf 1) (ρ := 1) (a := a + p2) (w := V) (by linarith) zero_le_one
      (show (1:ℝ) < 1 / τ 1 from hr1g)
      (fun σ h1 h2 => hP1 σ (by linarith) (lt_of_lt_of_le h2 hV2))
      (fun t h1 h2 => by
        rw [ex1_input1, ex1_input1, fy0 t (by linarith) (h2.trans hV1),
          fy0 (a + p2) (by linarith) ((h1.trans h2).trans hV1), fx0b t h1, fx0b (a + p2) le_rfl]
        ring)
    intro t h1 h2
    rw [this t h1 h2]; rfl
  -- buffer 3 output idle, buffer 4 empty
  have hy2 : ∀ t, a ≤ t → t ≤ w2 → T.y (ex1Buf 2) t = T.y (ex1Buf 2) a :=
    traj_idle hT _ ha (fun σ h1 h2 hp => by
      rw [show (S2 τ hτ).route (ex1Buf 2) = 1 from rfl, pw hT hk2 hk2a hk2w h1 h2, hb2] at hp
      exact ne12 hp)
  have z3 := zero_chain hT (ex1Buf 3) ha hx3 (fun t h1 h2 => by
      rw [ex1_input3, ex1_input3, hy2 t h1 h2])
  have fx2 : ∀ t, a ≤ t → t ≤ V → T.x (ex1Buf 2) t =
      (t - a) + ξ - max (ξ - (r0 - 1) * (t - a)) 0 - T.x (ex1Buf 1) t := by
    intro t h1 h2
    have e1 := bal1 hT ha (ha.trans h1)
    have e2 := bal2 hT ha (ha.trans h1)
    rw [hy2 t h1 (h2.trans hV2), hx2] at e2
    rw [fy0 t h1 (h2.trans hV1), hx1] at e1
    linarith
  -- x1 positive before a + p3
  have hx1pos : ∀ t, a < t → t < a + p3 → t ≤ V → 0 < T.x (ex1Buf 1) t := by
    intro t h1 h2 h3
    rcases le_total t (a + p2) with h | h
    · rw [fx1a t h1.le (le_min h h3)]; exact mul_pos (by linarith) (by linarith)
    · rw [fx1b t h h3, fx1a (a + p2) (by linarith) (le_min le_rfl (h.trans h3))]
      have hlt : t - (a + p2) < A / (r1 - 1) := by linarith
      have : (r1 - 1) * (t - (a + p2)) < A := by
        rw [lt_div_iff₀ (by linarith)] at hlt; linarith
      apply lt_max_of_lt_left
      have e : (r0 - r1) * (a + p2 - a) = A := by rw [hA]; ring
      linarith
  -- the first switch is not before a + p3
  have hVp3 : a + p3 ≤ V := by
    by_contra hcon
    push Not at hcon
    rcases le_total w2 w1 with h | h
    · have hVw : V = w2 := min_eq_right h
      obtain ⟨hr, hs⟩ := hw2e (by linarith)
      have := ((hC.2 1 k2 hk2).2 hr).1
      rw [hs, hb2] at this
      have := hx1pos w2 haw2 (by linarith) (by linarith)
      linarith
    · have hVw : V = w1 := min_eq_left h
      obtain ⟨hr, hs⟩ := hw1e (by linarith)
      have hex := ((hC.2 0 k1 hk1).2 hr)
      rw [hs] at hex
      obtain ⟨-, hne, hdem⟩ := hex
      have hb' := ex1_m0 (hroute 0 (k1 + 1) hr)
      rw [hb1] at hne
      rcases hb' with hb' | hb'
      · exact hne hb'
      rw [hb'] at hdem
      rcases lt_or_eq_of_le h with h' | h'
      · apply notdem (z3 w1 haw1.le h).1 h' _ hdem
        rw [ex1_input3, ex1_input3, hy2 w1 haw1.le h, hy2 w2 haw2.le le_rfl]
      · -- w1 = w2 = V < a + p3 : then also machine 1 switches there
        obtain ⟨hr2, hs2⟩ := hw2e (by linarith)
        have := ((hC.2 1 k2 hk2).2 hr2).1
        rw [hs2, hb2] at this
        have := hx1pos w2 haw2 (by linarith) (by linarith)
        linarith
  -- values at a + p3
  have hap3 : a ≤ a + p3 := by linarith
  have e0 : max (ξ - (r0 - 1) * (a + p3 - a)) 0 = 0 := fx0b _ (by linarith)
  have ex1v : T.x (ex1Buf 1) (a + p3) = 0 := by
    rw [fx1b _ (by linarith) hVp3, fx1a (a + p2) (by linarith) (le_min le_rfl (by linarith))]
    apply max_eq_right
    have : A = (r1 - 1) * (a + p3 - (a + p2)) := by
      rw [hp3e]; field_simp; ring_nf
    have e : (r0 - r1) * (a + p2 - a) = A := by rw [hA]; ring
    linarith
  refine ⟨?_, ex1v, ?_, (z3 _ hap3 (hVp3.trans hV2)).1⟩
  · rw [fx0 _ hap3 (hVp3.trans hV1), e0]
  · rw [fx2 _ hap3 hVp3, e0, ex1v, hp3]
    have : (1 - τ 1) ≠ 0 := by linarith
    field_simp
    ring

theorem ne23 : ex1Buf 2 ≠ ex1Buf 3 := fun h => absurd (ex1Buf_inj h) (by decide)

/-- Phase B of Case 2: from `x(a) = (0,0,X,0)`, at `a + τ₄X` the state is `(τ₄X, 0, 0, 0)` with
machines set up for buffers 4 and 3. -/
theorem phaseB (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    (hC : IsClearing (S2 τ hτ) T) {a X : ℝ} (ha : 0 ≤ a) (hX : 0 < X)
    (hx0 : T.x (ex1Buf 0) a = 0) (hx1 : T.x (ex1Buf 1) a = 0) (hx2 : T.x (ex1Buf 2) a = X)
    (hx3 : T.x (ex1Buf 3) a = 0) :
    T.x (ex1Buf 0) (a + τ 3 * X) = τ 3 * X ∧ T.x (ex1Buf 1) (a + τ 3 * X) = 0 ∧
    T.x (ex1Buf 2) (a + τ 3 * X) = 0 ∧ T.x (ex1Buf 3) (a + τ 3 * X) = 0 ∧
    T.IsSetUpFor 0 (a + τ 3 * X) (ex1Buf 3) ∧ T.IsSetUpFor 1 (a + τ 3 * X) (ex1Buf 2) := by
  have hT := hC.1
  have ht0 := hτ 0
  have ht1 := hτ 1
  have ht2 := hτ 2
  have ht3 := hτ 3
  have h23 : τ 2 < τ 3 := by linarith
  have h1lt : τ 1 < 1 := by linarith
  set r1 := 1 / τ 1 with hr1
  set r2 := 1 / τ 2 with hr2
  set r3 := 1 / τ 3 with hr3
  have hr1g : 1 < r1 := by rw [hr1, lt_one_div (by norm_num) ht1]; simpa using h1lt
  have hr23 : r3 < r2 := one_div_lt_one_div_of_lt ht2 h23
  have hr3pos : 0 < r3 := by positivity
  set q4 := τ 2 * X with hq4
  set q5 := τ 3 * X with hq5
  have hq4pos : 0 < q4 := mul_pos ht2 hX
  have hq45 : q4 < q5 := mul_lt_mul_of_pos_right h23 hX
  set Bv := (r2 - r3) * q4 with hBv
  have hBve : Bv = r3 * (q5 - q4) := by
    rw [hBv, hr2, hr3, hq4, hq5]; field_simp
  have hr2q4 : r2 * q4 = X := by rw [hr2, hq4]; field_simp
  set C := a + q5 + 1 with hCdef
  obtain ⟨j1, w1, hj1, hj1a, haw1, hw1C, hj1w, hw1e⟩ := window hT 0 ha C (by linarith)
  obtain ⟨j2, w2, hj2, hj2a, haw2, hw2C, hj2w, hw2e⟩ := window hT 1 ha C (by linarith)
  have hroute := hT.2.2.2.2.2.2.1
  set V := min w1 w2 with hVdef
  have hV1 : V ≤ w1 := min_le_left _ _
  have hV2 : V ≤ w2 := min_le_right _ _
  have haV : a < V := lt_min haw1 haw2
  -- machine 1 (Lean) is on buffer 3 (Lean `ex1Buf 2`)
  have hb2 : T.β 1 j2 = ex1Buf 2 := by
    rcases ex1_m1 (hroute 1 j2 hj2) with h | h
    swap
    · exact h
    exfalso
    have hy2 : ∀ t, a ≤ t → t ≤ w2 → T.y (ex1Buf 2) t = T.y (ex1Buf 2) a :=
      traj_idle hT _ ha (fun σ h1 h2 hp => by
        rw [show (S2 τ hτ).route (ex1Buf 2) = 1 from rfl, pw hT hj2 hj2a hj2w h1 h2, h] at hp
        exact ne12 hp)
    have hx2pos : ∀ t, a ≤ t → t ≤ w2 → 0 < T.x (ex1Buf 2) t := by
      intro t h1 h2
      have e := bal2 hT ha (ha.trans h1)
      rw [hy2 t h1 h2, hx2] at e
      have := y_mono hT (ex1Buf 1) ha h1
      linarith
    obtain ⟨ρ, hρ0, hρ1, hy0⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ 1 ∧
        ∀ t, a ≤ t → t ≤ w1 → T.y (ex1Buf 0) t = T.y (ex1Buf 0) a + ρ * (t - a) := by
      rcases ex1_m0 (hroute 0 j1 hj1) with h' | h'
      · have hP0 : ∀ σ, a ≤ σ → σ < w1 →
            T.Processing ((S2 τ hτ).route (ex1Buf 0)) (ex1Buf 0) σ :=
          fun σ h1 h2 => (pw hT hj1 hj1a hj1w h1 h2 _).2 h'
        have dr := traj_drain hT (ex1Buf 0) (ρ := 1) ha zero_le_one (by
            show (1:ℝ) < 1 / τ 0; rw [lt_one_div (by norm_num) ht0]; simpa using (by linarith : τ 0 < 1)) hP0
          (fun t _ _ => by rw [ex1_input0, ex1_input0]; ring)
        refine ⟨1, zero_le_one, le_rfl, fun t h1 h2 => ?_⟩
        have e := bal0 hT ha (ha.trans h1)
        have e2 := dr t h1 h2
        rw [hx0] at e2
        have : max (0 - (1 / (S2 τ hτ).τ (ex1Buf 0) - 1) * (t - a)) 0 = 0 := by
          apply max_eq_right
          have : 0 ≤ (1 / (S2 τ hτ).τ (ex1Buf 0) - 1) * (t - a) := by
            apply mul_nonneg _ (by linarith)
            show 0 ≤ 1 / τ 0 - 1
            rw [sub_nonneg, le_one_div (by norm_num) ht0]; linarith
          linarith
        rw [this] at e2
        rw [e2, hx0] at e
        linarith
      · refine ⟨0, le_rfl, zero_le_one, fun t h1 h2 => ?_⟩
        have := traj_idle hT (ex1Buf 0) ha (w := w1) (fun σ h1 h2 hp => by
          rw [show (S2 τ hτ).route (ex1Buf 0) = 0 from rfl, pw hT hj1 hj1a hj1w h1 h2, h'] at hp
          exact ne03 hp.symm) t h1 h2
        rw [this]; ring
    have dr1 := traj_drain hT (ex1Buf 1) (ρ := ρ) (w := V) ha hρ0
      (show ρ < 1 / τ 1 by linarith)
      (fun σ h1 h2 => (pw hT hj2 hj2a hj2w h1 (lt_of_lt_of_le h2 hV2) _).2 h)
      (fun t h1 h2 => by rw [ex1_input1, ex1_input1, hy0 t h1 (h2.trans hV1)])
    set t := (a + V) / 2
    have hat : a < t := by simp only [t]; linarith
    have htV : t < V := by simp only [t]; linarith
    apply nx hC hj2 hj2a hj2w hat (lt_of_lt_of_le htV hV2)
    rw [h]
    refine ⟨?_, ex1Buf 2, rfl, ne12.symm, Or.inl (hx2pos t hat.le (htV.le.trans hV2))⟩
    rw [dr1 t hat.le htV.le, hx1]
    apply max_eq_right
    have : 0 ≤ (1 / (S2 τ hτ).τ (ex1Buf 1) - ρ) * (t - a) :=
      mul_nonneg (by show 0 ≤ 1 / τ 1 - ρ; linarith) (by linarith)
    linarith
  -- buffer 3 drains
  have hy1 : ∀ t, a ≤ t → t ≤ w2 → T.y (ex1Buf 1) t = T.y (ex1Buf 1) a :=
    traj_idle hT _ ha (fun σ h1 h2 hp => by
      rw [show (S2 τ hτ).route (ex1Buf 1) = 1 from rfl, pw hT hj2 hj2a hj2w h1 h2, hb2] at hp
      exact ne12 hp.symm)
  have fx2 : ∀ t, a ≤ t → t ≤ w2 → T.x (ex1Buf 2) t = max (X - r2 * (t - a)) 0 := by
    have := traj_drain hT (ex1Buf 2) (ρ := 0) (w := w2) ha le_rfl
      (show (0:ℝ) < 1 / τ 2 by positivity)
      (fun σ h1 h2 => (pw hT hj2 hj2a hj2w h1 h2 _).2 hb2)
      (fun t h1 h2 => by rw [ex1_input2, ex1_input2, hy1 t h1 h2]; ring)
    intro t h1 h2
    rw [this t h1 h2, hx2]; simp only [sub_zero]; rfl
  have fy2 : ∀ t, a ≤ t → t ≤ w2 → T.y (ex1Buf 2) t = T.y (ex1Buf 2) a + X - max (X - r2 * (t - a)) 0 := by
    intro t h1 h2
    have e := bal2 hT ha (ha.trans h1)
    rw [hy1 t h1 h2, hx2, fx2 t h1 h2] at e
    linarith
  have fx2a : ∀ t, a ≤ t → t ≤ a + q4 → max (X - r2 * (t - a)) 0 = X - r2 * (t - a) := by
    intro t h1 h2
    apply max_eq_left
    have : r2 * (t - a) ≤ r2 * q4 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have fx2b : ∀ t, a + q4 ≤ t → max (X - r2 * (t - a)) 0 = 0 := by
    intro t h1
    apply max_eq_right
    have : r2 * q4 ≤ r2 * (t - a) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  -- machine 0 (Lean) is on buffer 4 (Lean `ex1Buf 3`)
  have hb1 : T.β 0 j1 = ex1Buf 3 := by
    rcases ex1_m0 (hroute 0 j1 hj1) with h | h
    swap
    · exact h
    exfalso
    have hP0 : ∀ σ, a ≤ σ → σ < w1 →
        T.Processing ((S2 τ hτ).route (ex1Buf 0)) (ex1Buf 0) σ :=
      fun σ h1 h2 => (pw hT hj1 hj1a hj1w h1 h2 _).2 h
    have dr := traj_drain hT (ex1Buf 0) (ρ := 1) ha zero_le_one (by
        show (1:ℝ) < 1 / τ 0; rw [lt_one_div (by norm_num) ht0]; simpa using (by linarith : τ 0 < 1)) hP0
      (fun t _ _ => by rw [ex1_input0, ex1_input0]; ring)
    set W := min V (a + q4)
    have hWV : W ≤ V := min_le_left _ _
    have hWq : W ≤ a + q4 := min_le_right _ _
    have haW : a < W := lt_min haV (by linarith)
    set t := (a + W) / 2
    have hat : a < t := by simp only [t]; linarith
    have htW : t < W := by simp only [t]; linarith
    apply nx hC hj1 hj1a hj1w hat (lt_of_lt_of_le htW (hWV.trans hV1))
    rw [h]
    refine ⟨?_, ex1Buf 3, rfl, ne03.symm, ?_⟩
    · rw [dr t hat.le (htW.le.trans (hWV.trans hV1)), hx0]
      apply max_eq_right
      have : 0 ≤ (1 / (S2 τ hτ).τ (ex1Buf 0) - 1) * (t - a) := by
        apply mul_nonneg _ (by linarith)
        show 0 ≤ 1 / τ 0 - 1
        rw [sub_nonneg, le_one_div (by norm_num) ht0]; linarith
      linarith
    · apply demanding_of_incr hT _ (by linarith) htW _ (input_mono hT _)
      intro σ h1 h2
      rw [ex1_input3, ex1_input3, fy2 t hat.le (htW.le.trans (hWV.trans hV2)),
        fy2 σ (by linarith) (h2.trans (hWV.trans hV2)), fx2a t hat.le (by linarith),
        fx2a σ (by linarith) (h2.trans hWq)]
      have : r2 * (t - a) < r2 * (σ - a) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
      linarith
  -- formulas in the real case
  have hy0 : ∀ t, a ≤ t → t ≤ w1 → T.y (ex1Buf 0) t = T.y (ex1Buf 0) a :=
    traj_idle hT _ ha (fun σ h1 h2 hp => by
      rw [show (S2 τ hτ).route (ex1Buf 0) = 0 from rfl, pw hT hj1 hj1a hj1w h1 h2, hb1] at hp
      exact ne03 hp.symm)
  have fx0 : ∀ t, a ≤ t → t ≤ w1 → T.x (ex1Buf 0) t = t - a := by
    intro t h1 h2
    have e := bal0 hT ha (ha.trans h1)
    rw [hy0 t h1 h2, hx0] at e; linarith
  have fx1 : ∀ t, a ≤ t → t ≤ V → T.x (ex1Buf 1) t = 0 := by
    intro t h1 h2
    have e := bal1 hT ha (ha.trans h1)
    rw [hy0 t h1 (h2.trans hV1), hy1 t h1 (h2.trans hV2), hx1] at e; linarith
  have hP3 : ∀ σ, a ≤ σ → σ < w1 → T.Processing ((S2 τ hτ).route (ex1Buf 3)) (ex1Buf 3) σ :=
    fun σ h1 h2 => (pw hT hj1 hj1a hj1w h1 h2 _).2 hb1
  have fx3a : ∀ t, a ≤ t → t ≤ min (a + q4) V → T.x (ex1Buf 3) t = (r2 - r3) * (t - a) := by
    have := traj_fill hT (ex1Buf 3) (ρ := r2) (w := min (a + q4) V) ha
      (show 1 / τ 3 < r2 from hr23)
      (fun σ h1 h2 => hP3 σ h1 (lt_of_lt_of_le h2 ((min_le_right _ _).trans hV1)))
      (fun t h1 h2 => by
        have h2' : t ≤ a + q4 := h2.trans (min_le_left _ _)
        have h2'' : t ≤ w2 := h2.trans ((min_le_right _ _).trans hV2)
        rw [ex1_input3, ex1_input3, fy2 t h1 h2'', fy2 a le_rfl haw2.le, fx2a t h1 h2',
          fx2a a le_rfl (by linarith)]
        ring)
    intro t h1 h2
    rw [this t h1 h2, hx3]; simp only [zero_add]; rfl
  have fx3b : ∀ t, a + q4 ≤ t → t ≤ V →
      T.x (ex1Buf 3) t = max (T.x (ex1Buf 3) (a + q4) - r3 * (t - (a + q4))) 0 := by
    have := traj_drain hT (ex1Buf 3) (ρ := 0) (a := a + q4) (w := V) (by linarith) le_rfl
      (show (0:ℝ) < 1 / τ 3 by positivity)
      (fun σ h1 h2 => hP3 σ (by linarith) (lt_of_lt_of_le h2 hV1))
      (fun t h1 h2 => by
        rw [ex1_input3, ex1_input3, fy2 t (by linarith) (h2.trans hV2),
          fy2 (a + q4) (by linarith) ((h1.trans h2).trans hV2), fx2b t h1, fx2b (a + q4) le_rfl]
        ring)
    intro t h1 h2
    rw [this t h1 h2]; simp only [sub_zero]; rfl
  have hx3pos : ∀ t, a < t → t < a + q5 → t ≤ V → 0 < T.x (ex1Buf 3) t := by
    intro t h1 h2 h3
    rcases le_total t (a + q4) with h | h
    · rw [fx3a t h1.le (le_min h h3)]; exact mul_pos (by linarith) (by linarith)
    · rw [fx3b t h h3, fx3a (a + q4) (by linarith) (le_min le_rfl (h.trans h3))]
      apply lt_max_of_lt_left
      have e : (r2 - r3) * (a + q4 - a) = Bv := by rw [hBv]; ring
      have : r3 * (t - (a + q4)) < r3 * (q5 - q4) := mul_lt_mul_of_pos_left (by linarith) hr3pos
      linarith
  have hVq5 : a + q5 ≤ V := by
    by_contra hcon
    push Not at hcon
    rcases le_total w1 w2 with h | h
    · have hVw : V = w1 := min_eq_left h
      obtain ⟨hr, hs⟩ := hw1e (by linarith)
      have := ((hC.2 0 j1 hj1).2 hr).1
      rw [hs, hb1] at this
      have := hx3pos w1 haw1 (by linarith) (by linarith)
      linarith
    · rcases lt_or_eq_of_le h with h' | h'
      · have hVw : V = w2 := min_eq_right h
        obtain ⟨hr, hs⟩ := hw2e (by linarith)
        have hex := ((hC.2 1 j2 hj2).2 hr)
        rw [hs] at hex
        obtain ⟨-, hne, hdem⟩ := hex
        have hb' := ex1_m1 (hroute 1 (j2 + 1) hr)
        rw [hb2] at hne
        rcases hb' with hb' | hb'
        swap
        · exact hne hb'
        rw [hb'] at hdem
        apply notdem (fx1 w2 haw2.le (by rw [hVw])) h' _ hdem
        rw [ex1_input1, ex1_input1, hy0 w2 haw2.le h, hy0 w1 haw1.le le_rfl]
      · have hVw : V = w1 := min_eq_left h'.symm.le
        obtain ⟨hr, hs⟩ := hw1e (by linarith)
        have := ((hC.2 0 j1 hj1).2 hr).1
        rw [hs, hb1] at this
        have := hx3pos w1 haw1 (by linarith) (by linarith)
        linarith
  have haq5 : a ≤ a + q5 := by linarith
  refine ⟨?_, fx1 _ haq5 hVq5, ?_, ?_, ?_, ?_⟩
  · rw [fx0 _ haq5 (hVq5.trans hV1)]; ring
  · rw [fx2 _ haq5 (hVq5.trans hV2), fx2b _ (by linarith)]
  · rw [fx3b _ (by linarith) hVq5, fx3a (a + q4) (by linarith) (le_min le_rfl (by linarith))]
    apply max_eq_right
    have e : (r2 - r3) * (a + q4 - a) = Bv := by rw [hBv]; ring
    have : r3 * (a + q5 - (a + q4)) = r3 * (q5 - q4) := by ring
    linarith
  · exact Or.inr ⟨j1, hj1, hb1, by linarith, fun h => (hVq5.trans hV1).trans (hj1w h)⟩
  · exact Or.inr ⟨j2, hj2, hb2, by linarith, fun h => (hVq5.trans hV2).trans (hj2w h)⟩

end C2
end KSR

namespace KSR
open KumarSeidman.Reentrant

/-- One full magnification cycle of Case 2 from an arbitrary time `a`. -/
theorem case2_cycle {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k}
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    {T : Trajectory (S2 τ hτ)} (hC : IsClearing (S2 τ hτ) T) {a ξ : ℝ} (ha : 0 ≤ a)
    (hξ : 0 < ξ)
    (hx0 : T.x (ex1Buf 0) a = ξ) (hx1 : T.x (ex1Buf 1) a = 0) (hx2 : T.x (ex1Buf 2) a = 0)
    (hx3 : T.x (ex1Buf 3) a = 0) :
    let t₅ := a + (τ 1 + τ 3) * ξ / (1 - τ 1)
    T.x (ex1Buf 0) t₅ = ex1Lambda τ * ξ ∧
    T.x (ex1Buf 1) t₅ = 0 ∧ T.x (ex1Buf 2) t₅ = 0 ∧ T.x (ex1Buf 3) t₅ = 0 ∧
    T.IsSetUpFor 0 t₅ (ex1Buf 3) ∧ T.IsSetUpFor 1 t₅ (ex1Buf 2) := by
  intro t₅
  have h1lt : τ 1 < 1 := by linarith [hτ 2]
  have hne : (1 - τ 1) ≠ 0 := by linarith
  obtain ⟨a0, a1, a2, a3⟩ := phaseA h3 h4 h5 hC ha hξ hx0 hx1 hx2 hx3
  have hp : 0 ≤ ξ * τ 1 / (1 - τ 1) := div_nonneg (mul_nonneg hξ.le (hτ 1).le) (by linarith)
  have hX : 0 < ξ / (1 - τ 1) := div_pos hξ (by linarith)
  have hB := phaseB h3 h4 h5 hC (by linarith) hX a0 a1 a2 a3
  have et : a + ξ * τ 1 / (1 - τ 1) + τ 3 * (ξ / (1 - τ 1)) = t₅ := by
    simp only [t₅]; field_simp; ring
  rw [et] at hB
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hB
  refine ⟨?_, b1, b2, b3, b4, b5⟩
  rw [b0, ex1Lambda]; field_simp

end KSR

open KumarSeidman.Reentrant in
theorem solution (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) (ξ : ℝ) (hξ : 0 < ξ)
    (T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)))
    (hT : IsClearing (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)) T) (h0 : Ex1Initial T ξ) :
    let t₅ := (τ 1 + τ 3) * ξ / (1 - τ 1)
    T.x (ex1Buf 0) t₅ = ex1Lambda τ * ξ ∧
    T.x (ex1Buf 1) t₅ = 0 ∧ T.x (ex1Buf 2) t₅ = 0 ∧ T.x (ex1Buf 3) t₅ = 0 ∧
    T.IsSetUpFor 0 t₅ (ex1Buf 3) ∧ T.IsSetUpFor 1 t₅ (ex1Buf 2) := by
  obtain ⟨i0, i1, i2, i3, -, -⟩ := h0
  have := KSR.case2_cycle (T := T) h3 h4 h5 hT le_rfl hξ i0 i1 i2 i3
  simpa using this

