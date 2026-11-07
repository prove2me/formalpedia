-- Prove2me | solution 1 for KumarSeidman.Reentrant.example1_clearing_unstable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T16:18:19.997207+00:00
-- url     : https://prove2.me/submissions/773a6a7c-ce3e-416f-b2e0-c44da7809508

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1
import Theorems.Thm_KumarSeidman_Reentrant_example1_case1_unstable

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
theorem solution_case2 (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
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


namespace KSR
open KumarSeidman.Reentrant

theorem ex1Lambda_gt_one {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (h3 : 1 < τ 1 + τ 3)
    (h5 : τ 1 + τ 2 < 1) : 1 < ex1Lambda τ := by
  have := hτ 2
  rw [ex1Lambda, lt_div_iff₀ (by linarith)]; linarith

theorem case2_unbounded {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k}
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    {T : Trajectory (S2 τ hτ)} (hC : IsClearing (S2 τ hτ) T) {ξ : ℝ} (hξ : 0 < ξ)
    (h0 : Ex1Initial T ξ) : ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t := by
  have hl := ex1Lambda_gt_one hτ h3 h5
  have key : ∀ n : ℕ, ∃ a : ℝ, 0 ≤ a ∧ T.x (ex1Buf 0) a = ex1Lambda τ ^ n * ξ ∧
      T.x (ex1Buf 1) a = 0 ∧ T.x (ex1Buf 2) a = 0 ∧ T.x (ex1Buf 3) a = 0 := by
    intro n
    induction n with
    | zero => exact ⟨0, le_rfl, by simp [h0.1], h0.2.1, h0.2.2.1, h0.2.2.2.1⟩
    | succ n ih =>
      obtain ⟨a, ha, e0, e1, e2, e3⟩ := ih
      have hpos : 0 < ex1Lambda τ ^ n * ξ := mul_pos (pow_pos (by linarith) n) hξ
      obtain ⟨b0, b1, b2, b3, -, -⟩ := case2_cycle h3 h4 h5 hC ha hpos e0 e1 e2 e3
      refine ⟨_, ?_, ?_, b1, b2, b3⟩
      · have : 0 ≤ (τ 1 + τ 3) * (ex1Lambda τ ^ n * ξ) / (1 - τ 1) :=
          div_nonneg (mul_nonneg (by linarith [hτ 1, hτ 3]) hpos.le) (by linarith [hτ 2])
        linarith
      · rw [b0]; ring
  intro C
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ξ) hl
  obtain ⟨a, ha, e0, -⟩ := key n
  refine ⟨a, ha, ?_⟩
  rw [e0]
  rwa [div_lt_iff₀ hξ] at hn

end KSR


namespace KSR
open KumarSeidman.Reentrant MeasureTheory

/-! ### Segment framework: piecewise-affine functions on a locally finite partition -/

section Seg
variable {b : ℕ → ℝ}

theorem seg_exists (hb0 : b 0 = 0) (hunb : ∀ C, ∃ j, C < b j) {t : ℝ} (ht : 0 ≤ t) :
    ∃ j, b j ≤ t ∧ t < b (j + 1) := by
  classical
  have h : ∃ j, t < b (j + 1) := by
    obtain ⟨j, hj⟩ := hunb t
    cases j with
    | zero => rw [hb0] at hj; linarith
    | succ j => exact ⟨j, hj⟩
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find h) with h0 | h0
  · rw [h0, hb0]; exact ht
  · have := Nat.find_min h (show Nat.pred (Nat.find h) < Nat.find h by omega)
    push Not at this
    rw [h0]; exact this

theorem seg_unique (hmono : StrictMono b) {t : ℝ} {i j : ℕ} (hi : b i ≤ t ∧ t < b (i + 1))
    (hj : b j ≤ t ∧ t < b (j + 1)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : b (i + 1) ≤ b j := hmono.monotone (by omega)
    linarith [hi.2, hj.1]
  · have : b (j + 1) ≤ b i := hmono.monotone (by omega)
    linarith [hi.1, hj.2]

/-- Chain lemma: a function that is monotone on every piece of `[s, t]` cut by the partition is
monotone from `s` to `t`. -/
theorem chain (hb0 : b 0 = 0) (hmono : StrictMono b) (hunb : ∀ C, ∃ j, C < b j) {h : ℝ → ℝ}
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hseg : ∀ j u v, s ≤ u → b j ≤ u → u ≤ v → v ≤ t → v ≤ b (j + 1) → h u ≤ h v) :
    h s ≤ h t := by
  obtain ⟨j0, hj0a, hj0b⟩ := seg_exists hb0 hunb hs
  have key : ∀ k : ℕ, ∀ u, s ≤ u → u ≤ t → u ≤ b (j0 + k + 1) → h s ≤ h u := by
    intro k
    induction k with
    | zero =>
      intro u h1 h2 h3
      exact hseg j0 s u le_rfl hj0a h1 h2 (by simpa using h3)
    | succ k ih =>
      intro u h1 h2 h3
      by_cases hu : u ≤ b (j0 + k + 1)
      · exact ih u h1 h2 hu
      · push Not at hu
        have hv1 : s ≤ b (j0 + k + 1) := by
          have : b (j0 + 1) ≤ b (j0 + k + 1) := hmono.monotone (by omega)
          linarith
        have := ih (b (j0 + k + 1)) hv1 (by linarith) le_rfl
        have h' := hseg (j0 + k + 1) (b (j0 + k + 1)) u hv1 le_rfl hu.le h2
          (by simpa [Nat.add_assoc] using h3)
        linarith
  obtain ⟨J, hJ⟩ := hunb t
  have : b J ≤ b (j0 + J + 1) := hmono.monotone (by omega)
  exact key J t hst le_rfl (by linarith)

/-- Cumulative values of a piecewise-affine function at the breakpoints. -/
def segCum (b sl : ℕ → ℝ) (f0 : ℝ) : ℕ → ℝ
  | 0 => f0
  | j + 1 => segCum b sl f0 j + sl j * (b (j + 1) - b j)

/-- The piecewise-affine function with slopes `sl` on the partition `b`, value `f0` at `b 0`. -/
noncomputable def segFun (b sl : ℕ → ℝ) (f0 : ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ j, b j ≤ t ∧ t < b (j + 1) then
    segCum b sl f0 h.choose + sl h.choose * (t - b h.choose) else f0

theorem segFun_eq (hmono : StrictMono b) (sl : ℕ → ℝ) (f0 : ℝ) {j : ℕ} {t : ℝ}
    (h1 : b j ≤ t) (h2 : t ≤ b (j + 1)) :
    segFun b sl f0 t = segCum b sl f0 j + sl j * (t - b j) := by
  classical
  rcases lt_or_eq_of_le h2 with h2 | h2
  · have hex : ∃ i, b i ≤ t ∧ t < b (i + 1) := ⟨j, h1, h2⟩
    simp only [segFun, dif_pos hex]
    have := seg_unique hmono hex.choose_spec ⟨h1, h2⟩
    rw [this]
  · have hex : ∃ i, b i ≤ t ∧ t < b (i + 1) := ⟨j + 1, by rw [h2], by rw [h2]; exact hmono (by omega)⟩
    simp only [segFun, dif_pos hex]
    have := seg_unique hmono hex.choose_spec ⟨by rw [h2], by rw [h2]; exact hmono (by omega)⟩
    rw [this, h2]
    simp [segCum]

theorem segFun_at (hmono : StrictMono b) (sl : ℕ → ℝ) (f0 : ℝ) (j : ℕ) :
    segFun b sl f0 (b j) = segCum b sl f0 j := by
  rw [segFun_eq hmono sl f0 le_rfl (hmono (Nat.lt_succ_self j)).le]; ring

/-- On a segment, a piecewise-affine function is affine. -/
theorem segFun_diff (hmono : StrictMono b) (sl : ℕ → ℝ) (f0 : ℝ) {j : ℕ} {u v : ℝ}
    (h1 : b j ≤ u) (h2 : v ≤ b (j + 1)) (huv : u ≤ v) :
    segFun b sl f0 v - segFun b sl f0 u = sl j * (v - u) := by
  rw [segFun_eq hmono sl f0 h1 (huv.trans h2), segFun_eq hmono sl f0 (h1.trans huv) h2]; ring

end Seg

section SegTraj
variable {P M : ℕ} {n : Fin P → ℕ} {S : System P M n} {b : ℕ → ℝ}

theorem seg_mono (hb0 : b 0 = 0) (hmono : StrictMono b) (hunb : ∀ C, ∃ j, C < b j)
    {f : ℝ → ℝ} {sl : ℕ → ℝ} (hf : ∀ t, 0 ≤ t → f t = segFun b sl 0 t) (hsl : ∀ j, 0 ≤ sl j) :
    MonotoneOn f (Set.Ici 0) := by
  intro s hs t ht hst
  apply chain hb0 hmono hunb (h := f) hs hst
  intro j u v h1 h2 h3 h4 h5
  rw [hf u (le_trans (Set.mem_Ici.mp hs) h1), hf v (le_trans (Set.mem_Ici.mp hs) (h1.trans h3))]
  have := segFun_diff hmono sl 0 h2 h5 h3
  have : 0 ≤ sl j * (v - u) := mul_nonneg (hsl j) (by linarith)
  linarith

theorem seg_cap (hb0 : b 0 = 0) (hmono : StrictMono b) (hunb : ∀ C, ∃ j, C < b j)
    (T : Trajectory S) (bb : Buffer P n) {sl : ℕ → ℝ}
    (hy : ∀ t, 0 ≤ t → T.y bb t = segFun b sl 0 t)
    (hsl : ∀ j, 0 ≤ sl j ∧ sl j ≤ 1 / S.τ bb)
    (hP : ∀ j, 0 < sl j → ∀ σ, b j < σ → σ < b (j + 1) → T.Processing (S.route bb) bb σ) :
    ∀ s t, 0 ≤ s → s ≤ t → T.y bb t - T.y bb s ≤
      (volume (Set.Icc s t ∩ {σ | T.Processing (S.route bb) bb σ})).toReal / S.τ bb := by
  intro s t hs hst
  have hτ := S.τ_pos bb
  set Pr := {σ | T.Processing (S.route bb) bb σ}
  set H : ℝ → ℝ := fun u => (volume (Set.Icc s u ∩ Pr)).toReal
  have hfin : ∀ u, volume (Set.Icc s u ∩ Pr) ≠ ⊤ := fun u =>
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_left)
  have hc := chain hb0 hmono hunb (h := fun u => H u / S.τ bb - T.y bb u) hs hst (by
    intro j u v h1 h2 h3 h4 h5
    have hdy : T.y bb v - T.y bb u = sl j * (v - u) := by
      rw [hy u (hs.trans h1), hy v (hs.trans (h1.trans h3))]
      exact segFun_diff hmono sl 0 h2 h5 h3
    have hHm : H u ≤ H v := ENNReal.toReal_mono (hfin v)
      (measure_mono (Set.inter_subset_inter_left _ (Set.Icc_subset_Icc le_rfl h3)))
    rcases (hsl j).1.lt_or_eq with hpos | hzero
    · have hsub : Set.Ioo u v ⊆ Pr := fun σ hσ =>
        hP j hpos σ (lt_of_le_of_lt h2 hσ.1) (lt_of_lt_of_le hσ.2 h5)
      have hdisj : Disjoint (Set.Icc s u ∩ Pr) (Set.Ioo u v) := by
        rw [Set.disjoint_left]
        rintro σ ⟨⟨_, hσ⟩, _⟩ ⟨hσ', _⟩
        linarith
      have hunion : (Set.Icc s u ∩ Pr) ∪ Set.Ioo u v ⊆ Set.Icc s v ∩ Pr := by
        rintro σ (⟨⟨h1', h2'⟩, h3'⟩ | hσ)
        · exact ⟨⟨h1', h2'.trans h3⟩, h3'⟩
        · exact ⟨⟨by linarith [hσ.1], hσ.2.le⟩, hsub hσ⟩
      have hm := measure_mono (μ := volume) hunion
      rw [measure_union hdisj measurableSet_Ioo, Real.volume_Ioo] at hm
      have hm2 := ENNReal.toReal_mono (hfin v) hm
      rw [ENNReal.toReal_add (hfin u) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith)] at hm2
      have : sl j * (v - u) ≤ (1 / S.τ bb) * (v - u) :=
        mul_le_mul_of_nonneg_right (hsl j).2 (by linarith)
      have e : (H v - H u) / S.τ bb ≥ (1 / S.τ bb) * (v - u) := by
        have hh : v - u ≤ H v - H u := by linarith
        rw [ge_iff_le, div_eq_mul_one_div (H v - H u), mul_comm (H v - H u)]
        exact mul_le_mul_of_nonneg_left hh (by positivity)
      have : H v / S.τ bb - H u / S.τ bb = (H v - H u) / S.τ bb := by ring
      linarith
    · rw [← hzero] at hdy
      have : H u / S.τ bb ≤ H v / S.τ bb := div_le_div_of_nonneg_right hHm hτ.le
      linarith)
  have : 0 ≤ H s / S.τ bb := div_nonneg ENNReal.toReal_nonneg hτ.le
  simp only [H] at hc this ⊢
  linarith

theorem seg_full (hb0 : b 0 = 0) (hmono : StrictMono b) (hunb : ∀ C, ∃ j, C < b j)
    (T : Trajectory S) (bb : Buffer P n) {sl : ℕ → ℝ}
    (hy : ∀ t, 0 ≤ t → T.y bb t = segFun b sl 0 t)
    (hfs : ∀ j σ, b j < σ → σ < b (j + 1) → T.Processing (S.route bb) bb σ → 0 < T.x bb σ →
      sl j = 1 / S.τ bb) :
    ∀ s t, 0 ≤ s → s ≤ t →
      (∀ σ ∈ Set.Ico s t, T.Processing (S.route bb) bb σ ∧ 0 < T.x bb σ) →
      T.y bb t - T.y bb s = (t - s) / S.τ bb := by
  intro s t hs hst hall
  have hseg : ∀ j u v, s ≤ u → b j ≤ u → u ≤ v → v ≤ t → v ≤ b (j + 1) →
      T.y bb v - T.y bb u = (1 / S.τ bb) * (v - u) := by
    intro j u v h1 h2 h3 h4 h5
    rw [hy u (hs.trans h1), hy v (hs.trans (h1.trans h3)), segFun_diff hmono sl 0 h2 h5 h3]
    rcases lt_or_eq_of_le h3 with h3 | h3
    · have hσ := hall ((u + v) / 2) ⟨by linarith, by linarith⟩
      rw [hfs j ((u + v) / 2) (by linarith) (by linarith) hσ.1 hσ.2]
    · rw [h3]; ring
  have c1 := chain hb0 hmono hunb (h := fun u => T.y bb u - (1 / S.τ bb) * u) hs hst (by
    intro j u v h1 h2 h3 h4 h5
    have := hseg j u v h1 h2 h3 h4 h5
    linarith)
  have c2 := chain hb0 hmono hunb (h := fun u => (1 / S.τ bb) * u - T.y bb u) hs hst (by
    intro j u v h1 h2 h3 h4 h5
    have := hseg j u v h1 h2 h3 h4 h5
    linarith)
  have : (t - s) / S.τ bb = (1 / S.τ bb) * t - (1 / S.τ bb) * s := by ring
  linarith

end SegTraj

end KSR

namespace KSR
open KumarSeidman.Reentrant

theorem processing_iff' {P M : ℕ} {n : Fin P → ℕ} {S : System P M n} {T : Trajectory S}
    {m : Fin M} (hsm : ∀ i j, i ≤ j → T.RunExists m j → T.s m i ≤ T.s m j) {k : ℕ}
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
      have := hsm (j + 1) k hjk hk
      linarith
    · subst hjk; exact ⟨hjb, hjs⟩
    · exfalso
      have hk1 : T.RunExists m (k + 1) := runExists_mono hjk hj
      have := hkw hk1
      have := hsm (k + 1) j hjk hj
      have := s_le_procStart T m j
      linarith
  · rintro ⟨hb, hs⟩
    exact ⟨k, hk, hb, hs, fun h => lt_of_lt_of_le h2 (hkw h)⟩

/-- Sign of an affine function on an interval from its endpoint values. -/
theorem aff_nonneg {f : ℝ → ℝ} {p q c : ℝ} (hpq : p ≤ q)
    (hf : ∀ t, p ≤ t → t ≤ q → f t = f p + c * (t - p)) (hp : 0 ≤ f p) (hq : 0 ≤ f q) :
    ∀ t, p ≤ t → t ≤ q → 0 ≤ f t := by
  intro t h1 h2
  rw [hf t h1 h2]
  have eq := hf q hpq le_rfl
  rcases le_total 0 c with hc | hc
  · nlinarith
  · nlinarith

theorem aff_pos {f : ℝ → ℝ} {p q c : ℝ}
    (hf : ∀ t, p ≤ t → t ≤ q → f t = f p + c * (t - p)) (hp : 0 ≤ f p) (hq : 0 ≤ f q)
    (hpos : 0 < f p ∨ 0 < f q) : ∀ t, p < t → t < q → 0 < f t := by
  intro t h1 h2
  rw [hf t h1.le h2.le]
  have eq := hf q (h1.trans h2).le le_rfl
  rcases hpos with h | h
  · rcases le_total 0 c with hc | hc
    · nlinarith
    · rcases lt_or_eq_of_le hc with hc' | hc'
      · have : c * (q - p) < c * (t - p) := mul_lt_mul_of_neg_left (by linarith) hc'
        linarith
      · rw [hc']; linarith
  · rcases le_total 0 c with hc | hc
    · rcases lt_or_eq_of_le hc with hc' | hc'
      · have : 0 < c * (t - p) := mul_pos hc' (by linarith)
        nlinarith
      · rw [← hc'] at eq ⊢; linarith
    · nlinarith

theorem aff_zero {f : ℝ → ℝ} {p q c : ℝ} (hpq : p < q)
    (hf : ∀ t, p ≤ t → t ≤ q → f t = f p + c * (t - p)) (hp : f p = 0) (hq : f q = 0) :
    ∀ t, p ≤ t → t ≤ q → f t = 0 := by
  intro t h1 h2
  have eq := hf q hpq.le le_rfl
  rw [hp, hq] at eq
  have hc : c = 0 := by
    have : c * (q - p) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · linarith
  rw [hf t h1 h2, hp, hc]; ring

end KSR


namespace KSR
open KumarSeidman.Reentrant

namespace C2E

variable (τ : Fin 4 → ℝ) (ξ : ℝ)

noncomputable def kap : ℝ := (τ 1 + τ 3) / (1 - τ 1)
noncomputable def Kc : ℝ := 1 / (1 - τ 1)

/-- Normalised breakpoints of one cycle. -/
noncomputable def Uf : ℕ → ℝ
  | 0 => 0
  | 1 => τ 0 / (1 - τ 0)
  | 2 => τ 1 / (1 - τ 1)
  | 3 => τ 1 / (1 - τ 1) + τ 2 / (1 - τ 1)
  | _ => kap τ

noncomputable def cyc (n : ℕ) : ℝ := ξ * ex1Lambda τ ^ n

noncomputable def ast : ℕ → ℝ
  | 0 => 0
  | n + 1 => ast n + kap τ * cyc τ ξ n

noncomputable def Ssum : ℕ → ℝ
  | 0 => 0
  | n + 1 => Ssum n + cyc τ ξ n

noncomputable def bk (j : ℕ) : ℝ := ast τ ξ (j / 4) + cyc τ ξ (j / 4) * Uf τ (j % 4)

/-- Output slopes of buffer `i` in the `k`-th segment of a cycle. -/
noncomputable def osl (i : Fin 4) (k : ℕ) : ℝ :=
  match i, k with
  | 0, 0 => 1 / τ 0
  | 0, 1 => 1
  | 1, 0 => 1 / τ 1
  | 1, 1 => 1 / τ 1
  | 2, 2 => 1 / τ 2
  | 3, 2 => 1 / τ 3
  | 3, 3 => 1 / τ 3
  | _, _ => 0

/-- Normalised cumulative output of buffer `i` at the `k`-th breakpoint of a cycle. -/
noncomputable def Yc (i : Fin 4) : ℕ → ℝ
  | 0 => 0
  | k + 1 => Yc i k + osl τ i k * (Uf τ (k + 1) - Uf τ k)

end C2E

section C2Pure
variable {τ : Fin 4 → ℝ} {ξ : ℝ}
open C2E


theorem kap_eq : kap τ = Uf τ 4 := rfl

theorem ast_eq (n : ℕ) : ast τ ξ n = kap τ * Ssum τ ξ n := by
  induction n with
  | zero => simp [ast, Ssum]
  | succ n ih => simp only [ast, Ssum, ih]; ring

theorem bk_cyc (n k : ℕ) (hk : k < 4) :
    bk τ ξ (4 * n + k) = ast τ ξ n + cyc τ ξ n * Uf τ k := by
  simp only [bk]
  have e1 : (4 * n + k) / 4 = n := by omega
  have e2 : (4 * n + k) % 4 = k := by omega
  rw [e1, e2]

theorem bk_step (n k : ℕ) (hk : k ≤ 3) :
    bk τ ξ (4 * n + k + 1) - bk τ ξ (4 * n + k) = cyc τ ξ n * (Uf τ (k + 1) - Uf τ k) := by
  rcases Nat.lt_or_ge k 3 with h | h
  · rw [show 4 * n + k + 1 = 4 * n + (k + 1) by ring, bk_cyc (τ := τ) (ξ := ξ) n (k + 1) (by omega),
      bk_cyc (τ := τ) (ξ := ξ) n k (by omega)]
    ring
  · obtain rfl : k = 3 := by omega
    rw [show 4 * n + 3 + 1 = 4 * (n + 1) + 0 by ring, bk_cyc (τ := τ) (ξ := ξ) (n + 1) 0 (by omega),
      bk_cyc (τ := τ) (ξ := ξ) n 3 (by omega)]
    simp only [ast, Uf, kap]
    ring

theorem bk_zero : bk τ ξ 0 = 0 := by simp [bk, ast, Uf]

theorem cyc_succ (n : ℕ) : cyc τ ξ (n + 1) = ex1Lambda τ * cyc τ ξ n := by
  simp only [cyc, pow_succ]; ring

end C2Pure

section C2Enum
variable {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ}
include hτ h3 h4 h5

open C2E

theorem c2_basic : τ 0 < τ 1 ∧ τ 2 < τ 3 ∧ τ 0 < 1 ∧ τ 1 < 1 ∧ τ 2 < 1 ∧ τ 3 < 1 := by
  have := hτ 0; have := hτ 1; have := hτ 2; have := hτ 3
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem Uf_lt : Uf τ 0 < Uf τ 1 ∧ Uf τ 1 < Uf τ 2 ∧ Uf τ 2 < Uf τ 3 ∧ Uf τ 3 < Uf τ 4 := by
  obtain ⟨h01, h23, h0, h1, h2, h3'⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  simp only [Uf, kap]
  refine ⟨div_pos t0 (by linarith), ?_, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · have : 0 < τ 2 / (1 - τ 1) := div_pos t2 (by linarith)
    linarith
  · rw [← add_div, div_lt_div_iff_of_pos_right (by linarith)]; linarith

theorem lam_gt : 1 < ex1Lambda τ := ex1Lambda_gt_one hτ h3 h5

theorem cyc_pos (hξ : 0 < ξ) (n : ℕ) : 0 < cyc τ ξ n := by
  have := lam_gt hτ h3 h4 h5
  exact mul_pos hξ (pow_pos (by linarith) n)

theorem cyc_ge (hξ : 0 < ξ) (n : ℕ) : ξ ≤ cyc τ ξ n := by
  have := lam_gt hτ h3 h4 h5
  have : 1 ≤ ex1Lambda τ ^ n := one_le_pow₀ (by linarith)
  simp only [cyc]; nlinarith

theorem kap_pos : 0 < kap τ := by
  obtain ⟨-, -, -, h1, -, -⟩ := c2_basic hτ h3 h4 h5
  exact div_pos (by linarith [hτ 1, hτ 3]) (by linarith)

theorem cyc_eq (hξ : 0 < ξ) (n : ℕ) : cyc τ ξ n = ξ + (ex1Lambda τ - 1) * Ssum τ ξ n := by
  induction n with
  | zero => simp [cyc, Ssum]
  | succ n ih =>
    rw [cyc_succ]
    simp only [Ssum]
    rw [ih]
    have : cyc τ ξ n = ξ + (ex1Lambda τ - 1) * Ssum τ ξ n := ih
    nlinarith [this]

theorem ast_ge (hξ : 0 < ξ) (n : ℕ) : (n : ℝ) * (kap τ * ξ) ≤ ast τ ξ n := by
  induction n with
  | zero => simp [ast]
  | succ n ih =>
    simp only [ast]
    have := cyc_ge hτ h3 h4 h5 hξ n
    have := kap_pos hτ h3 h4 h5
    push_cast
    nlinarith

theorem bk_mono (hξ : 0 < ξ) : StrictMono (bk τ ξ) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hj : j = 4 * (j / 4) + j % 4 := (Nat.div_add_mod j 4).symm
  have hr : j % 4 ≤ 3 := by omega
  have := bk_step (τ := τ) (ξ := ξ) (j / 4) (j % 4) hr
  rw [← hj] at this
  have hc := cyc_pos hτ h3 h4 h5 hξ (j / 4)
  obtain ⟨u1, u2, u3, u4⟩ := Uf_lt hτ h3 h4 h5
  have hU' : ∀ r, r ≤ 3 → Uf τ r < Uf τ (r + 1) := by
    intro r hr
    interval_cases r
    exacts [u1, u2, u3, u4]
  have hU := hU' (j % 4) hr
  have : 0 < cyc τ ξ (j / 4) * (Uf τ (j % 4 + 1) - Uf τ (j % 4)) := mul_pos hc (by linarith)
  linarith

theorem bk_unb (hξ : 0 < ξ) : ∀ C, ∃ j, C < bk τ ξ j := by
  intro C
  have hk := mul_pos (kap_pos hτ h3 h4 h5) hξ
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (kap τ * ξ))
  refine ⟨4 * n, ?_⟩
  rw [show 4 * n = 4 * n + 0 by ring, bk_cyc (τ := τ) (ξ := ξ) n 0 (by omega)]
  simp only [Uf, mul_zero, add_zero]
  have := ast_ge hτ h3 h4 h5 hξ n
  rw [div_lt_iff₀ hk] at hn
  linarith


theorem Yc4 (i : Fin 4) : Yc τ i 4 = Kc τ := by
  obtain ⟨h01, h23, h0, h1, h2, h3'⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have n0 : (1 - τ 0) ≠ 0 := by linarith
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  fin_cases i <;> simp [Yc, osl, Uf, kap, Kc] <;> field_simp <;> ring

theorem kap_Kc : kap τ - Kc τ = ex1Lambda τ - 1 := by
  obtain ⟨h01, h23, h0, h1, h2, h3'⟩ := c2_basic hτ h3 h4 h5
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  simp only [kap, Kc, ex1Lambda]; field_simp; ring

theorem segCum_eq (i : Fin 4) (j : ℕ) :
    segCum (bk τ ξ) (fun j => osl τ i (j % 4)) 0 j =
      Kc τ * Ssum τ ξ (j / 4) + cyc τ ξ (j / 4) * Yc τ i (j % 4) := by
  induction j with
  | zero => simp [segCum, Ssum, Yc]
  | succ j ih =>
    simp only [segCum]
    rw [ih]
    have hj : j = 4 * (j / 4) + j % 4 := (Nat.div_add_mod j 4).symm
    have hst := bk_step (τ := τ) (ξ := ξ) (j / 4) (j % 4) (by omega)
    rw [← hj] at hst
    rw [hst]
    rcases Nat.lt_or_ge (j % 4) 3 with h | h
    · have e1 : (j + 1) / 4 = j / 4 := by omega
      have e2 : (j + 1) % 4 = j % 4 + 1 := by omega
      rw [e1, e2]
      simp only [Yc]; ring
    · have e1 : (j + 1) / 4 = j / 4 + 1 := by omega
      have e2 : (j + 1) % 4 = 0 := by omega
      have e3 : j % 4 = 3 := by omega
      rw [e1, e2, e3]
      have := Yc4 hτ h3 h4 h5 i
      simp only [Yc] at this
      simp only [Yc, Ssum]
      rw [show (3 : ℕ) + 1 = 4 by rfl] at *
      rw [← this]
      ring

end C2Enum


namespace C2E
noncomputable def yf (τ : Fin 4 → ℝ) (ξ : ℝ) (i : Fin 4) (t : ℝ) : ℝ :=
  segFun (bk τ ξ) (fun j => osl τ i (j % 4)) 0 t

def βf (m : Fin 2) (k : ℕ) : Ex1Buffer :=
  if k % 2 = 1 then (if m = 0 then ex1Buf 0 else ex1Buf 1)
  else (if m = 0 then ex1Buf 3 else ex1Buf 2)

noncomputable def sf (τ : Fin 4 → ℝ) (ξ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else bk τ ξ (2 * (k - 1))

noncomputable def traj (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k) (ξ : ℝ) : Trajectory (S2 τ hτ) where
  x b t := (if b.2 = 0 then ξ else 0) + (S2 τ hτ).input (fun b' => yf τ ξ b'.2) b t - yf τ ξ b.2 t
  y b := yf τ ξ b.2
  N _ := ⊤
  β := βf
  s _ k := sf τ ξ k
end C2E

open C2E


section C2Traj
variable {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k} {ξ : ℝ}

theorem tx0 (t : ℝ) : (traj τ hτ ξ).x (ex1Buf 0) t = ξ + t - yf τ ξ 0 t := by
  simp only [traj]; rw [ex1_input0]; simp [ex1Buf]
theorem tx1 (t : ℝ) : (traj τ hτ ξ).x (ex1Buf 1) t = yf τ ξ 0 t - yf τ ξ 1 t := by
  simp only [traj]; rw [ex1_input1]; simp [ex1Buf]
theorem tx2 (t : ℝ) : (traj τ hτ ξ).x (ex1Buf 2) t = yf τ ξ 1 t - yf τ ξ 2 t := by
  simp only [traj]; rw [ex1_input2]; simp [ex1Buf]
theorem tx3 (t : ℝ) : (traj τ hτ ξ).x (ex1Buf 3) t = yf τ ξ 2 t - yf τ ξ 3 t := by
  simp only [traj]; rw [ex1_input3]; simp [ex1Buf]
theorem ty (b : Ex1Buffer) : (traj τ hτ ξ).y b = yf τ ξ b.2 := rfl
theorem ts (m : Fin 2) (k : ℕ) : (traj τ hτ ξ).s m k = sf τ ξ k := rfl
theorem tβ (m : Fin 2) (k : ℕ) : (traj τ hτ ξ).β m k = βf m k := rfl

end C2Traj

section C2Vals
variable {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
include hτ h3 h4 h5 hξ

theorem yf_bk (i : Fin 4) (n k : ℕ) (hk : k < 4) :
    yf τ ξ i (bk τ ξ (4 * n + k)) = Kc τ * Ssum τ ξ n + cyc τ ξ n * Yc τ i k := by
  simp only [yf]
  rw [segFun_at (bk_mono hτ h3 h4 h5 hξ), segCum_eq hτ h3 h4 h5]
  have e1 : (4 * n + k) / 4 = n := by omega
  have e2 : (4 * n + k) % 4 = k := by omega
  rw [e1, e2]

theorem yf_aff (i : Fin 4) (j : ℕ) {t : ℝ} (h1 : bk τ ξ j ≤ t) (h2 : t ≤ bk τ ξ (j + 1)) :
    yf τ ξ i t = yf τ ξ i (bk τ ξ j) + osl τ i (j % 4) * (t - bk τ ξ j) := by
  simp only [yf]
  rw [segFun_eq (bk_mono hτ h3 h4 h5 hξ) _ 0 h1 h2, segFun_at (bk_mono hτ h3 h4 h5 hξ)]

/-- The common affine identity behind all buffer values. -/
theorem base_id (n : ℕ) :
    ξ + ast τ ξ n - Kc τ * Ssum τ ξ n = cyc τ ξ n := by
  rw [ast_eq, cyc_eq hτ h3 h4 h5 hξ, ← kap_Kc hτ h3 h4 h5]; ring

theorem xv0 (n k : ℕ) (hk : k < 4) :
    (traj τ hτ ξ).x (ex1Buf 0) (bk τ ξ (4 * n + k)) = cyc τ ξ n * (1 + Uf τ k - Yc τ 0 k) := by
  rw [tx0, yf_bk hτ h3 h4 h5 hξ 0 n k hk, bk_cyc n k hk]
  have := base_id hτ h3 h4 h5 hξ n
  linear_combination this
theorem xv1 (n k : ℕ) (hk : k < 4) :
    (traj τ hτ ξ).x (ex1Buf 1) (bk τ ξ (4 * n + k)) = cyc τ ξ n * (Yc τ 0 k - Yc τ 1 k) := by
  rw [tx1, yf_bk hτ h3 h4 h5 hξ 0 n k hk, yf_bk hτ h3 h4 h5 hξ 1 n k hk]; ring
theorem xv2 (n k : ℕ) (hk : k < 4) :
    (traj τ hτ ξ).x (ex1Buf 2) (bk τ ξ (4 * n + k)) = cyc τ ξ n * (Yc τ 1 k - Yc τ 2 k) := by
  rw [tx2, yf_bk hτ h3 h4 h5 hξ 1 n k hk, yf_bk hτ h3 h4 h5 hξ 2 n k hk]; ring
theorem xv3 (n k : ℕ) (hk : k < 4) :
    (traj τ hτ ξ).x (ex1Buf 3) (bk τ ξ (4 * n + k)) = cyc τ ξ n * (Yc τ 2 k - Yc τ 3 k) := by
  rw [tx3, yf_bk hτ h3 h4 h5 hξ 2 n k hk, yf_bk hτ h3 h4 h5 hξ 3 n k hk]; ring

end C2Vals


section C2Tab
variable {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
include hτ h3 h4 h5

theorem tab :
    (1 + Uf τ 0 - Yc τ 0 0 = 1 ∧ 1 + Uf τ 1 - Yc τ 0 1 = 0 ∧ 1 + Uf τ 2 - Yc τ 0 2 = 0 ∧
      0 < 1 + Uf τ 3 - Yc τ 0 3) ∧
    (Yc τ 0 0 - Yc τ 1 0 = 0 ∧ 0 < Yc τ 0 1 - Yc τ 1 1 ∧ Yc τ 0 2 - Yc τ 1 2 = 0 ∧
      Yc τ 0 3 - Yc τ 1 3 = 0) ∧
    (Yc τ 1 0 - Yc τ 2 0 = 0 ∧ 0 < Yc τ 1 1 - Yc τ 2 1 ∧ 0 < Yc τ 1 2 - Yc τ 2 2 ∧
      Yc τ 1 3 - Yc τ 2 3 = 0) ∧
    (Yc τ 2 0 - Yc τ 3 0 = 0 ∧ Yc τ 2 1 - Yc τ 3 1 = 0 ∧ Yc τ 2 2 - Yc τ 3 2 = 0 ∧
      0 < Yc τ 2 3 - Yc τ 3 3) := by
  obtain ⟨h01, h23, h0, h1, h2, h3'⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have n0 : (1 - τ 0) ≠ 0 := by linarith
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  have p0 : 0 < 1 - τ 0 := by linarith
  have p1 : 0 < 1 - τ 1 := by linarith
  simp only [Yc, osl, Uf]
  refine ⟨⟨by ring, by field_simp; ring, by field_simp; ring, ?_⟩,
    ⟨by ring, ?_, by field_simp; ring, by field_simp; ring⟩,
    ⟨by ring, ?_, ?_, by field_simp; ring⟩, ⟨by ring, by ring, by ring, ?_⟩⟩
  · have : 0 < τ 2 / (1 - τ 1) := div_pos t2 p1
    have e : 1 + (τ 1 / (1 - τ 1) + τ 2 / (1 - τ 1)) -
      (0 + 1 / τ 0 * (τ 0 / (1 - τ 0) - 0) + 1 * (τ 1 / (1 - τ 1) - τ 0 / (1 - τ 0)) +
        0 * (τ 1 / (1 - τ 1) + τ 2 / (1 - τ 1) - τ 1 / (1 - τ 1))) = τ 2 / (1 - τ 1) := by
      field_simp; ring
    linarith
  · have e : 0 + 1 / τ 0 * (τ 0 / (1 - τ 0) - 0) - (0 + 1 / τ 1 * (τ 0 / (1 - τ 0) - 0)) =
        (τ 0 / (1 - τ 0)) * (1 / τ 0 - 1 / τ 1) := by ring
    rw [e]
    exact mul_pos (div_pos t0 p0) (by rw [sub_pos]; exact one_div_lt_one_div_of_lt t0 h01)
  · have e : 0 + 1 / τ 1 * (τ 0 / (1 - τ 0) - 0) - (0 + 0 * (τ 0 / (1 - τ 0) - 0)) =
        1 / τ 1 * (τ 0 / (1 - τ 0)) := by ring
    rw [e]; positivity
  · have e : 0 + 1 / τ 1 * (τ 0 / (1 - τ 0) - 0) + 1 / τ 1 * (τ 1 / (1 - τ 1) - τ 0 / (1 - τ 0)) -
        (0 + 0 * (τ 0 / (1 - τ 0) - 0) + 0 * (τ 1 / (1 - τ 1) - τ 0 / (1 - τ 0))) =
        1 / (1 - τ 1) := by field_simp; ring
    rw [e]; positivity
  · have e : 0 + 0 * (τ 0 / (1 - τ 0) - 0) + 0 * (τ 1 / (1 - τ 1) - τ 0 / (1 - τ 0)) +
        1 / τ 2 * (τ 1 / (1 - τ 1) + τ 2 / (1 - τ 1) - τ 1 / (1 - τ 1)) -
        (0 + 0 * (τ 0 / (1 - τ 0) - 0) + 0 * (τ 1 / (1 - τ 1) - τ 0 / (1 - τ 0)) +
          1 / τ 3 * (τ 1 / (1 - τ 1) + τ 2 / (1 - τ 1) - τ 1 / (1 - τ 1))) =
        (τ 2 / (1 - τ 1)) * (1 / τ 2 - 1 / τ 3) := by ring
    rw [e]
    exact mul_pos (div_pos t2 p1) (by rw [sub_pos]; exact one_div_lt_one_div_of_lt t2 h23)

end C2Tab


section C2X
variable {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
include hτ h3 h4 h5 hξ

theorem bk4 (n : ℕ) : bk τ ξ (4 * (n + 1)) = bk τ ξ (4 * n + 3 + 1) := by ring_nf

/-- Values of the buffers at the breakpoints of cycle `n`. -/
theorem xtab (n : ℕ) :
    ((traj τ hτ ξ).x (ex1Buf 0) (bk τ ξ (4 * n)) = cyc τ ξ n ∧
      (traj τ hτ ξ).x (ex1Buf 0) (bk τ ξ (4 * n + 1)) = 0 ∧
      (traj τ hτ ξ).x (ex1Buf 0) (bk τ ξ (4 * n + 2)) = 0 ∧
      0 < (traj τ hτ ξ).x (ex1Buf 0) (bk τ ξ (4 * n + 3))) ∧
    ((traj τ hτ ξ).x (ex1Buf 1) (bk τ ξ (4 * n)) = 0 ∧
      0 < (traj τ hτ ξ).x (ex1Buf 1) (bk τ ξ (4 * n + 1)) ∧
      (traj τ hτ ξ).x (ex1Buf 1) (bk τ ξ (4 * n + 2)) = 0 ∧
      (traj τ hτ ξ).x (ex1Buf 1) (bk τ ξ (4 * n + 3)) = 0) ∧
    ((traj τ hτ ξ).x (ex1Buf 2) (bk τ ξ (4 * n)) = 0 ∧
      0 < (traj τ hτ ξ).x (ex1Buf 2) (bk τ ξ (4 * n + 1)) ∧
      0 < (traj τ hτ ξ).x (ex1Buf 2) (bk τ ξ (4 * n + 2)) ∧
      (traj τ hτ ξ).x (ex1Buf 2) (bk τ ξ (4 * n + 3)) = 0) ∧
    ((traj τ hτ ξ).x (ex1Buf 3) (bk τ ξ (4 * n)) = 0 ∧
      (traj τ hτ ξ).x (ex1Buf 3) (bk τ ξ (4 * n + 1)) = 0 ∧
      (traj τ hτ ξ).x (ex1Buf 3) (bk τ ξ (4 * n + 2)) = 0 ∧
      0 < (traj τ hτ ξ).x (ex1Buf 3) (bk τ ξ (4 * n + 3))) := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ :=
    tab hτ h3 h4 h5
  have hc := cyc_pos hτ h3 h4 h5 hξ n
  have e0 : 4 * n = 4 * n + 0 := rfl
  rw [e0, xv0 hτ h3 h4 h5 hξ n 0 (by omega), xv0 hτ h3 h4 h5 hξ n 1 (by omega),
    xv0 hτ h3 h4 h5 hξ n 2 (by omega), xv0 hτ h3 h4 h5 hξ n 3 (by omega),
    xv1 hτ h3 h4 h5 hξ n 0 (by omega), xv1 hτ h3 h4 h5 hξ n 1 (by omega),
    xv1 hτ h3 h4 h5 hξ n 2 (by omega), xv1 hτ h3 h4 h5 hξ n 3 (by omega),
    xv2 hτ h3 h4 h5 hξ n 0 (by omega), xv2 hτ h3 h4 h5 hξ n 1 (by omega),
    xv2 hτ h3 h4 h5 hξ n 2 (by omega), xv2 hτ h3 h4 h5 hξ n 3 (by omega),
    xv3 hτ h3 h4 h5 hξ n 0 (by omega), xv3 hτ h3 h4 h5 hξ n 1 (by omega),
    xv3 hτ h3 h4 h5 hξ n 2 (by omega), xv3 hτ h3 h4 h5 hξ n 3 (by omega),
    a0, a1, a2, b0, b2, b3, c0, c3, d0, d1, d2]
  refine ⟨⟨by ring, by ring, by ring, mul_pos hc a3⟩, ⟨by ring, mul_pos hc b1, by ring, by ring⟩,
    ⟨by ring, mul_pos hc c1, mul_pos hc c2, by ring⟩, ⟨by ring, by ring, by ring, mul_pos hc d3⟩⟩

theorem xbk_nn (b : Ex1Buffer) (j : ℕ) : 0 ≤ (traj τ hτ ξ).x b (bk τ ξ j) := by
  have hj : j = 4 * (j / 4) + j % 4 := (Nat.div_add_mod j 4).symm
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ :=
    xtab hτ h3 h4 h5 hξ (j / 4)
  have hc := cyc_pos hτ h3 h4 h5 hξ (j / 4)
  rw [ex1_buf_eq b, hj]
  generalize j / 4 = n at *
  have hr : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize j % 4 = r at *
  generalize b.2 = i
  interval_cases r <;> fin_cases i <;> simp_all <;> linarith

theorem xaff (b : Ex1Buffer) (j : ℕ) : ∃ c : ℝ, ∀ t, bk τ ξ j ≤ t → t ≤ bk τ ξ (j + 1) →
    (traj τ hτ ξ).x b t = (traj τ hτ ξ).x b (bk τ ξ j) + c * (t - bk τ ξ j) := by
  have hb := (bk_mono hτ h3 h4 h5 hξ) (Nat.lt_succ_self j)
  have A := fun i t (h1 : bk τ ξ j ≤ t) (h2 : t ≤ bk τ ξ (j + 1)) =>
    yf_aff hτ h3 h4 h5 hξ i j h1 h2
  have B := fun i => yf_aff hτ h3 h4 h5 hξ i j le_rfl hb.le
  rw [ex1_buf_eq b]
  generalize b.2 = i
  fin_cases i
  · refine ⟨1 - osl τ 0 (j % 4), fun t h1 h2 => ?_⟩
    simp only [Fin.zero_eta]
    rw [tx0, tx0, A 0 t h1 h2]; ring
  · refine ⟨osl τ 0 (j % 4) - osl τ 1 (j % 4), fun t h1 h2 => ?_⟩
    simp only [Fin.mk_one]
    rw [tx1, tx1, A 0 t h1 h2, A 1 t h1 h2]; ring
  · refine ⟨osl τ 1 (j % 4) - osl τ 2 (j % 4), fun t h1 h2 => ?_⟩
    show (traj τ hτ ξ).x (ex1Buf 2) t = (traj τ hτ ξ).x (ex1Buf 2) (bk τ ξ j) + _
    rw [tx2, tx2, A 1 t h1 h2, A 2 t h1 h2]; ring
  · refine ⟨osl τ 2 (j % 4) - osl τ 3 (j % 4), fun t h1 h2 => ?_⟩
    show (traj τ hτ ξ).x (ex1Buf 3) t = (traj τ hτ ξ).x (ex1Buf 3) (bk τ ξ j) + _
    rw [tx3, tx3, A 2 t h1 h2, A 3 t h1 h2]; ring

theorem x_nn (b : Ex1Buffer) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ (traj τ hτ ξ).x b t := by
  obtain ⟨j, h1, h2⟩ := seg_exists bk_zero (bk_unb hτ h3 h4 h5 hξ) ht
  obtain ⟨c, hc⟩ := xaff hτ h3 h4 h5 hξ b j
  exact aff_nonneg (bk_mono hτ h3 h4 h5 hξ (Nat.lt_succ_self j)).le hc
    (xbk_nn hτ h3 h4 h5 hξ b j) (xbk_nn hτ h3 h4 h5 hξ b (j + 1)) t h1 h2.le

/-- Positivity in the interior of a segment from a positive endpoint. -/
theorem x_pos_seg (b : Ex1Buffer) (j : ℕ)
    (hpos : 0 < (traj τ hτ ξ).x b (bk τ ξ j) ∨ 0 < (traj τ hτ ξ).x b (bk τ ξ (j + 1))) :
    ∀ t, bk τ ξ j < t → t < bk τ ξ (j + 1) → 0 < (traj τ hτ ξ).x b t := by
  obtain ⟨c, hc⟩ := xaff hτ h3 h4 h5 hξ b j
  exact aff_pos hc (xbk_nn hτ h3 h4 h5 hξ b j) (xbk_nn hτ h3 h4 h5 hξ b (j + 1)) hpos

theorem x_zero_seg (b : Ex1Buffer) (j : ℕ)
    (h0 : (traj τ hτ ξ).x b (bk τ ξ j) = 0) (h1 : (traj τ hτ ξ).x b (bk τ ξ (j + 1)) = 0) :
    ∀ t, bk τ ξ j ≤ t → t ≤ bk τ ξ (j + 1) → (traj τ hτ ξ).x b t = 0 := by
  obtain ⟨c, hc⟩ := xaff hτ h3 h4 h5 hξ b j
  exact aff_zero (bk_mono hτ h3 h4 h5 hξ (Nat.lt_succ_self j)) hc h0 h1

end C2X


section C2P
variable {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)

theorem sf_odd (n : ℕ) : sf τ ξ (2 * n + 1) = bk τ ξ (4 * n) := by
  simp only [sf]; rw [if_neg (by omega)]; congr 1; omega
theorem sf_even (n : ℕ) : sf τ ξ (2 * n + 2) = bk τ ξ (4 * n + 2) := by
  simp only [sf]; rw [if_neg (by omega)]; congr 1; omega
theorem βf_odd0 (n : ℕ) : βf 0 (2 * n + 1) = ex1Buf 0 := by simp [βf]
theorem βf_odd1 (n : ℕ) : βf 1 (2 * n + 1) = ex1Buf 1 := by simp [βf]
theorem βf_even0 (n : ℕ) : βf 0 (2 * n + 2) = ex1Buf 3 := by
  simp only [βf]; rw [if_neg (by omega)]; rfl
theorem βf_even1 (n : ℕ) : βf 1 (2 * n + 2) = ex1Buf 2 := by
  simp only [βf]; rw [if_neg (by omega)]; rfl

include hτ h3 h4 h5 hξ

theorem bk_nn (j : ℕ) : 0 ≤ bk τ ξ j := by
  rw [← bk_zero (τ := τ) (ξ := ξ)]; exact (bk_mono hτ h3 h4 h5 hξ).monotone (Nat.zero_le j)

theorem sf_mono : ∀ i j, i ≤ j → sf τ ξ i ≤ sf τ ξ j := by
  intro i j hij
  simp only [sf]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact bk_nn hτ h3 h4 h5 hξ _
  · omega
  · exact (bk_mono hτ h3 h4 h5 hξ).monotone (by omega)

theorem procA (m : Fin 2) (b : Ex1Buffer) (n : ℕ) {σ : ℝ} (h1 : bk τ ξ (4 * n) ≤ σ)
    (h2 : σ < bk τ ξ (4 * n + 2)) :
    (traj τ hτ ξ).Processing m b σ ↔ βf m (2 * n + 1) = b := by
  have := processing_iff' (T := traj τ hτ ξ) (m := m) (k := 2 * n + 1)
    (fun i j hij _ => sf_mono hτ h3 h4 h5 hξ i j hij) (WithTop.coe_lt_top _)
    (a := bk τ ξ (4 * n)) (w := bk τ ξ (4 * n + 2)) (by simp only [traj]; rw [sf_odd])
    (fun _ => by simp only [traj]; rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, sf_even])
    h1 h2 b
  rw [this, ex1_zero_setup]
  simp only [traj]
  rw [sf_odd]
  exact ⟨fun h => h.1, fun h => ⟨h, h1⟩⟩

theorem procB (m : Fin 2) (b : Ex1Buffer) (n : ℕ) {σ : ℝ} (h1 : bk τ ξ (4 * n + 2) ≤ σ)
    (h2 : σ < bk τ ξ (4 * n + 4)) :
    (traj τ hτ ξ).Processing m b σ ↔ βf m (2 * n + 2) = b := by
  have := processing_iff' (T := traj τ hτ ξ) (m := m) (k := 2 * n + 2)
    (fun i j hij _ => sf_mono hτ h3 h4 h5 hξ i j hij) (WithTop.coe_lt_top _)
    (a := bk τ ξ (4 * n + 2)) (w := bk τ ξ (4 * n + 4)) (by simp only [traj]; rw [sf_even])
    (fun _ => by
      simp only [traj]
      rw [show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, sf_odd,
        show 4 * (n + 1) = 4 * n + 4 by ring])
    h1 h2 b
  rw [this, ex1_zero_setup]
  simp only [traj]
  rw [sf_even]
  exact ⟨fun h => h.1, fun h => ⟨h, h1⟩⟩

end C2P


section C2Simp
variable {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k}
@[simp] theorem rB0 : (S2 τ hτ).route (ex1Buf 0) = 0 := rfl
@[simp] theorem rB1 : (S2 τ hτ).route (ex1Buf 1) = 1 := rfl
@[simp] theorem rB2 : (S2 τ hτ).route (ex1Buf 2) = 1 := rfl
@[simp] theorem rB3 : (S2 τ hτ).route (ex1Buf 3) = 0 := rfl
@[simp] theorem tS2 (i : Fin 4) : (S2 τ hτ).τ (ex1Buf i) = τ i := rfl
@[simp] theorem ex1Buf_eq_iff (i j : Fin 4) : ex1Buf i = ex1Buf j ↔ i = j :=
  ⟨ex1Buf_inj, fun h => h ▸ rfl⟩
@[simp] theorem ex1Buf_snd (i : Fin 4) : (ex1Buf i).2 = i := rfl
attribute [simp] βf_odd0 βf_odd1 βf_even0 βf_even1
end C2Simp

section C2T
variable {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
include hτ h3 h4 h5 hξ

theorem osl_bounds (i : Fin 4) (k : ℕ) : 0 ≤ osl τ i k ∧ osl τ i k ≤ 1 / τ i := by
  obtain ⟨h01, h23, h0, h1, h2, h3'⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have g0 : 1 ≤ 1 / τ 0 := by rw [le_one_div (by norm_num) t0]; linarith
  have g0' : 1 ≤ (τ 0)⁻¹ := by simpa using g0
  fin_cases i <;> rcases k with _ | _ | _ | _ | k <;>
    simp [osl] <;> first | positivity | (try constructor) <;> first | positivity | linarith | skip

theorem seg_split (j : ℕ) : ∃ n r, r < 4 ∧ j = 4 * n + r :=
  ⟨j / 4, j % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 4).symm⟩

theorem yf_zero (i : Fin 4) : yf τ ξ i 0 = 0 := by
  have := yf_bk hτ h3 h4 h5 hξ i 0 0 (by norm_num)
  simp only [mul_zero, add_zero, bk_zero, Ssum, Yc] at this
  simpa using this

theorem traj_isTraj : IsTrajectory (S2 τ hτ) (traj τ hτ ξ) := by
  have hmono := bk_mono hτ h3 h4 h5 hξ
  have hunb := bk_unb hτ h3 h4 h5 hξ
  have hb0 : bk τ ξ 0 = 0 := bk_zero
  have hin0 : ∀ b : Ex1Buffer, (S2 τ hτ).input (traj τ hτ ξ).y b 0 = 0 := by
    intro b
    rw [ex1_buf_eq b]
    generalize b.2 = i
    fin_cases i
    · simp only [Fin.zero_eta]; rw [ex1_input0]
    · simp only [Fin.mk_one]; rw [ex1_input1, ty]; exact yf_zero hτ h3 h4 h5 hξ 0
    · show (S2 τ hτ).input (traj τ hτ ξ).y (ex1Buf 2) 0 = 0
      rw [ex1_input2, ty]; exact yf_zero hτ h3 h4 h5 hξ 1
    · show (S2 τ hτ).input (traj τ hτ ξ).y (ex1Buf 3) 0 = 0
      rw [ex1_input3, ty]; exact yf_zero hτ h3 h4 h5 hξ 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b; rw [ty]; exact yf_zero hτ h3 h4 h5 hξ _
  · intro b
    rw [ty]
    exact seg_mono hb0 hmono hunb (fun t _ => rfl) (fun j => (osl_bounds hτ h3 h4 h5 hξ _ _).1)
  · intro b t _
    have e := hin0 b
    have hy := yf_zero hτ h3 h4 h5 hξ b.2
    simp only [traj] at e ⊢
    rw [e, hy]; ring
  · intro b t ht; exact x_nn hτ h3 h4 h5 hξ b t ht
  · intro m; exact WithTop.coe_lt_top _
  · intro m; simp [traj, sf]
  · intro m k _
    simp only [traj, βf]
    fin_cases m <;> split_ifs <;> first | rfl | (exfalso; simp_all)
  · intro m k _
    rw [ex1_zero_setup]
    exact sf_mono hτ h3 h4 h5 hξ k (k + 1) (Nat.le_succ k)
  · intro m t
    obtain ⟨j, hj⟩ := hunb t
    apply Set.Finite.subset (Set.finite_lt_nat (2 * j + 1))
    intro k ⟨_, hk⟩
    simp only [Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    have : bk τ ξ j ≤ sf τ ξ k := by
      simp only [sf]
      rw [if_neg (by omega)]
      exact hmono.monotone (by omega)
    simp only [traj] at hk
    linarith
  · intro bb s t hs hst
    have := seg_cap hb0 hmono hunb (traj τ hτ ξ) bb (sl := fun j => osl τ bb.2 (j % 4))
      (fun t _ => rfl) (fun j => osl_bounds hτ h3 h4 h5 hξ _ _) (by
        intro j hpos σ h1 h2
        obtain ⟨n, r, hr, rfl⟩ := seg_split hτ h3 h4 h5 hξ j
        have hr' : (4 * n + r) % 4 = r := by omega
        rw [hr'] at hpos
        rw [ex1_buf_eq bb] at hpos ⊢
        generalize bb.2 = i at hpos ⊢
        interval_cases r
        · rw [procA hτ h3 h4 h5 hξ _ _ n (le_of_lt (by simpa using h1)) (lt_trans h2 (hmono (by omega)))]
          fin_cases i <;> simp_all [osl]
        · rw [procA hτ h3 h4 h5 hξ _ _ n (le_trans (hmono.monotone (by omega)) h1.le) h2]
          fin_cases i <;> simp_all [osl]
        · rw [procB hτ h3 h4 h5 hξ _ _ n h1.le (lt_trans h2 (hmono (by omega)))]
          fin_cases i <;> simp_all [osl]
        · rw [procB hτ h3 h4 h5 hξ _ _ n (le_trans (hmono.monotone (by omega)) h1.le)
            (by simpa using h2)]
          fin_cases i <;> simp_all [osl]) s t hs hst
    exact this
  · intro bb s t hs hst hall
    exact seg_full hb0 hmono hunb (traj τ hτ ξ) bb (sl := fun j => osl τ bb.2 (j % 4))
      (fun t _ => rfl) (by
        intro j σ h1 h2 hP hx
        obtain ⟨n, r, hr, rfl⟩ := seg_split hτ h3 h4 h5 hξ j
        have hr' : (4 * n + r) % 4 = r := by omega
        rw [hr']
        obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ :=
          xtab hτ h3 h4 h5 hξ n
        obtain ⟨⟨a0', -⟩, ⟨b0', -⟩, ⟨c0', -⟩, ⟨d0', -⟩⟩ := xtab hτ h3 h4 h5 hξ (n + 1)
        rw [ex1_buf_eq bb] at hP hx ⊢
        generalize bb.2 = i at hP hx ⊢
        interval_cases r
        · rw [procA hτ h3 h4 h5 hξ _ _ n (le_of_lt (by simpa using h1)) (lt_trans h2 (hmono (by omega)))] at hP
          fin_cases i <;> simp_all [osl]
        · rw [procA hτ h3 h4 h5 hξ _ _ n (le_trans (hmono.monotone (by omega)) h1.le) h2] at hP
          have hz := x_zero_seg hτ h3 h4 h5 hξ (ex1Buf 0) (4 * n + 1) a1 a2 σ h1.le h2.le
          fin_cases i <;> simp_all [osl]
        · rw [procB hτ h3 h4 h5 hξ _ _ n h1.le (lt_trans h2 (hmono (by omega)))] at hP
          fin_cases i <;> simp_all [osl]
        · rw [procB hτ h3 h4 h5 hξ _ _ n (le_trans (hmono.monotone (by omega)) h1.le)
            (by simpa using h2)] at hP
          rw [← bk4 hτ h3 h4 h5 hξ n] at h2
          have hz := x_zero_seg hτ h3 h4 h5 hξ (ex1Buf 2) (4 * n + 3) c3
            (by rw [← bk4 hτ h3 h4 h5 hξ n]; simpa using c0') σ h1.le
            (by rw [← bk4 hτ h3 h4 h5 hξ n]; exact h2.le)
          fin_cases i <;> simp_all [osl]) s t hs hst hall

end C2T


section C2Cl
variable {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
include hτ h3 h4 h5 hξ

theorem yf_inc (i : Fin 4) (j : ℕ) (hpos : 0 < osl τ i (j % 4)) :
    ∀ σ, bk τ ξ j < σ → σ ≤ bk τ ξ (j + 1) → yf τ ξ i (bk τ ξ j) < yf τ ξ i σ := by
  intro σ h1 h2
  rw [yf_aff hτ h3 h4 h5 hξ i j h1.le h2]
  have : 0 < osl τ i (j % 4) * (σ - bk τ ξ j) := mul_pos hpos (by linarith)
  linarith

theorem yf_const (i : Fin 4) (j : ℕ) (hz : osl τ i (j % 4) = 0) :
    ∀ σ, bk τ ξ j ≤ σ → σ ≤ bk τ ξ (j + 1) → yf τ ξ i σ = yf τ ξ i (bk τ ξ j) := by
  intro σ h1 h2
  rw [yf_aff hτ h3 h4 h5 hξ i j h1 h2, hz]; ring

theorem traj_clearing : IsClearing (S2 τ hτ) (traj τ hτ ξ) := by
  have hT := traj_isTraj hτ h3 h4 h5 hξ
  have hmono := bk_mono hτ h3 h4 h5 hξ
  have t0 := hτ 0; have t2 := hτ 2
  refine ⟨hT, ?_⟩
  intro m k _
  rw [ex1_zero_setup]
  simp only [ts, tβ]
  -- demand helpers
  have demB1 : ∀ n, (traj τ hτ ξ).Demanding (ex1Buf 1) (bk τ ξ (4 * n)) := by
    intro n
    apply demanding_of_incr hT _ (bk_nn hτ h3 h4 h5 hξ _) (hmono (Nat.lt_succ_self _)) _
      (input_mono hT _)
    intro σ h1 h2
    rw [ex1_input1, ex1_input1, ty, ex1Buf_snd]
    apply yf_inc hτ h3 h4 h5 hξ 0 (4 * n) _ σ h1 h2
    rw [show 4 * n % 4 = 0 by omega]; simp [osl]; positivity
  have demB3 : ∀ n, (traj τ hτ ξ).Demanding (ex1Buf 3) (bk τ ξ (4 * n + 2)) := by
    intro n
    apply demanding_of_incr hT _ (bk_nn hτ h3 h4 h5 hξ _) (hmono (Nat.lt_succ_self _)) _
      (input_mono hT _)
    intro σ h1 h2
    rw [ex1_input3, ex1_input3, ty, ex1Buf_snd]
    apply yf_inc hτ h3 h4 h5 hξ 2 (4 * n + 2) _ σ h1 h2
    rw [show (4 * n + 2) % 4 = 2 by omega]; simp [osl]; positivity
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rcases n with _ | n
    · -- run 0
      have hs1 : sf τ ξ (2 * 0 + 1) = bk τ ξ (4 * 0) := sf_odd 0
      simp only [Nat.mul_zero, Nat.zero_add] at hs1 ⊢
      obtain ⟨⟨a0, -⟩, ⟨b0, -⟩, ⟨c0, -⟩, ⟨d0, -⟩⟩ := xtab hτ h3 h4 h5 hξ 0
      simp only [Nat.mul_zero] at a0 b0 c0 d0
      have e0 : sf τ ξ 0 = 0 := by simp [sf]
      rw [e0]
      refine ⟨fun t ht h => absurd (h (WithTop.coe_lt_top _)) (by rw [hs1, bk_zero]; linarith),
        fun _ => ?_⟩
      rw [hs1]
      fin_cases m <;> simp only [Fin.zero_eta, Fin.mk_one]
      · refine ⟨?_, by simp [βf], by rw [show βf 0 1 = ex1Buf 0 by simp [βf]]; exact dem0 _⟩
        rw [show βf 0 0 = ex1Buf 3 by simp [βf]]; exact d0
      · refine ⟨?_, by simp [βf], ?_⟩
        · rw [show βf 1 0 = ex1Buf 2 by simp [βf]]; exact c0
        · rw [show βf 1 1 = ex1Buf 1 by simp [βf]]; simpa using demB1 0
    · -- run 2(n+1) = 2n+2
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, sf_even, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring,
        sf_odd, show 4 * (n + 1) = 4 * n + 4 by ring]
      obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ :=
        xtab hτ h3 h4 h5 hξ n
      obtain ⟨⟨a0', -⟩, ⟨b0', -⟩, ⟨c0', -⟩, ⟨d0', -⟩⟩ := xtab hτ h3 h4 h5 hξ (n + 1)
      rw [show 4 * (n + 1) = 4 * n + 3 + 1 by ring] at a0' b0' c0' d0'
      have e44 : 4 * n + 4 = 4 * n + 3 + 1 := by ring
      fin_cases m
      · simp only [Fin.zero_eta, βf_even0, βf_odd0]
        refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, dem0 _⟩⟩
        · have h2' := h2 (WithTop.coe_lt_top _)
          apply lt_irrefl (0 : ℝ)
          nth_rewrite 2 [← hc.1]
          rcases lt_trichotomy t (bk τ ξ (4 * n + 3)) with h | h | h
          · exact x_pos_seg hτ h3 h4 h5 hξ (ex1Buf 3) (4 * n + 2) (Or.inr d3) t h1 h
          · rw [h]; exact d3
          · exact x_pos_seg hτ h3 h4 h5 hξ (ex1Buf 3) (4 * n + 3) (Or.inl d3) t h
              (by rw [← e44]; exact h2')
        · rw [e44]; exact d0'
      · simp only [Fin.mk_one, βf_even1, βf_odd1]
        refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, ?_⟩⟩
        · have h2' := h2 (WithTop.coe_lt_top _)
          rcases lt_or_ge t (bk τ ξ (4 * n + 3)) with h | h
          · have := x_pos_seg hτ h3 h4 h5 hξ (ex1Buf 2) (4 * n + 2) (Or.inl c2) t h1 h
            rw [hc.1] at this; exact lt_irrefl _ this
          · obtain ⟨b', hb'r, hb'ne, hb'd⟩ := hc.2
            rcases ex1_m1 hb'r with hb | hb
            swap
            · exact hb'ne hb
            rw [hb] at hb'd
            have h2'' : t < bk τ ξ (4 * n + 3 + 1) := h2'.trans_eq (congrArg (bk τ ξ) e44)
            refine notdem (x_zero_seg hτ h3 h4 h5 hξ (ex1Buf 1) (4 * n + 3) b3 b0' t h
              h2''.le) h2' ?_ hb'd
            rw [ex1_input1, ex1_input1, ty, ex1Buf_snd, e44,
              yf_const hτ h3 h4 h5 hξ 0 (4 * n + 3) (by simp [show (4 * n + 3) % 4 = 3 by omega, osl])
                _ (hmono (Nat.lt_succ_self _)).le le_rfl,
              yf_const hτ h3 h4 h5 hξ 0 (4 * n + 3) (by simp [show (4 * n + 3) % 4 = 3 by omega, osl])
                _ h h2''.le]
        · rw [e44]; exact c0'
        · have := demB1 (n + 1)
          rwa [show 4 * (n + 1) = 4 * n + 4 by ring] at this
  · -- run 2n+1
    rw [sf_odd, show 2 * n + 1 + 1 = 2 * n + 2 by ring, sf_even]
    obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ :=
      xtab hτ h3 h4 h5 hξ n
    have e0 : 4 * n = 4 * n + 0 := rfl
    fin_cases m
    · simp only [Fin.zero_eta, βf_even0, βf_odd0]
      refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨a2, by simp, demB3 n⟩⟩
      have h2' := h2 (WithTop.coe_lt_top _)
      rcases lt_or_ge t (bk τ ξ (4 * n + 1)) with h | h
      · have := x_pos_seg hτ h3 h4 h5 hξ (ex1Buf 0) (4 * n) (Or.inl (by rw [a0]; exact cyc_pos hτ h3 h4 h5 hξ n)) t h1 h
        rw [hc.1] at this; exact lt_irrefl _ this
      · obtain ⟨b', hb'r, hb'ne, hb'd⟩ := hc.2
        rcases ex1_m0 hb'r with hb | hb
        · exact hb'ne hb
        rw [hb] at hb'd
        refine notdem (x_zero_seg hτ h3 h4 h5 hξ (ex1Buf 3) (4 * n + 1) d1 d2 t h h2'.le) h2' ?_ hb'd
        rw [ex1_input3, ex1_input3, ty, ex1Buf_snd,
          yf_const hτ h3 h4 h5 hξ 2 (4 * n + 1) (by simp [show (4 * n + 1) % 4 = 1 by omega, osl])
            _ (le_trans h h2'.le) le_rfl,
          yf_const hτ h3 h4 h5 hξ 2 (4 * n + 1) (by simp [show (4 * n + 1) % 4 = 1 by omega, osl])
            _ h h2'.le]
    · simp only [Fin.mk_one, βf_even1, βf_odd1]
      refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨b2, by simp, Or.inl c2⟩⟩
      have h2' := h2 (WithTop.coe_lt_top _)
      apply lt_irrefl (0 : ℝ)
      nth_rewrite 2 [← hc.1]
      rcases lt_trichotomy t (bk τ ξ (4 * n + 1)) with h | h | h
      · exact x_pos_seg hτ h3 h4 h5 hξ (ex1Buf 1) (4 * n) (Or.inr b1) t h1 h
      · rw [h]; exact b1
      · exact x_pos_seg hτ h3 h4 h5 hξ (ex1Buf 1) (4 * n + 1) (Or.inl b1) t h h2'

end C2Cl

end KSR

namespace KSR
open KumarSeidman.Reentrant C2E

theorem traj_initial {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ) :
    Ex1Initial (traj τ hτ ξ) ξ := by
  have z := fun i => yf_zero hτ h3 h4 h5 hξ i
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · rw [tx0, z]; ring
  · rw [tx1, z, z]; ring
  · rw [tx2, z, z]; ring
  · rw [tx3, z, z]; ring

theorem case2_half (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) :
    ∀ ξ : ℝ, 0 < ξ →
      (∃ T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)),
          IsClearing (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)) T ∧ Ex1Initial T ξ) ∧
        ∀ T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)),
          IsClearing (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)) T → Ex1Initial T ξ →
            ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t := by
  intro ξ hξ
  exact ⟨⟨traj τ hτ ξ, traj_clearing hτ h3 h4 h5 hξ, traj_initial hτ h3 h4 h5 hξ⟩,
    fun T hC h0 => case2_unbounded h3 h4 h5 hC hξ h0⟩

end KSR


open KumarSeidman.Reentrant in
theorem solution (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) :
    (∀ (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k),
      ∃ ξ₀ : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ₀ ≤ ξ →
        (∃ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
          IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T ∧ Ex1Initial T ξ) ∧
        ∀ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
          IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T → Ex1Initial T ξ →
            ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t) ∧
    (∀ ξ : ℝ, 0 < ξ →
      (∃ T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)),
          IsClearing (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)) T ∧ Ex1Initial T ξ) ∧
        ∀ T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)),
          IsClearing (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)) T → Ex1Initial T ξ →
            ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t) :=
  ⟨fun δ hδ => example1_case1_unstable τ hτ h3 h4 h5 δ hδ, KSR.case2_half τ hτ h3 h4 h5⟩

