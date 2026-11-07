-- Prove2me | solution 1 for KumarSeidman.Reentrant.example1_case1_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:24:03.792196+00:00
-- url     : https://prove2.me/submissions/aec8eaca-2876-4100-9641-593e618fa85d

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

theorem ne01 : ex1Buf 0 ≠ ex1Buf 1 := fun h => absurd (ex1Buf_inj h) (by decide)
theorem ne03 : ex1Buf 0 ≠ ex1Buf 3 := fun h => absurd (ex1Buf_inj h) (by decide)
theorem ne12 : ex1Buf 1 ≠ ex1Buf 2 := fun h => absurd (ex1Buf_inj h) (by decide)
theorem ne23 : ex1Buf 2 ≠ ex1Buf 3 := fun h => absurd (ex1Buf_inj h) (by decide)

@[simp] theorem ex1Buf_eq_iff (i j : Fin 4) : ex1Buf i = ex1Buf j ↔ i = j :=
  ⟨ex1Buf_inj, fun h => h ▸ rfl⟩
@[simp] theorem ex1Buf_snd (i : Fin 4) : (ex1Buf i).2 = i := rfl

theorem c2_basic {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) :
    τ 0 < τ 1 ∧ τ 2 < τ 3 ∧ τ 0 < 1 ∧ τ 1 < 1 ∧ τ 2 < 1 ∧ τ 3 < 1 := by
  have := hτ 0; have := hτ 1; have := hτ 2; have := hτ 3
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem ex1Lambda_gt_one {τ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (h3 : 1 < τ 1 + τ 3)
    (h5 : τ 1 + τ 2 < 1) : 1 < ex1Lambda τ := by
  have := hτ 2
  rw [ex1Lambda, lt_div_iff₀ (by linarith)]; linarith

theorem ex1Beta_pos {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h5 : τ 1 + τ 2 < 1) : 0 < ex1Beta τ δ := by
  have := hτ 2; have := hτ 3; have := hδ 0; have := hδ 1; have := hδ 2; have := hδ 3
  have : 0 < 1 - τ 1 := by linarith
  unfold ex1Beta; positivity

abbrev S1 (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k) (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k) :=
  ex1 τ hτ δ (fun k => (hδ k).le)

section C1H
variable {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k} {δ : Fin 4 → ℝ} {hδ : ∀ k, 0 < δ k}
@[simp] theorem r1B0 : (S1 τ hτ δ hδ).route (ex1Buf 0) = 0 := rfl
@[simp] theorem r1B1 : (S1 τ hτ δ hδ).route (ex1Buf 1) = 1 := rfl
@[simp] theorem r1B2 : (S1 τ hτ δ hδ).route (ex1Buf 2) = 1 := rfl
@[simp] theorem r1B3 : (S1 τ hτ δ hδ).route (ex1Buf 3) = 0 := rfl
@[simp] theorem t1S (i : Fin 4) : (S1 τ hτ δ hδ).τ (ex1Buf i) = τ i := rfl
end C1H

noncomputable def xi0 (τ δ : Fin 4 → ℝ) : ℝ :=
  δ 1 / τ 0 + δ 3 / τ 2 + ((δ 1 + τ 1 * δ 2 + δ 2) / (τ 3 / τ 2 - 1) + δ 3) / τ 2 + 1

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

namespace C1E

variable (τ δ : Fin 4 → ℝ) (ξ : ℝ)

noncomputable def T1f (X : ℝ) : ℝ := (ex1Lambda τ + τ 1 / (1 - τ 1)) * X + ex1Alpha τ δ

noncomputable def U4 (X : ℝ) : ℝ := δ 0 + (τ 1 * (X + δ 0) + δ 1) / (1 - τ 1)

/-- Offsets of the breakpoints `t₁, …, t₁₃` of a cycle with backlog `X`. -/
noncomputable def Uc : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => δ 0
  | 2, _ => δ 0 + δ 1
  | 3, X => δ 0 + (X + δ 0) * τ 0 / (1 - τ 0)
  | 4, X => U4 τ δ X
  | 5, X => U4 τ δ X + δ 2
  | 6, X => U4 τ δ X + δ 2 + δ 3
  | 7, X => U4 τ δ X + δ 2 + τ 2 * (X + U4 τ δ X)
  | 8, X => U4 τ δ X + δ 2 + τ 2 * (X + U4 τ δ X) + δ 1
  | 9, X => U4 τ δ X + δ 2 + τ 2 * (X + U4 τ δ X) + δ 1 + τ 1 * δ 2
  | 10, X => U4 τ δ X + δ 2 + τ 2 * (X + U4 τ δ X) + δ 1 + τ 1 * δ 2 + δ 2
  | 11, X => U4 τ δ X + δ 2 + τ 2 * (X + U4 τ δ X) + δ 1 + τ 1 * δ 2 + δ 2 + τ 2 * δ 2
  | _, X => T1f τ δ X

noncomputable def xs : ℕ → ℝ
  | 0 => ξ
  | n + 1 => ex1Lambda τ * xs n + ex1Beta τ δ

noncomputable def ast : ℕ → ℝ
  | 0 => 0
  | n + 1 => ast n + T1f τ δ (xs τ δ ξ n)

noncomputable def bk (j : ℕ) : ℝ := ast τ δ ξ (j / 12) + Uc τ δ (j % 12) (xs τ δ ξ (j / 12))

/-- Output slopes of buffer `i` in the `k`-th segment of a cycle. -/
noncomputable def osl (i : Fin 4) (k : ℕ) : ℝ :=
  match i, k with
  | 0, 1 => 1 / τ 0
  | 0, 2 => 1 / τ 0
  | 0, 3 => 1
  | 0, 4 => 1
  | 1, 2 => 1 / τ 1
  | 1, 3 => 1 / τ 1
  | 1, 8 => 1 / τ 1
  | 2, 5 => 1 / τ 2
  | 2, 6 => 1 / τ 2
  | 2, 10 => 1 / τ 2
  | 3, 6 => 1 / τ 3
  | 3, 7 => 1 / τ 3
  | 3, 8 => 1 / τ 3
  | 3, 9 => 1 / τ 3
  | 3, 10 => 1 / τ 3
  | 3, 11 => 1 / τ 3
  | _, _ => 0

/-- Input slopes. -/
noncomputable def isl (i : Fin 4) (k : ℕ) : ℝ :=
  match i with
  | 0 => 1
  | 1 => osl τ 0 k
  | 2 => osl τ 1 k
  | 3 => osl τ 2 k

/-- Buffer levels at the breakpoints of a cycle with backlog `X`. -/
noncomputable def Xv (i : Fin 4) : ℕ → ℝ → ℝ
  | 0, X => if i = 0 then X else 0
  | k + 1, X => Xv i k X + (isl τ i k - osl τ i k) * (Uc τ δ (k + 1) X - Uc τ δ k X)

end C1E

end KSR

namespace KSR
open KumarSeidman.Reentrant C1E


section C1Pure
variable {τ δ : Fin 4 → ℝ} {ξ : ℝ}

theorem e1_bk_cyc (n k : ℕ) (hk : k < 12) :
    bk τ δ ξ (12 * n + k) = ast τ δ ξ n + Uc τ δ k (xs τ δ ξ n) := by
  simp only [bk]
  have e1 : (12 * n + k) / 12 = n := by omega
  have e2 : (12 * n + k) % 12 = k := by omega
  rw [e1, e2]

theorem e1_bk_step (n k : ℕ) (hk : k ≤ 11) :
    bk τ δ ξ (12 * n + k + 1) - bk τ δ ξ (12 * n + k) =
      Uc τ δ (k + 1) (xs τ δ ξ n) - Uc τ δ k (xs τ δ ξ n) := by
  rcases Nat.lt_or_ge k 11 with h | h
  · rw [show 12 * n + k + 1 = 12 * n + (k + 1) by ring, e1_bk_cyc n (k + 1) (by omega),
      e1_bk_cyc n k (by omega)]
    ring
  · obtain rfl : k = 11 := by omega
    rw [show 12 * n + 11 + 1 = 12 * (n + 1) + 0 by ring, e1_bk_cyc (n + 1) 0 (by omega),
      e1_bk_cyc n 11 (by omega)]
    simp only [ast, Uc]
    ring

theorem e1_bk_zero : bk τ δ ξ 0 = 0 := by simp [bk, ast, Uc]

end C1Pure

section C1Tab
variable {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
include hτ hδ h3 h4 h5

theorem Xv3_12 (X : ℝ) : Xv τ δ 3 12 X = 0 := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have n0 : (1 - τ 0) ≠ 0 := by linarith
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  simp [Xv, isl, osl, Uc, U4, T1f, ex1Lambda, ex1Alpha]
  field_simp
  ring

theorem Xv0_12 (X : ℝ) : Xv τ δ 0 12 X = ex1Lambda τ * X + ex1Beta τ δ := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have n0 : (1 - τ 0) ≠ 0 := by linarith
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  simp [Xv, isl, osl, Uc, U4, T1f, ex1Lambda, ex1Alpha, ex1Beta]
  field_simp
  ring

theorem Xv0_tab (X : ℝ) :
    Xv τ δ 0 0 X = X ∧ Xv τ δ 0 1 X = X + δ 0 ∧
    Xv τ δ 0 2 X = X + δ 0 + (1 - 1 / τ 0) * δ 1 ∧ Xv τ δ 0 3 X = 0 ∧ Xv τ δ 0 4 X = 0 ∧
    Xv τ δ 0 5 X = 0 ∧ Xv τ δ 0 6 X = Uc τ δ 6 X - Uc τ δ 5 X ∧
    Xv τ δ 0 7 X = Uc τ δ 7 X - Uc τ δ 5 X ∧ Xv τ δ 0 8 X = Uc τ δ 8 X - Uc τ δ 5 X ∧
    Xv τ δ 0 9 X = Uc τ δ 9 X - Uc τ δ 5 X ∧ Xv τ δ 0 10 X = Uc τ δ 10 X - Uc τ δ 5 X ∧
    Xv τ δ 0 11 X = Uc τ δ 11 X - Uc τ δ 5 X := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have n0 : (1 - τ 0) ≠ 0 := by linarith
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Xv, isl, osl, Uc, U4] <;> field_simp <;> ring

theorem Xv1_tab (X : ℝ) :
    Xv τ δ 1 0 X = 0 ∧ Xv τ δ 1 1 X = 0 ∧ Xv τ δ 1 2 X = δ 1 / τ 0 ∧
    Xv τ δ 1 3 X = δ 1 / τ 0 + (1 / τ 0 - 1 / τ 1) * (Uc τ δ 3 X - Uc τ δ 2 X) ∧
    Xv τ δ 1 4 X = 0 ∧ Xv τ δ 1 5 X = δ 2 ∧ Xv τ δ 1 6 X = δ 2 ∧ Xv τ δ 1 7 X = δ 2 ∧
    Xv τ δ 1 8 X = δ 2 ∧ Xv τ δ 1 9 X = 0 ∧ Xv τ δ 1 10 X = 0 ∧ Xv τ δ 1 11 X = 0 ∧
    Xv τ δ 1 12 X = 0 := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have n0 : (1 - τ 0) ≠ 0 := by linarith
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Xv, isl, osl, Uc, U4, T1f] <;> field_simp <;> ring

theorem Xv2_tab (X : ℝ) :
    Xv τ δ 2 0 X = 0 ∧ Xv τ δ 2 1 X = 0 ∧ Xv τ δ 2 2 X = 0 ∧
    Xv τ δ 2 3 X = (Uc τ δ 3 X - Uc τ δ 2 X) / τ 1 ∧
    Xv τ δ 2 4 X = (Uc τ δ 4 X - Uc τ δ 2 X) / τ 1 ∧ Xv τ δ 2 5 X = X + U4 τ δ X ∧
    Xv τ δ 2 6 X = X + U4 τ δ X - δ 3 / τ 2 ∧ Xv τ δ 2 7 X = 0 ∧ Xv τ δ 2 8 X = 0 ∧
    Xv τ δ 2 9 X = δ 2 ∧ Xv τ δ 2 10 X = δ 2 ∧ Xv τ δ 2 11 X = 0 ∧ Xv τ δ 2 12 X = 0 := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have n0 : (1 - τ 0) ≠ 0 := by linarith
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Xv, isl, osl, Uc, U4, T1f] <;> field_simp <;> ring

theorem Xv3_tab (X : ℝ) :
    Xv τ δ 3 0 X = 0 ∧ Xv τ δ 3 1 X = 0 ∧ Xv τ δ 3 2 X = 0 ∧ Xv τ δ 3 3 X = 0 ∧
    Xv τ δ 3 4 X = 0 ∧ Xv τ δ 3 5 X = 0 ∧ Xv τ δ 3 6 X = δ 3 / τ 2 ∧
    Xv τ δ 3 7 X = δ 3 / τ 2 + (1 / τ 2 - 1 / τ 3) * (Uc τ δ 7 X - Uc τ δ 6 X) ∧
    Xv τ δ 3 8 X = Xv τ δ 3 7 X - δ 1 / τ 3 ∧
    Xv τ δ 3 9 X = Xv τ δ 3 7 X - δ 1 / τ 3 - τ 1 * δ 2 / τ 3 ∧
    Xv τ δ 3 10 X = Xv τ δ 3 7 X - (δ 1 + τ 1 * δ 2 + δ 2) / τ 3 ∧
    Xv τ δ 3 11 X = Xv τ δ 3 7 X - (δ 1 + τ 1 * δ 2 + δ 2) / τ 3 +
      (1 / τ 2 - 1 / τ 3) * (τ 2 * δ 2) := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have n0 : (1 - τ 0) ≠ 0 := by linarith
  have n1 : (1 - τ 1) ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Xv, isl, osl, Uc, U4, T1f] <;> field_simp <;> ring

theorem xi0_facts {X : ℝ} (hX : xi0 τ δ ≤ X) :
    δ 1 / τ 0 < X ∧ δ 3 / τ 2 < X ∧
    ((δ 1 + τ 1 * δ 2 + δ 2) / (τ 3 / τ 2 - 1) + δ 3) / τ 2 < X := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have d0 := hδ 0; have d1 := hδ 1; have d2 := hδ 2; have d3 := hδ 3
  have hq : 0 < τ 3 / τ 2 - 1 := by rw [sub_pos, one_lt_div t2]; exact h23
  have a1 : 0 < δ 1 / τ 0 := by positivity
  have a2 : 0 < δ 3 / τ 2 := by positivity
  have a3 : 0 < ((δ 1 + τ 1 * δ 2 + δ 2) / (τ 3 / τ 2 - 1) + δ 3) / τ 2 := by positivity
  unfold xi0 at hX
  refine ⟨by linarith, by linarith, by linarith⟩

theorem c1e_lens {X : ℝ} (hX : xi0 τ δ ≤ X) :
    0 < Uc τ δ 3 X - Uc τ δ 2 X ∧ 0 < Uc τ δ 4 X - Uc τ δ 3 X ∧
    0 < Uc τ δ 7 X - Uc τ δ 6 X ∧ 0 < Xv τ δ 3 7 X - (δ 1 + τ 1 * δ 2 + δ 2) / τ 3 := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have d0 := hδ 0; have d1 := hδ 1; have d2 := hδ 2; have d3 := hδ 3
  obtain ⟨th1, th2, th3⟩ := xi0_facts hτ hδ h3 h4 h5 hX
  have hX0 : 0 < X := lt_of_le_of_lt (by positivity) th1
  have p0 : 0 < 1 - τ 0 := by linarith
  have p1 : 0 < 1 - τ 1 := by linarith
  have hU4 : 0 < U4 τ δ X := by unfold U4; positivity
  have L2 : 0 < Uc τ δ 3 X - Uc τ δ 2 X := by
    simp only [Uc]
    have e1 : δ 1 < X * τ 0 := by rwa [div_lt_iff₀ t0] at th1
    have e2 : X * τ 0 ≤ (X + δ 0) * τ 0 / (1 - τ 0) := by
      rw [le_div_iff₀ p0]; nlinarith
    linarith
  have L3 : 0 < Uc τ δ 4 X - Uc τ δ 3 X := by
    simp only [Uc, U4]
    have e1 : τ 0 / (1 - τ 0) < τ 1 / (1 - τ 1) := by
      rw [div_lt_div_iff₀ p0 p1]; nlinarith
    have e2 : (X + δ 0) * τ 0 / (1 - τ 0) < (X + δ 0) * (τ 1 / (1 - τ 1)) := by
      rw [mul_div_assoc]; exact mul_lt_mul_of_pos_left e1 (by linarith)
    have e3 : (τ 1 * (X + δ 0) + δ 1) / (1 - τ 1) = (X + δ 0) * (τ 1 / (1 - τ 1)) + δ 1 / (1 - τ 1) := by
      field_simp
    have e4 : 0 < δ 1 / (1 - τ 1) := by positivity
    linarith
  have L6 : 0 < Uc τ δ 7 X - Uc τ δ 6 X := by
    simp only [Uc]
    have e1 : δ 3 < X * τ 2 := by rwa [div_lt_iff₀ t2] at th2
    have : 0 < τ 2 * U4 τ δ X := mul_pos t2 hU4
    nlinarith
  refine ⟨L2, L3, L6, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, e7, -⟩ := Xv3_tab hτ hδ h3 h4 h5 X
  rw [e7]
  have hq : 0 < τ 3 / τ 2 - 1 := by rw [sub_pos, one_lt_div t2]; exact h23
  have K : (δ 1 + τ 1 * δ 2 + δ 2) / (τ 3 / τ 2 - 1) < τ 2 * X - δ 3 := by
    have := (div_lt_iff₀ t2).mp th3; linarith
  rw [div_lt_iff₀ hq] at K
  have L6' : τ 2 * X - δ 3 < Uc τ δ 7 X - Uc τ δ 6 X := by
    simp only [Uc]; have : 0 < τ 2 * U4 τ δ X := mul_pos t2 hU4; nlinarith
  have hpos : 0 < 1 / τ 2 - 1 / τ 3 := by rw [sub_pos]; exact one_div_lt_one_div_of_lt t2 h23
  have e : (1 / τ 2 - 1 / τ 3) = (τ 3 / τ 2 - 1) / τ 3 := by field_simp
  have : (1 / τ 2 - 1 / τ 3) * (τ 2 * X - δ 3) < (1 / τ 2 - 1 / τ 3) * (Uc τ δ 7 X - Uc τ δ 6 X) :=
    mul_lt_mul_of_pos_left L6' hpos
  have : (δ 1 + τ 1 * δ 2 + δ 2) / τ 3 < (1 / τ 2 - 1 / τ 3) * (τ 2 * X - δ 3) := by
    rw [e, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right t3]; linarith
  have : 0 < δ 3 / τ 2 := by positivity
  linarith

theorem e1_xs_ge {ξ : ℝ} (hξ : 0 < ξ) (n : ℕ) : ξ ≤ xs τ δ ξ n := by
  have hl := ex1Lambda_gt_one hτ h3 h5
  have hb := ex1Beta_pos hτ hδ h5
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [xs]
    have : 0 < xs τ δ ξ n := lt_of_lt_of_le hξ ih
    nlinarith

theorem e1_Ulen {X : ℝ} (hX : xi0 τ δ ≤ X) (k : ℕ) (hk : k ≤ 11) :
    Uc τ δ k X < Uc τ δ (k + 1) X := by
  obtain ⟨L2, L3, L6, L10⟩ := c1e_lens hτ hδ h3 h4 h5 hX
  have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have d0 := hδ 0; have d1 := hδ 1; have d2 := hδ 2; have d3 := hδ 3
  interval_cases k
  · simp [Uc]; linarith
  · simp [Uc]; linarith
  · linarith
  · linarith
  · simp only [Uc]; linarith
  · simp only [Uc]; linarith
  · linarith
  · simp only [Uc]; linarith
  · simp only [Uc]; have := mul_pos t1 d2; linarith
  · simp only [Uc]; linarith
  · simp only [Uc]; have := mul_pos t2 d2; linarith
  · -- the last segment: its length is `τ₄ · x₄(t₁₂)`
    have e12 := Xv3_12 hτ hδ h3 h4 h5 X
    obtain ⟨-, -, -, -, -, -, -, -, -, -, e10, e11⟩ := Xv3_tab hτ hδ h3 h4 h5 X
    have h12 : Xv τ δ 3 12 X = Xv τ δ 3 11 X +
        (isl τ 3 11 - osl τ 3 11) * (Uc τ δ 12 X - Uc τ δ 11 X) := rfl
    have hsl : isl τ 3 11 - osl τ 3 11 = - (1 / τ 3) := by simp [isl, osl]
    rw [hsl, e12] at h12
    have hpos : 0 < Xv τ δ 3 11 X := by
      rw [e11]
      have : 0 < (1 / τ 2 - 1 / τ 3) * (τ 2 * δ 2) :=
        mul_pos (by rw [sub_pos]; exact one_div_lt_one_div_of_lt t2 (by linarith [hτ 0, h4, h5]))
          (by positivity)
      linarith
    have : (1 / τ 3) * (Uc τ δ 12 X - Uc τ δ 11 X) = Xv τ δ 3 11 X := by linarith
    have : 0 < (1 / τ 3) * (Uc τ δ 12 X - Uc τ δ 11 X) := by linarith
    have := pos_of_mul_pos_right this (by positivity)
    linarith

theorem e1_xs_big {ξ : ℝ} (hξ : 0 < ξ) (hbig : xi0 τ δ ≤ ξ) (n : ℕ) : xi0 τ δ ≤ xs τ δ ξ n :=
  hbig.trans (e1_xs_ge hτ hδ h3 h4 h5 hξ n)

theorem e1_bk_mono {ξ : ℝ} (hξ : 0 < ξ) (hbig : xi0 τ δ ≤ ξ) : StrictMono (bk τ δ ξ) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hj : j = 12 * (j / 12) + j % 12 := (Nat.div_add_mod j 12).symm
  have hr : j % 12 ≤ 11 := by omega
  have := e1_bk_step (τ := τ) (δ := δ) (ξ := ξ) (j / 12) (j % 12) hr
  rw [← hj] at this
  have := e1_Ulen hτ hδ h3 h4 h5 (e1_xs_big hτ hδ h3 h4 h5 hξ hbig (j / 12)) (j % 12) hr
  linarith

theorem e1_alpha_pos : 0 < ex1Alpha τ δ := by
  have := hτ 1; have := hτ 2; have := hτ 3
  have := hδ 0; have := hδ 1; have := hδ 2; have := hδ 3
  have : 0 < 1 - τ 1 := by linarith
  unfold ex1Alpha; positivity

theorem e1_ast_ge {ξ : ℝ} (hξ : 0 < ξ) (n : ℕ) : (n : ℝ) * ex1Alpha τ δ ≤ ast τ δ ξ n := by
  have hl := ex1Lambda_gt_one hτ h3 h5
  induction n with
  | zero => simp [ast]
  | succ n ih =>
    simp only [ast, T1f]
    have hx := lt_of_lt_of_le hξ (e1_xs_ge hτ hδ h3 h4 h5 hξ n)
    have : 0 ≤ (ex1Lambda τ + τ 1 / (1 - τ 1)) * xs τ δ ξ n := by
      have := hτ 1; have : 0 < 1 - τ 1 := by linarith [hτ 2]
      have : 0 ≤ τ 1 / (1 - τ 1) := by positivity
      apply mul_nonneg _ hx.le; linarith
    push_cast; linarith

theorem e1_bk_unb {ξ : ℝ} (hξ : 0 < ξ) : ∀ C, ∃ j, C < bk τ δ ξ j := by
  intro C
  have ha := e1_alpha_pos hτ hδ h3 h4 h5
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ex1Alpha τ δ)
  refine ⟨12 * n, ?_⟩
  rw [show 12 * n = 12 * n + 0 by ring, e1_bk_cyc n 0 (by omega)]
  simp only [Uc, add_zero]
  have := e1_ast_ge hτ hδ h3 h4 h5 hξ n
  rw [div_lt_iff₀ ha] at hn
  linarith

end C1Tab
end KSR

namespace KSR
open KumarSeidman.Reentrant

namespace C1E
noncomputable def yf (τ δ : Fin 4 → ℝ) (ξ : ℝ) (i : Fin 4) (t : ℝ) : ℝ :=
  segFun (bk τ δ ξ) (fun j => osl τ i (j % 12)) 0 t

def βf (m : Fin 2) (k : ℕ) : Ex1Buffer :=
  if m = 0 then (if k % 2 = 1 then ex1Buf 0 else ex1Buf 3)
  else (if k % 2 = 1 then ex1Buf 1 else ex1Buf 2)

def sidx1aux (r : ℕ) : ℕ :=
  match r with
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | _ => 9

/-- Breakpoint index of the start of run `k` of machine `m`. -/
def sidx (m : Fin 2) (k : ℕ) : ℕ :=
  if k = 0 then 0 else
  if m = 0 then (if k % 2 = 1 then 12 * ((k - 1) / 2) else 12 * ((k - 2) / 2) + 5)
  else 12 * ((k - 1) / 4) + sidx1aux ((k - 1) % 4)

noncomputable def traj (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k) (δ : Fin 4 → ℝ)
    (hδ : ∀ k, 0 < δ k) (ξ : ℝ) : Trajectory (S1 τ hτ δ hδ) where
  x b t := (if b.2 = 0 then ξ else 0) + (S1 τ hτ δ hδ).input (fun b' => yf τ δ ξ b'.2) b t -
    yf τ δ ξ b.2 t
  y b := yf τ δ ξ b.2
  N _ := ⊤
  β := βf
  s m k := bk τ δ ξ (sidx m k)
end C1E

open C1E

section C1Traj
variable {τ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k} {δ : Fin 4 → ℝ} {hδ : ∀ k, 0 < δ k} {ξ : ℝ}

theorem e1_tx0 (t : ℝ) : (traj τ hτ δ hδ ξ).x (ex1Buf 0) t = ξ + t - yf τ δ ξ 0 t := by
  simp only [traj]; rw [ex1_input0]; simp [ex1Buf]
theorem e1_tx1 (t : ℝ) : (traj τ hτ δ hδ ξ).x (ex1Buf 1) t = yf τ δ ξ 0 t - yf τ δ ξ 1 t := by
  simp only [traj]; rw [ex1_input1]; simp [ex1Buf]
theorem e1_tx2 (t : ℝ) : (traj τ hτ δ hδ ξ).x (ex1Buf 2) t = yf τ δ ξ 1 t - yf τ δ ξ 2 t := by
  simp only [traj]; rw [ex1_input2]; simp [ex1Buf]
theorem e1_tx3 (t : ℝ) : (traj τ hτ δ hδ ξ).x (ex1Buf 3) t = yf τ δ ξ 2 t - yf τ δ ξ 3 t := by
  simp only [traj]; rw [ex1_input3]; simp [ex1Buf]
theorem e1_ty (b : Ex1Buffer) : (traj τ hτ δ hδ ξ).y b = yf τ δ ξ b.2 := rfl
theorem e1_ts (m : Fin 2) (k : ℕ) : (traj τ hτ δ hδ ξ).s m k = bk τ δ ξ (sidx m k) := rfl
theorem e1_tβ (m : Fin 2) (k : ℕ) : (traj τ hτ δ hδ ξ).β m k = βf m k := rfl

theorem sidx_zero (m : Fin 2) : sidx m 0 = 0 := by simp [sidx]
theorem sidx0_odd (n : ℕ) : sidx 0 (2 * n + 1) = 12 * n := by
  simp only [sidx]; rw [if_neg (by omega), if_pos trivial, if_pos (by omega)]; omega
theorem sidx0_even (n : ℕ) : sidx 0 (2 * n + 2) = 12 * n + 5 := by
  simp only [sidx]; rw [if_neg (by omega), if_pos trivial, if_neg (by omega)]; omega
theorem sidx1_r (n r : ℕ) (hr : r < 4) : sidx 1 (4 * n + r + 1) = 12 * n + sidx1aux r := by
  simp only [sidx]; rw [if_neg (by omega), if_neg (by decide)]
  have e1 : (4 * n + r + 1 - 1) / 4 = n := by omega
  have e2 : (4 * n + r + 1 - 1) % 4 = r := by omega
  rw [e1, e2]

theorem sidx_succ (m : Fin 2) (k : ℕ) : sidx m k ≤ sidx m (k + 1) := by
  fin_cases m
  · show sidx 0 k ≤ sidx 0 (k + 1)
    rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
    · rcases n with _ | n
      · simp [sidx_zero]
      · rw [show 2 * (n + 1) = 2 * n + 2 by ring, sidx0_even, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring,
          sidx0_odd]; omega
    · rw [sidx0_odd, show 2 * n + 1 + 1 = 2 * n + 2 by ring, sidx0_even]; omega
  · show sidx 1 k ≤ sidx 1 (k + 1)
    rcases k with _ | k
    · simp [sidx_zero]
    · have hk : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
      have hr : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rw [hk, sidx1_r _ _ hr]
      rcases Nat.lt_or_ge (k % 4) 3 with h | h
      · rw [show 4 * (k / 4) + k % 4 + 1 + 1 = 4 * (k / 4) + (k % 4 + 1) + 1 by ring,
          sidx1_r _ _ (by omega)]
        have : sidx1aux (k % 4) ≤ sidx1aux (k % 4 + 1) := by
          generalize k % 4 = r at h
          interval_cases r <;> simp [sidx1aux]
        omega
      · have e3 : k % 4 = 3 := by omega
        rw [e3, show 4 * (k / 4) + 3 + 1 + 1 = 4 * (k / 4 + 1) + 0 + 1 by ring]
        rw [sidx1_r (k / 4 + 1) 0 (by omega)]
        simp [sidx1aux]; omega

theorem sidx_mono (m : Fin 2) : Monotone (sidx m) :=
  monotone_nat_of_le_succ (sidx_succ m)

end C1Traj
end KSR

namespace KSR
open KumarSeidman.Reentrant C1E

section C1Vals
variable {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
include hτ hδ h3 h4 h5

theorem e1_Xv_pos {X : ℝ} (hX : xi0 τ δ ≤ X) :
    (0 < Xv τ δ 0 0 X ∧ 0 < Xv τ δ 0 1 X ∧ 0 < Xv τ δ 0 2 X ∧ 0 < Xv τ δ 0 6 X ∧
      0 < Xv τ δ 0 7 X ∧ 0 < Xv τ δ 0 8 X ∧ 0 < Xv τ δ 0 9 X ∧ 0 < Xv τ δ 0 10 X ∧
      0 < Xv τ δ 0 11 X ∧ 0 < Xv τ δ 0 12 X) ∧
    (0 < Xv τ δ 1 2 X ∧ 0 < Xv τ δ 1 3 X ∧ 0 < Xv τ δ 1 5 X ∧ 0 < Xv τ δ 1 6 X ∧
      0 < Xv τ δ 1 7 X ∧ 0 < Xv τ δ 1 8 X) ∧
    (0 < Xv τ δ 2 3 X ∧ 0 < Xv τ δ 2 4 X ∧ 0 < Xv τ δ 2 5 X ∧ 0 < Xv τ δ 2 6 X ∧
      0 < Xv τ δ 2 9 X ∧ 0 < Xv τ δ 2 10 X) ∧
    (0 < Xv τ δ 3 6 X ∧ 0 < Xv τ δ 3 7 X ∧ 0 < Xv τ δ 3 8 X ∧ 0 < Xv τ δ 3 9 X ∧
      0 < Xv τ δ 3 10 X ∧ 0 < Xv τ δ 3 11 X) := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have d0 := hδ 0; have d1 := hδ 1; have d2 := hδ 2; have d3 := hδ 3
  obtain ⟨th1, th2, th3⟩ := xi0_facts hτ hδ h3 h4 h5 hX
  have hX0 : 0 < X := lt_of_le_of_lt (by positivity) th1
  obtain ⟨L2, L3, L6, L10⟩ := c1e_lens hτ hδ h3 h4 h5 hX
  have U := fun k hk => e1_Ulen hτ hδ h3 h4 h5 hX k hk
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := Xv0_tab hτ hδ h3 h4 h5 X
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := Xv1_tab hτ hδ h3 h4 h5 X
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := Xv2_tab hτ hδ h3 h4 h5 X
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := Xv3_tab hτ hδ h3 h4 h5 X
  have u5 := U 5 (by norm_num); have u6 := U 6 (by norm_num); have u7 := U 7 (by norm_num)
  have u8 := U 8 (by norm_num); have u9 := U 9 (by norm_num); have u10 := U 10 (by norm_num)
  have hU4 : 0 < U4 τ δ X := by
    have : 0 < 1 - τ 1 := by linarith
    unfold U4; positivity
  have hp23 : 0 < 1 / τ 2 - 1 / τ 3 := by rw [sub_pos]; exact one_div_lt_one_div_of_lt t2 h23
  have hp01 : 0 < 1 / τ 0 - 1 / τ 1 := by rw [sub_pos]; exact one_div_lt_one_div_of_lt t0 h01
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [a0]; exact hX0
  · rw [a1]; linarith
  · rw [a2]
    have : (1 / τ 0 - 1) * δ 1 < δ 1 / τ 0 := by
      have : (1 / τ 0 - 1) * δ 1 = δ 1 / τ 0 - δ 1 := by ring
      linarith
    linarith
  · rw [a6]; linarith
  · rw [a7]; linarith
  · rw [a8]; linarith
  · rw [a9]; linarith
  · rw [a10]; linarith
  · rw [a11]; linarith [U 11 (by norm_num)]
  · rw [Xv0_12 hτ hδ h3 h4 h5]
    have := ex1Beta_pos hτ hδ h5
    have := ex1Lambda_gt_one hτ h3 h5
    have := mul_pos (by linarith : 0 < ex1Lambda τ) hX0
    linarith
  · rw [b2]; positivity
  · rw [b3]; have : 0 < δ 1 / τ 0 := by positivity
    have := mul_pos hp01 L2; linarith
  · rw [b5]; exact d2
  · rw [b6]; exact d2
  · rw [b7]; exact d2
  · rw [b8]; exact d2
  · rw [c3]; exact div_pos L2 t1
  · rw [c4]; exact div_pos (by linarith) t1
  · rw [c5]; linarith
  · rw [c6]; linarith
  · rw [c9]; exact d2
  · rw [c10]; exact d2
  · rw [e6]; positivity
  · have : 0 < (δ 1 + τ 1 * δ 2 + δ 2) / τ 3 := by positivity
    linarith
  · rw [e8]
    have : δ 1 / τ 3 ≤ (δ 1 + τ 1 * δ 2 + δ 2) / τ 3 := by
      apply div_le_div_of_nonneg_right _ t3.le; have := mul_pos t1 d2; linarith
    linarith
  · rw [e9]
    have : δ 1 / τ 3 + τ 1 * δ 2 / τ 3 ≤ (δ 1 + τ 1 * δ 2 + δ 2) / τ 3 := by
      rw [← add_div]; apply div_le_div_of_nonneg_right _ t3.le; linarith
    linarith
  · rw [e10]; exact L10
  · rw [e11]
    have := mul_pos hp23 (mul_pos t2 d2)
    linarith

end C1Vals
end KSR


namespace KSR
open KumarSeidman.Reentrant C1E

section C1X
variable {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hbig : xi0 τ δ ≤ ξ)
include hτ hδ h3 h4 h5 hξ hbig

theorem e1_yf_aff (i : Fin 4) (j : ℕ) {t : ℝ} (h1 : bk τ δ ξ j ≤ t) (h2 : t ≤ bk τ δ ξ (j + 1)) :
    yf τ δ ξ i t = yf τ δ ξ i (bk τ δ ξ j) + osl τ i (j % 12) * (t - bk τ δ ξ j) := by
  simp only [yf]
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  rw [segFun_eq hm _ 0 h1 h2, segFun_at hm]

theorem e1_yf_zero (i : Fin 4) : yf τ δ ξ i 0 = 0 := by
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have := segFun_at hm (fun j => osl τ i (j % 12)) 0 0
  rw [e1_bk_zero] at this
  simp only [yf]; rw [this]; rfl

/-- One step of the buffer levels between consecutive breakpoints. -/
theorem e1_xstep {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (i : Fin 4) (j : ℕ) :
    (traj τ hτ' δ hδ' ξ).x (ex1Buf i) (bk τ δ ξ (j + 1)) =
      (traj τ hτ' δ hδ' ξ).x (ex1Buf i) (bk τ δ ξ j) +
        (isl τ i (j % 12) - osl τ i (j % 12)) * (bk τ δ ξ (j + 1) - bk τ δ ξ j) := by
  have hb : bk τ δ ξ j < bk τ δ ξ (j + 1) :=
    (e1_bk_mono hτ hδ h3 h4 h5 hξ hbig) (show j < j + 1 by omega)
  have B : ∀ i, yf τ δ ξ i (bk τ δ ξ (j + 1)) =
      yf τ δ ξ i (bk τ δ ξ j) + osl τ i (j % 12) * (bk τ δ ξ (j + 1) - bk τ δ ξ j) :=
    fun i => e1_yf_aff hτ hδ h3 h4 h5 hξ hbig i j hb.le le_rfl
  have e : ∀ i : Fin 4, ∃ k : Fin 4, i = k := fun i => ⟨i, rfl⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl
  · rw [e1_tx0, e1_tx0, B 0]; simp only [isl]; ring
  · rw [e1_tx1, e1_tx1, B 0, B 1]; simp only [isl]; ring
  · rw [e1_tx2, e1_tx2, B 1, B 2]; simp only [isl]; ring
  · rw [e1_tx3, e1_tx3, B 2, B 3]; simp only [isl]; ring

theorem e1_Xv_wrap (i : Fin 4) (X : ℝ) :
    Xv τ δ i 12 X = Xv τ δ i 0 (ex1Lambda τ * X + ex1Beta τ δ) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl
  · rw [Xv0_12 hτ hδ h3 h4 h5]; simp [Xv]
  · rw [(Xv1_tab hτ hδ h3 h4 h5 X).2.2.2.2.2.2.2.2.2.2.2.2]; simp [Xv]
  · rw [(Xv2_tab hτ hδ h3 h4 h5 X).2.2.2.2.2.2.2.2.2.2.2.2]; simp [Xv]
  · rw [Xv3_12 hτ hδ h3 h4 h5]; simp [Xv]

theorem e1_xbk {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (i : Fin 4) (j : ℕ) :
    (traj τ hτ' δ hδ' ξ).x (ex1Buf i) (bk τ δ ξ j) = Xv τ δ i (j % 12) (xs τ δ ξ (j / 12)) := by
  induction j with
  | zero =>
    rw [e1_bk_zero]
    have z := fun i => e1_yf_zero hτ hδ h3 h4 h5 hξ hbig i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl
    · rw [e1_tx0, z]; simp [Xv, xs]
    · rw [e1_tx1, z, z]; simp [Xv]
    · rw [e1_tx2, z, z]; simp [Xv]
    · rw [e1_tx3, z, z]; simp [Xv]
  | succ j ih =>
    rw [e1_xstep hτ hδ h3 h4 h5 hξ hbig, ih]
    have hj : j = 12 * (j / 12) + j % 12 := (Nat.div_add_mod j 12).symm
    have hst := e1_bk_step (τ := τ) (δ := δ) (ξ := ξ) (j / 12) (j % 12) (by omega)
    rw [← hj] at hst
    rw [hst]
    rcases Nat.lt_or_ge (j % 12) 11 with h | h
    · have e1 : (j + 1) / 12 = j / 12 := by omega
      have e2 : (j + 1) % 12 = j % 12 + 1 := by omega
      rw [e1, e2]; rfl
    · have e1 : (j + 1) / 12 = j / 12 + 1 := by omega
      have e2 : (j + 1) % 12 = 0 := by omega
      have e3 : j % 12 = 11 := by omega
      rw [e1, e2, e3]
      show Xv τ δ i 12 (xs τ δ ξ (j / 12)) = _
      rw [e1_Xv_wrap hτ hδ h3 h4 h5 hξ hbig]
      rfl

theorem e1_xv {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (i : Fin 4) (n k : ℕ) (hk : k ≤ 12) :
    (traj τ hτ' δ hδ' ξ).x (ex1Buf i) (bk τ δ ξ (12 * n + k)) = Xv τ δ i k (xs τ δ ξ n) := by
  rcases Nat.lt_or_ge k 12 with h | h
  · rw [e1_xbk hτ hδ h3 h4 h5 hξ hbig]
    have e1 : (12 * n + k) / 12 = n := by omega
    have e2 : (12 * n + k) % 12 = k := by omega
    rw [e1, e2]
  · obtain rfl : k = 12 := by omega
    rw [e1_xbk hτ hδ h3 h4 h5 hξ hbig, e1_Xv_wrap hτ hδ h3 h4 h5 hξ hbig]
    have e1 : (12 * n + 12) / 12 = n + 1 := by omega
    have e2 : (12 * n + 12) % 12 = 0 := by omega
    rw [e1, e2]; rfl

omit hξ hbig in
theorem e1_Xv_nn {X : ℝ} (hX : xi0 τ δ ≤ X) (i : Fin 4) (k : ℕ) (hk : k ≤ 12) :
    0 ≤ Xv τ δ i k X := by
  obtain ⟨⟨p00, p01, p02, p06, p07, p08, p09, p010, p011, p012⟩, ⟨p12, p13, p15, p16, p17, p18⟩,
    ⟨p23, p24, p25, p26, p29, p210⟩, ⟨p36, p37, p38, p39, p310, p311⟩⟩ :=
    e1_Xv_pos hτ hδ h3 h4 h5 hX
  obtain ⟨-, -, -, a3, a4, a5, -⟩ := Xv0_tab hτ hδ h3 h4 h5 X
  obtain ⟨b0, b1, -, -, b4, -, -, -, -, b9, b10, b11, b12⟩ := Xv1_tab hτ hδ h3 h4 h5 X
  obtain ⟨c0, c1, c2, -, -, -, -, c7, c8, -, -, c11, c12⟩ := Xv2_tab hτ hδ h3 h4 h5 X
  obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := Xv3_tab hτ hδ h3 h4 h5 X
  have e12 := Xv3_12 hτ hδ h3 h4 h5 X
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl <;>
    interval_cases k <;> linarith

theorem e1_xaff {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (b : Ex1Buffer) (j : ℕ) :
    ∃ c : ℝ, ∀ t, bk τ δ ξ j ≤ t → t ≤ bk τ δ ξ (j + 1) →
    (traj τ hτ' δ hδ' ξ).x b t = (traj τ hτ' δ hδ' ξ).x b (bk τ δ ξ j) + c * (t - bk τ δ ξ j) := by
  have hb : bk τ δ ξ j < bk τ δ ξ (j + 1) :=
    (e1_bk_mono hτ hδ h3 h4 h5 hξ hbig) (show j < j + 1 by omega)
  have A := fun i t (h1 : bk τ δ ξ j ≤ t) (h2 : t ≤ bk τ δ ξ (j + 1)) =>
    e1_yf_aff hτ hδ h3 h4 h5 hξ hbig i j h1 h2
  rw [ex1_buf_eq b]
  generalize b.2 = i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl
  · refine ⟨1 - osl τ 0 (j % 12), fun t h1 h2 => ?_⟩
    rw [e1_tx0, e1_tx0, A 0 t h1 h2]; ring
  · refine ⟨osl τ 0 (j % 12) - osl τ 1 (j % 12), fun t h1 h2 => ?_⟩
    rw [e1_tx1, e1_tx1, A 0 t h1 h2, A 1 t h1 h2]; ring
  · refine ⟨osl τ 1 (j % 12) - osl τ 2 (j % 12), fun t h1 h2 => ?_⟩
    rw [e1_tx2, e1_tx2, A 1 t h1 h2, A 2 t h1 h2]; ring
  · refine ⟨osl τ 2 (j % 12) - osl τ 3 (j % 12), fun t h1 h2 => ?_⟩
    rw [e1_tx3, e1_tx3, A 2 t h1 h2, A 3 t h1 h2]; ring

theorem e1_xbk_nn {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (b : Ex1Buffer) (j : ℕ) :
    0 ≤ (traj τ hτ' δ hδ' ξ).x b (bk τ δ ξ j) := by
  rw [ex1_buf_eq b, e1_xbk hτ hδ h3 h4 h5 hξ hbig]
  exact e1_Xv_nn hτ hδ h3 h4 h5 (e1_xs_big hτ hδ h3 h4 h5 hξ hbig _) _ _ (by omega)

theorem e1_x_nn {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (b : Ex1Buffer) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (traj τ hτ' δ hδ' ξ).x b t := by
  obtain ⟨j, h1, h2⟩ := seg_exists e1_bk_zero (e1_bk_unb hτ hδ h3 h4 h5 hξ) ht
  obtain ⟨c, hc⟩ := e1_xaff hτ hδ h3 h4 h5 hξ hbig (hτ' := hτ') (hδ' := hδ') b j
  exact aff_nonneg ((e1_bk_mono hτ hδ h3 h4 h5 hξ hbig) (Nat.lt_succ_self j)).le hc
    (e1_xbk_nn hτ hδ h3 h4 h5 hξ hbig b j) (e1_xbk_nn hτ hδ h3 h4 h5 hξ hbig b (j + 1)) t h1 h2.le

theorem e1_x_pos_seg {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (b : Ex1Buffer) (j : ℕ)
    (hpos : 0 < (traj τ hτ' δ hδ' ξ).x b (bk τ δ ξ j) ∨
      0 < (traj τ hτ' δ hδ' ξ).x b (bk τ δ ξ (j + 1))) :
    ∀ t, bk τ δ ξ j < t → t < bk τ δ ξ (j + 1) → 0 < (traj τ hτ' δ hδ' ξ).x b t := by
  obtain ⟨c, hc⟩ := e1_xaff hτ hδ h3 h4 h5 hξ hbig (hτ' := hτ') (hδ' := hδ') b j
  exact aff_pos hc (e1_xbk_nn hτ hδ h3 h4 h5 hξ hbig b j)
    (e1_xbk_nn hτ hδ h3 h4 h5 hξ hbig b (j + 1)) hpos

theorem e1_x_zero_seg {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (b : Ex1Buffer) (j : ℕ)
    (h0 : (traj τ hτ' δ hδ' ξ).x b (bk τ δ ξ j) = 0)
    (h1 : (traj τ hτ' δ hδ' ξ).x b (bk τ δ ξ (j + 1)) = 0) :
    ∀ t, bk τ δ ξ j ≤ t → t ≤ bk τ δ ξ (j + 1) → (traj τ hτ' δ hδ' ξ).x b t = 0 := by
  obtain ⟨c, hc⟩ := e1_xaff hτ hδ h3 h4 h5 hξ hbig (hτ' := hτ') (hδ' := hδ') b j
  exact aff_zero ((e1_bk_mono hτ hδ h3 h4 h5 hξ hbig) (Nat.lt_succ_self j)) hc h0 h1

end C1X
end KSR


namespace KSR
open KumarSeidman.Reentrant C1E

section C1Proc
variable {τ δ : Fin 4 → ℝ} {hτ : ∀ k, 0 < τ k} {hδ : ∀ k, 0 < δ k} {ξ : ℝ}

theorem βf_ne (m : Fin 2) (k : ℕ) : βf m k ≠ βf m (k + 1) := by
  simp only [βf]
  have : (k + 1) % 2 = 1 ↔ ¬ k % 2 = 1 := by omega
  fin_cases m <;> simp only [Fin.zero_eta, Fin.mk_one, if_true, one_ne_zero, if_false] <;>
    split_ifs <;> simp_all

theorem e1_pS (m : Fin 2) (k : ℕ) :
    (traj τ hτ δ hδ ξ).procStart m (k + 1) = bk τ δ ξ (sidx m (k + 1)) + δ (βf m (k + 1)).2 := by
  simp only [Trajectory.procStart, Trajectory.setupTime, e1_ts, e1_tβ, S1, ex1]
  rw [if_neg (βf_ne m k)]

theorem e1_pS0 (m : Fin 2) : (traj τ hτ δ hδ ξ).procStart m 0 = 0 := by
  simp [Trajectory.procStart, Trajectory.setupTime, e1_ts, sidx_zero, e1_bk_zero]

theorem bk_add (n k : ℕ) (hk : k < 11) :
    bk τ δ ξ (12 * n + (k + 1)) = bk τ δ ξ (12 * n + k) +
      (Uc τ δ (k + 1) (xs τ δ ξ n) - Uc τ δ k (xs τ δ ξ n)) := by
  rw [e1_bk_cyc n (k + 1) (by omega), e1_bk_cyc n k (by omega)]; ring

theorem pS_0odd (n : ℕ) : (traj τ hτ δ hδ ξ).procStart 0 (2 * n + 1) = bk τ δ ξ (12 * n + 1) := by
  rw [e1_pS 0 (2 * n), sidx0_odd, show (12 * n + 1) = 12 * n + (0 + 1) by ring, bk_add n 0 (by omega)]
  simp [βf, Uc]
theorem pS_0even (n : ℕ) : (traj τ hτ δ hδ ξ).procStart 0 (2 * n + 2) = bk τ δ ξ (12 * n + 6) := by
  rw [show 2 * n + 2 = 2 * n + 1 + 1 by ring, e1_pS 0 (2 * n + 1), show 2 * n + 1 + 1 = 2 * n + 2 by ring,
    sidx0_even, show (12 * n + 6) = 12 * n + (5 + 1) by ring, bk_add n 5 (by omega)]
  simp only [βf]; rw [if_pos trivial, if_neg (by omega)]
  simp [Uc]
theorem pS_1 (n r : ℕ) (hr : r < 4) : (traj τ hτ δ hδ ξ).procStart 1 (4 * n + r + 1) =
    bk τ δ ξ (12 * n + sidx1aux r + 1) := by
  rw [e1_pS 1 (4 * n + r), sidx1_r n r hr, show 12 * n + sidx1aux r + 1 = 12 * n + (sidx1aux r + 1) by ring,
    bk_add n (sidx1aux r) (by interval_cases r <;> simp [sidx1aux])]
  simp only [βf]; rw [if_neg (by decide)]
  interval_cases r
  · rw [if_pos (by omega)]; simp [Uc, sidx1aux]
  · rw [if_neg (by omega)]; simp [Uc, sidx1aux]
  · rw [if_pos (by omega)]; simp [Uc, sidx1aux]
  · rw [if_neg (by omega)]; simp [Uc, sidx1aux]

end C1Proc
end KSR

namespace KSR
open KumarSeidman.Reentrant C1E

section C1PW
variable {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hbig : xi0 τ δ ≤ ξ)
include hτ hδ h3 h4 h5 hξ hbig

theorem e1_pw {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (m : Fin 2) (k' p q : ℕ)
    (hsp : sidx m k' ≤ p) (hqs : q ≤ sidx m (k' + 1)) {σ : ℝ} (h1 : bk τ δ ξ p ≤ σ)
    (h2 : σ < bk τ δ ξ q) (b : Ex1Buffer) :
    (traj τ hτ' δ hδ' ξ).Processing m b σ ↔
      βf m k' = b ∧ (traj τ hτ' δ hδ' ξ).procStart m k' ≤ σ := by
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have := processing_iff' (T := traj τ hτ' δ hδ' ξ) (m := m) (k := k')
    (fun i j hij _ => hm.monotone (sidx_mono m hij)) (WithTop.coe_lt_top _)
    (a := σ) (w := bk τ δ ξ q) (le_trans (hm.monotone hsp) h1) (fun _ => hm.monotone hqs)
    le_rfl h2 b
  rw [this]; rfl

theorem bk_le_iff {r j : ℕ} {σ : ℝ} (h1 : bk τ δ ξ j < σ) (h2 : σ < bk τ δ ξ (j + 1)) :
    bk τ δ ξ r ≤ σ ↔ r ≤ j := by
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := hm.monotone (show j + 1 ≤ r by omega)
    linarith
  · intro h; exact le_trans (hm.monotone h) h1.le

theorem e1_proc0 {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (b : Ex1Buffer) (n k : ℕ)
    (hk : k < 12) {σ : ℝ} (h1 : bk τ δ ξ (12 * n + k) < σ) (h2 : σ < bk τ δ ξ (12 * n + k + 1)) :
    (traj τ hτ' δ hδ' ξ).Processing 0 b σ ↔
      (b = ex1Buf 0 ∧ 1 ≤ k ∧ k ≤ 4) ∨ (b = ex1Buf 3 ∧ 6 ≤ k) := by
  have hle := fun r => bk_le_iff hτ hδ h3 h4 h5 hξ hbig (r := r) h1 h2
  rcases Nat.lt_or_ge k 5 with hk5 | hk5
  · rw [e1_pw hτ hδ h3 h4 h5 hξ hbig 0 (2 * n + 1) (12 * n + k) (12 * n + k + 1)
      (by rw [sidx0_odd]; omega) (by rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, sidx0_even]; omega)
      h1.le h2, pS_0odd, hle]
    simp only [βf, if_true]
    rw [if_pos (by omega)]
    constructor
    · rintro ⟨rfl, h⟩; left; exact ⟨rfl, by omega, by omega⟩
    · rintro (⟨rfl, h, h'⟩ | ⟨h, h'⟩)
      · exact ⟨rfl, by omega⟩
      · omega
  · rw [e1_pw hτ hδ h3 h4 h5 hξ hbig 0 (2 * n + 2) (12 * n + k) (12 * n + k + 1)
      (by rw [sidx0_even]; omega)
      (by rw [show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, sidx0_odd]; omega)
      h1.le h2, pS_0even, hle]
    simp only [βf, if_true]
    rw [if_neg (by omega)]
    constructor
    · rintro ⟨rfl, h⟩; right; exact ⟨rfl, by omega⟩
    · rintro (⟨h, h', h''⟩ | ⟨rfl, h⟩)
      · omega
      · exact ⟨rfl, by omega⟩

theorem e1_proc1 {hτ' : ∀ k, 0 < τ k} {hδ' : ∀ k, 0 < δ k} (b : Ex1Buffer) (n k : ℕ)
    (hk : k < 12) {σ : ℝ} (h1 : bk τ δ ξ (12 * n + k) < σ) (h2 : σ < bk τ δ ξ (12 * n + k + 1)) :
    (traj τ hτ' δ hδ' ξ).Processing 1 b σ ↔
      (b = ex1Buf 2 ∧ (k = 0 ∨ k = 5 ∨ k = 6 ∨ k = 10 ∨ k = 11)) ∨
      (b = ex1Buf 1 ∧ (k = 2 ∨ k = 3 ∨ k = 8)) := by
  have hle := fun r => bk_le_iff hτ hδ h3 h4 h5 hξ hbig (r := r) h1 h2
  have b1 : βf 1 (4 * n + 0 + 1) = ex1Buf 1 := by simp only [βf]; rw [if_neg (by decide), if_pos (by omega)]
  have b2 : βf 1 (4 * n + 1 + 1) = ex1Buf 2 := by simp only [βf]; rw [if_neg (by decide), if_neg (by omega)]
  have b3 : βf 1 (4 * n + 2 + 1) = ex1Buf 1 := by simp only [βf]; rw [if_neg (by decide), if_pos (by omega)]
  have b4 : βf 1 (4 * n + 3 + 1) = ex1Buf 2 := by simp only [βf]; rw [if_neg (by decide), if_neg (by omega)]
  have nB : ex1Buf 1 ≠ ex1Buf 2 := ne12
  have run_r : ∀ r, r < 4 → ∀ p q, sidx1aux r ≤ p → q ≤ (if r = 3 then 13 else sidx1aux (r + 1)) →
      12 * n + p ≤ 12 * n + k → 12 * n + k + 1 ≤ 12 * n + q →
      ((traj τ hτ' δ hδ' ξ).Processing 1 b σ ↔ βf 1 (4 * n + r + 1) = b ∧
        12 * n + sidx1aux r + 1 ≤ 12 * n + k) := by
    intro r hr p q hp hq hpk hqk
    rw [e1_pw hτ hδ h3 h4 h5 hξ hbig 1 (4 * n + r + 1) (12 * n + k) (12 * n + k + 1)
      (by rw [sidx1_r n r hr]; omega) (by
        rcases Nat.lt_or_ge r 3 with h | h
        · rw [show 4 * n + r + 1 + 1 = 4 * n + (r + 1) + 1 by ring, sidx1_r n (r + 1) (by omega)]
          rw [if_neg (by omega)] at hq; omega
        · obtain rfl : r = 3 := by omega
          rw [show 4 * n + 3 + 1 + 1 = 4 * (n + 1) + 0 + 1 by ring, sidx1_r (n + 1) 0 (by omega)]
          simp only [sidx1aux, if_true] at hq ⊢; omega) h1.le h2, pS_1 n r hr, hle]
  have fin : ∀ (P : Prop) (c : Bool), (P ↔ True) → True := fun _ _ _ => trivial
  interval_cases k
  · -- k = 0: run 4n
    rcases n with _ | n
    · rw [e1_pw hτ hδ h3 h4 h5 hξ hbig 1 0 0 1 (by simp [sidx_zero])
        (by rw [show (0 : ℕ) + 1 = 4 * 0 + 0 + 1 by rfl, sidx1_r 0 0 (by omega)]; simp [sidx1aux])
        (by simpa using h1.le) (by simpa using h2), e1_pS0]
      have hσ : 0 ≤ σ := by
        have := h1.le; simp only [Nat.mul_zero, Nat.add_zero, e1_bk_zero] at this; exact this
      have hb0 : βf 1 0 = ex1Buf 2 := by simp [βf]
      rw [hb0]
      constructor
      · rintro ⟨rfl, -⟩; left; exact ⟨rfl, by first | decide | omega⟩
      · rintro (⟨rfl, -⟩ | ⟨rfl, h⟩)
        · exact ⟨rfl, hσ⟩
        · omega
    · rw [e1_pw hτ hδ h3 h4 h5 hξ hbig 1 (4 * n + 3 + 1) (12 * (n + 1) + 0) (12 * (n + 1) + 0 + 1)
        (by rw [sidx1_r n 3 (by omega)]; simp [sidx1aux]; omega)
        (by rw [show 4 * n + 3 + 1 + 1 = 4 * (n + 1) + 0 + 1 by ring, sidx1_r (n + 1) 0 (by omega)]
            simp [sidx1aux])
        h1.le h2, pS_1 n 3 (by omega)]
      rw [show (12 * n + sidx1aux 3 + 1) = 12 * n + 10 by simp [sidx1aux],
        bk_le_iff hτ hδ h3 h4 h5 hξ hbig (r := 12 * n + 10) h1 h2]
      have b4' : βf 1 (4 * n + 3 + 1) = ex1Buf 2 := by
        simp only [βf]; rw [if_neg (by decide), if_neg (by omega)]
      rw [b4']
      constructor
      · rintro ⟨rfl, -⟩; left; exact ⟨rfl, by first | decide | omega⟩
      · rintro (⟨rfl, -⟩ | ⟨rfl, h⟩)
        · exact ⟨rfl, by first | decide | omega⟩
        · omega
  · rw [run_r 0 (by omega) 1 4 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b1]
    simp only [sidx1aux]
    constructor
    · rintro ⟨-, h⟩; omega
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
  · rw [run_r 0 (by omega) 1 4 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b1]
    simp only [sidx1aux]
    constructor
    · rintro ⟨rfl, -⟩; right; exact ⟨rfl, by first | decide | omega⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, -⟩)
      · omega
      · exact ⟨rfl, by first | decide | omega⟩
  · rw [run_r 0 (by omega) 1 4 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b1]
    simp only [sidx1aux]
    constructor
    · rintro ⟨rfl, -⟩; right; exact ⟨rfl, by first | decide | omega⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, -⟩)
      · omega
      · exact ⟨rfl, by first | decide | omega⟩
  · rw [run_r 1 (by omega) 4 7 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b2]
    simp only [sidx1aux]
    constructor
    · rintro ⟨-, h⟩; omega
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
  · rw [run_r 1 (by omega) 4 7 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b2]
    simp only [sidx1aux]
    constructor
    · rintro ⟨rfl, -⟩; left; exact ⟨rfl, by first | decide | omega⟩
    · rintro (⟨rfl, -⟩ | ⟨rfl, h⟩)
      · exact ⟨rfl, by first | decide | omega⟩
      · omega
  · rw [run_r 1 (by omega) 4 7 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b2]
    simp only [sidx1aux]
    constructor
    · rintro ⟨rfl, -⟩; left; exact ⟨rfl, by first | decide | omega⟩
    · rintro (⟨rfl, -⟩ | ⟨rfl, h⟩)
      · exact ⟨rfl, by first | decide | omega⟩
      · omega
  · rw [run_r 2 (by omega) 7 9 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b3]
    simp only [sidx1aux]
    constructor
    · rintro ⟨-, h⟩; omega
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
  · rw [run_r 2 (by omega) 7 9 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b3]
    simp only [sidx1aux]
    constructor
    · rintro ⟨rfl, -⟩; right; exact ⟨rfl, by first | decide | omega⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, -⟩)
      · omega
      · exact ⟨rfl, by first | decide | omega⟩
  · rw [run_r 3 (by omega) 9 13 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b4]
    simp only [sidx1aux]
    constructor
    · rintro ⟨-, h⟩; omega
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
  · rw [run_r 3 (by omega) 9 13 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b4]
    simp only [sidx1aux]
    constructor
    · rintro ⟨rfl, -⟩; left; exact ⟨rfl, by first | decide | omega⟩
    · rintro (⟨rfl, -⟩ | ⟨rfl, h⟩)
      · exact ⟨rfl, by first | decide | omega⟩
      · omega
  · rw [run_r 3 (by omega) 9 13 (by simp [sidx1aux]) (by simp [sidx1aux]) (by omega) (by omega), b4]
    simp only [sidx1aux]
    constructor
    · rintro ⟨rfl, -⟩; left; exact ⟨rfl, by first | decide | omega⟩
    · rintro (⟨rfl, -⟩ | ⟨rfl, h⟩)
      · exact ⟨rfl, by first | decide | omega⟩
      · omega

end C1PW
end KSR

namespace KSR
open KumarSeidman.Reentrant C1E

theorem sidx_ge (m : Fin 2) (k : ℕ) : k ≤ sidx m k + 1 := by
  fin_cases m
  · show k ≤ sidx 0 k + 1
    rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
    · rcases n with _ | n
      · simp
      · rw [show 2 * (n + 1) = 2 * n + 2 by ring, sidx0_even]; omega
    · rw [sidx0_odd]; omega
  · show k ≤ sidx 1 k + 1
    rcases k with _ | k
    · simp
    · have hk : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
      have hr : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rw [hk, sidx1_r _ _ hr]
      have : k % 4 ≤ sidx1aux (k % 4) := by
        generalize k % 4 = r at hr; interval_cases r <;> simp [sidx1aux]
      omega

section C1T
variable {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hbig : xi0 τ δ ≤ ξ)
include hτ hδ h3 h4 h5 hξ hbig

theorem e1_setup_ok (m : Fin 2) (k : ℕ) :
    (traj τ hτ δ hδ ξ).procStart m k ≤ (traj τ hτ δ hδ ξ).s m (k + 1) := by
  have hm := (e1_bk_mono hτ hδ h3 h4 h5 hξ hbig).monotone
  rw [e1_ts]
  rcases k with _ | k
  · rw [e1_pS0, ← e1_bk_zero (τ := τ) (δ := δ) (ξ := ξ)]; exact hm (Nat.zero_le _)
  fin_cases m
  · show (traj τ hτ δ hδ ξ).procStart 0 (k + 1) ≤ bk τ δ ξ (sidx 0 (k + 1 + 1))
    rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
    · rw [pS_0odd, show 2 * n + 1 + 1 = 2 * n + 2 by ring, sidx0_even]; exact hm (by omega)
    · rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring, pS_0even,
        show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, sidx0_odd]; exact hm (by omega)
  · show (traj τ hτ δ hδ ξ).procStart 1 (k + 1) ≤ bk τ δ ξ (sidx 1 (k + 1 + 1))
    have hk : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
    have hr : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [hk, pS_1 _ _ hr]
    rcases Nat.lt_or_ge (k % 4) 3 with h | h
    · rw [show 4 * (k / 4) + k % 4 + 1 + 1 = 4 * (k / 4) + (k % 4 + 1) + 1 by ring,
        sidx1_r _ _ (by omega)]
      apply hm
      have : sidx1aux (k % 4) + 1 ≤ sidx1aux (k % 4 + 1) := by
        generalize k % 4 = r at h; interval_cases r <;> simp [sidx1aux]
      omega
    · have e3 : k % 4 = 3 := by omega
      rw [e3, show 4 * (k / 4) + 3 + 1 + 1 = 4 * (k / 4 + 1) + 0 + 1 by ring,
        sidx1_r (k / 4 + 1) 0 (by omega)]
      apply hm; simp [sidx1aux]; omega

omit hξ hbig in
theorem e1_osl_bounds (i : Fin 4) (k : ℕ) : 0 ≤ osl τ i k ∧ osl τ i k ≤ 1 / τ i := by
  obtain ⟨h01, h23, h0lt, h1lt, h2lt, h3lt⟩ := c2_basic hτ h3 h4 h5
  have t0 := hτ 0; have t1 := hτ 1; have t2 := hτ 2; have t3 := hτ 3
  have g0 : 1 ≤ 1 / τ 0 := by rw [le_one_div (by norm_num) t0]; linarith
  have g0' : 1 ≤ (τ 0)⁻¹ := by simpa using g0
  have p0 : 0 ≤ (τ 0)⁻¹ := by positivity
  have p1 : 0 ≤ (τ 1)⁻¹ := by positivity
  have p2 : 0 ≤ (τ 2)⁻¹ := by positivity
  have p3 : 0 ≤ (τ 3)⁻¹ := by positivity
  constructor <;>
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl <;>
  · unfold osl
    split <;> simp_all

theorem e1_isTraj : IsTrajectory (S1 τ hτ δ hδ) (traj τ hτ δ hδ ξ) := by
  have hmono := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have hunb := e1_bk_unb hτ hδ h3 h4 h5 hξ (δ := δ)
  have hb0 : bk τ δ ξ 0 = 0 := e1_bk_zero
  have yz := e1_yf_zero hτ hδ h3 h4 h5 hξ hbig
  have hin0 : ∀ b : Ex1Buffer, (S1 τ hτ δ hδ).input (traj τ hτ δ hδ ξ).y b 0 = 0 := by
    intro b
    rw [ex1_buf_eq b]
    generalize b.2 = i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl
    · rw [ex1_input0]
    · rw [ex1_input1, e1_ty]; exact yz 0
    · rw [ex1_input2, e1_ty]; exact yz 1
    · rw [ex1_input3, e1_ty]; exact yz 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b; rw [e1_ty]; exact yz _
  · intro b
    rw [e1_ty]
    exact seg_mono hb0 hmono hunb (fun t _ => rfl)
      (fun j => (e1_osl_bounds hτ hδ h3 h4 h5 _ _).1)
  · intro b t _
    have e := hin0 b
    have hy := yz b.2
    simp only [traj] at e ⊢
    rw [e, hy]; ring
  · intro b t ht; exact e1_x_nn hτ hδ h3 h4 h5 hξ hbig b t ht
  · intro m; exact WithTop.coe_lt_top _
  · intro m; rw [e1_ts, sidx_zero, hb0]
  · intro m k _
    rw [e1_tβ]
    simp only [βf]
    fin_cases m <;> split_ifs <;> first | rfl | (exfalso; simp_all)
  · intro m k _; exact e1_setup_ok hτ hδ h3 h4 h5 hξ hbig m k
  · intro m t
    obtain ⟨J, hJ⟩ := hunb t
    apply Set.Finite.subset (Set.finite_lt_nat (J + 1))
    intro k ⟨_, hk⟩
    simp only [Set.mem_setOf_eq]
    by_contra hcon
    push Not at hcon
    have : bk τ δ ξ J ≤ (traj τ hτ δ hδ ξ).s m k := by
      rw [e1_ts]; apply hmono.monotone; have := sidx_ge m k; omega
    linarith
  · intro bb s t hs hst
    exact seg_cap hb0 hmono hunb (traj τ hτ δ hδ ξ) bb (sl := fun j => osl τ bb.2 (j % 12))
      (fun t _ => rfl) (fun j => e1_osl_bounds hτ hδ h3 h4 h5 _ _) (by
        intro j hpos σ h1 h2
        obtain ⟨n, r, hr, rfl⟩ : ∃ n r, r < 12 ∧ j = 12 * n + r :=
          ⟨j / 12, j % 12, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 12).symm⟩
        have hr' : (12 * n + r) % 12 = r := by omega
        rw [hr'] at hpos
        rw [ex1_buf_eq bb] at hpos ⊢
        generalize bb.2 = i at hpos ⊢
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl
        · rw [r1B0, e1_proc0 hτ hδ h3 h4 h5 hξ hbig _ n r hr h1 h2]
          interval_cases r <;> simp_all [osl]
        · rw [r1B1, e1_proc1 hτ hδ h3 h4 h5 hξ hbig _ n r hr h1 h2]
          interval_cases r <;> simp_all [osl]
        · rw [r1B2, e1_proc1 hτ hδ h3 h4 h5 hξ hbig _ n r hr h1 h2]
          interval_cases r <;> simp_all [osl]
        · rw [r1B3, e1_proc0 hτ hδ h3 h4 h5 hξ hbig _ n r hr h1 h2]
          interval_cases r <;> simp_all [osl]) s t hs hst
  · intro bb s t hs hst hall
    exact seg_full hb0 hmono hunb (traj τ hτ δ hδ ξ) bb (sl := fun j => osl τ bb.2 (j % 12))
      (fun t _ => rfl) (by
        intro j σ h1 h2 hP hx
        obtain ⟨n, r, hr, rfl⟩ : ∃ n r, r < 12 ∧ j = 12 * n + r :=
          ⟨j / 12, j % 12, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 12).symm⟩
        have hr' : (12 * n + r) % 12 = r := by omega
        rw [hr']
        have xv := fun i k hk => e1_xv hτ hδ h3 h4 h5 hξ hbig (hτ' := hτ) (hδ' := hδ) i n k hk
        obtain ⟨-, -, -, a3, a4, a5, -⟩ := Xv0_tab hτ hδ h3 h4 h5 (xs τ δ ξ n)
        obtain ⟨c0, c1, -, -, -, -, -, -, -, -, -, c11, c12⟩ := Xv2_tab hτ hδ h3 h4 h5 (xs τ δ ξ n)
        rw [ex1_buf_eq bb] at hP hx ⊢
        generalize bb.2 = i at hP hx ⊢
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by fin_cases i <;> simp) with rfl | rfl | rfl | rfl
        · rw [r1B0, e1_proc0 hτ hδ h3 h4 h5 hξ hbig _ n r hr h1 h2] at hP
          have hz : r = 3 ∨ r = 4 → (traj τ hτ δ hδ ξ).x (ex1Buf 0) σ = 0 := by
            intro hr34
            apply e1_x_zero_seg hτ hδ h3 h4 h5 hξ hbig (ex1Buf 0) (12 * n + r) _ _ σ h1.le h2.le
            · rw [xv 0 r (by omega)]; rcases hr34 with rfl | rfl <;> assumption
            · rw [show 12 * n + r + 1 = 12 * n + (r + 1) by ring, xv 0 (r + 1) (by omega)]
              rcases hr34 with rfl | rfl <;> assumption
          interval_cases r <;> simp_all [osl]
        · rw [r1B1, e1_proc1 hτ hδ h3 h4 h5 hξ hbig _ n r hr h1 h2] at hP
          interval_cases r <;> simp_all [osl]
        · rw [r1B2, e1_proc1 hτ hδ h3 h4 h5 hξ hbig _ n r hr h1 h2] at hP
          have hz : r = 0 ∨ r = 11 → (traj τ hτ δ hδ ξ).x (ex1Buf 2) σ = 0 := by
            intro hr34
            apply e1_x_zero_seg hτ hδ h3 h4 h5 hξ hbig (ex1Buf 2) (12 * n + r) _ _ σ h1.le h2.le
            · rw [xv 2 r (by omega)]; rcases hr34 with rfl | rfl <;> assumption
            · rw [show 12 * n + r + 1 = 12 * n + (r + 1) by ring, xv 2 (r + 1) (by omega)]
              rcases hr34 with rfl | rfl <;> assumption
          interval_cases r <;> simp_all [osl]
        · rw [r1B3, e1_proc0 hτ hδ h3 h4 h5 hξ hbig _ n r hr h1 h2] at hP
          interval_cases r <;> simp_all [osl]) s t hs hst hall

end C1T
end KSR


namespace KSR
open KumarSeidman.Reentrant C1E

section C1R
variable {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hbig : xi0 τ δ ≤ ξ)
include hτ hδ h3 h4 h5 hξ hbig

theorem e1_pos_range (b : Ex1Buffer) (p q : ℕ)
    (hin : ∀ j, p < j → j < q → 0 < (traj τ hτ δ hδ ξ).x b (bk τ δ ξ j))
    (hseg : ∀ j, p ≤ j → j < q →
      0 < (traj τ hτ δ hδ ξ).x b (bk τ δ ξ j) ∨ 0 < (traj τ hτ δ hδ ξ).x b (bk τ δ ξ (j + 1))) :
    ∀ t, bk τ δ ξ p < t → t < bk τ δ ξ q → 0 < (traj τ hτ δ hδ ξ).x b t := by
  intro t h1 h2
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have ht0 : 0 ≤ t := le_trans (by rw [← e1_bk_zero (τ := τ) (δ := δ) (ξ := ξ)]; exact hm.monotone (Nat.zero_le p)) h1.le
  obtain ⟨j, hj1, hj2⟩ := seg_exists e1_bk_zero (e1_bk_unb hτ hδ h3 h4 h5 hξ) ht0
  have hpj : p ≤ j := by
    by_contra hc; push Not at hc
    have := hm.monotone (show j + 1 ≤ p by omega); linarith
  have hjq : j < q := by
    by_contra hc; push Not at hc
    have := hm.monotone hc; linarith
  rcases lt_or_eq_of_le hj1 with h | h
  · exact e1_x_pos_seg hτ hδ h3 h4 h5 hξ hbig b j (hseg j hpj hjq) t h hj2
  · rw [← h]
    rcases lt_or_eq_of_le hpj with h' | h'
    · exact hin j h' hjq
    · rw [← h'] at h; linarith

theorem e1_zero_range (b : Ex1Buffer) (p q : ℕ)
    (hz : ∀ j, p ≤ j → j ≤ q → (traj τ hτ δ hδ ξ).x b (bk τ δ ξ j) = 0) :
    ∀ t, bk τ δ ξ p ≤ t → t ≤ bk τ δ ξ q → (traj τ hτ δ hδ ξ).x b t = 0 := by
  intro t h1 h2
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have ht0 : 0 ≤ t := le_trans (by rw [← e1_bk_zero (τ := τ) (δ := δ) (ξ := ξ)]; exact hm.monotone (Nat.zero_le p)) h1
  obtain ⟨j, hj1, hj2⟩ := seg_exists e1_bk_zero (e1_bk_unb hτ hδ h3 h4 h5 hξ) ht0
  have hpj : p ≤ j := by
    by_contra hc; push Not at hc
    have := hm (show j + 1 < p + 1 by omega)
    have := hm.monotone (show j + 1 ≤ p by omega); linarith
  rcases lt_or_eq_of_le h2 with h2' | h2'
  · have hjq : j < q := by
      by_contra hc; push Not at hc
      have := hm.monotone hc; linarith
    exact e1_x_zero_seg hτ hδ h3 h4 h5 hξ hbig b j (hz j hpj hjq.le) (hz (j + 1) (by omega) hjq)
      t hj1 hj2.le
  · rw [h2']; exact hz q (hm.le_iff_le.mp (h1.trans h2'.le)) le_rfl

theorem e1_yconst_range (i : Fin 4) (p q : ℕ)
    (hz : ∀ j, p ≤ j → j < q → osl τ i (j % 12) = 0) :
    ∀ t, bk τ δ ξ p ≤ t → t ≤ bk τ δ ξ q → yf τ δ ξ i t = yf τ δ ξ i (bk τ δ ξ p) := by
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have hbk : ∀ j, p ≤ j → j ≤ q → yf τ δ ξ i (bk τ δ ξ j) = yf τ δ ξ i (bk τ δ ξ p) := by
    intro j h1 h2
    induction j, h1 using Nat.le_induction with
    | base => rfl
    | succ j hpj ih =>
      rw [e1_yf_aff hτ hδ h3 h4 h5 hξ hbig i j (hm (Nat.lt_succ_self j)).le le_rfl,
        hz j hpj (by omega), ih (by omega)]
      ring
  intro t h1 h2
  have ht0 : 0 ≤ t := le_trans (by rw [← e1_bk_zero (τ := τ) (δ := δ) (ξ := ξ)]; exact hm.monotone (Nat.zero_le p)) h1
  obtain ⟨j, hj1, hj2⟩ := seg_exists e1_bk_zero (e1_bk_unb hτ hδ h3 h4 h5 hξ) ht0
  have hpj : p ≤ j := by
    by_contra hc; push Not at hc
    have := hm.monotone (show j + 1 ≤ p by omega); linarith
  rcases lt_or_eq_of_le h2 with h2' | h2'
  · have hjq : j < q := by
      by_contra hc; push Not at hc
      have := hm.monotone hc; linarith
    rw [e1_yf_aff hτ hδ h3 h4 h5 hξ hbig i j hj1 hj2.le, hz j hpj hjq, hbk j hpj hjq.le]; ring
  · rw [h2']; exact hbk q (hm.le_iff_le.mp (h1.trans h2'.le)) le_rfl

end C1R
end KSR

namespace KSR
open KumarSeidman.Reentrant C1E

section C1Cl
variable {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hbig : xi0 τ δ ≤ ξ)
include hτ hδ h3 h4 h5 hξ hbig

theorem e1_dem_inc (i : Fin 4) (b : Ex1Buffer)
    (hin : ∀ t, (S1 τ hτ δ hδ).input (traj τ hτ δ hδ ξ).y b t = yf τ δ ξ i t)
    (j : ℕ) (hpos : 0 < osl τ i (j % 12)) :
    (traj τ hτ δ hδ ξ).Demanding b (bk τ δ ξ j) := by
  have hT := e1_isTraj hτ hδ h3 h4 h5 hξ hbig
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have hj0 : 0 ≤ bk τ δ ξ j := by
    rw [← e1_bk_zero (τ := τ) (δ := δ) (ξ := ξ)]; exact hm.monotone (Nat.zero_le j)
  apply demanding_of_incr hT b hj0 (hm (Nat.lt_succ_self j)) _ (input_mono hT b)
  intro σ h1 h2
  rw [hin, hin, e1_yf_aff hτ hδ h3 h4 h5 hξ hbig i j h1.le h2]
  have : 0 < osl τ i (j % 12) * (σ - bk τ δ ξ j) := mul_pos hpos (by linarith)
  linarith

theorem e1_notdem (b : Ex1Buffer) (i : Fin 4)
    (hin : ∀ t, (S1 τ hτ δ hδ).input (traj τ hτ δ hδ ξ).y b t = yf τ δ ξ i t)
    (p q : ℕ) (hz : ∀ j, p ≤ j → j < q → osl τ i (j % 12) = 0) {t : ℝ}
    (h1 : bk τ δ ξ p ≤ t) (h2 : t < bk τ δ ξ q) (hx : (traj τ hτ δ hδ ξ).x b t = 0) :
    ¬ (traj τ hτ δ hδ ξ).Demanding b t := by
  have hc := e1_yconst_range hτ hδ h3 h4 h5 hξ hbig i p q hz
  apply notdem hx h2
  rw [hin, hin, hc t h1 h2.le, hc _ (h1.trans h2.le) le_rfl]

end C1Cl
end KSR

namespace KSR
open KumarSeidman.Reentrant C1E

section C1Cl2
variable {τ δ : Fin 4 → ℝ} (hτ : ∀ k, 0 < τ k) (hδ : ∀ k, 0 < δ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) {ξ : ℝ} (hξ : 0 < ξ)
    (hbig : xi0 τ δ ≤ ξ)
include hτ hδ h3 h4 h5 hξ hbig

theorem e1_in1 (t : ℝ) : (S1 τ hτ δ hδ).input (traj τ hτ δ hδ ξ).y (ex1Buf 1) t = yf τ δ ξ 0 t := by
  rw [ex1_input1, e1_ty]; rfl
theorem e1_in2 (t : ℝ) : (S1 τ hτ δ hδ).input (traj τ hτ δ hδ ξ).y (ex1Buf 2) t = yf τ δ ξ 1 t := by
  rw [ex1_input2, e1_ty]; rfl
theorem e1_in3 (t : ℝ) : (S1 τ hτ δ hδ).input (traj τ hτ δ hδ ξ).y (ex1Buf 3) t = yf τ δ ξ 2 t := by
  rw [ex1_input3, e1_ty]; rfl

theorem e1_cl0 (k : ℕ) :
    (∀ t : ℝ, (traj τ hτ δ hδ ξ).procStart 0 k < t →
      ((traj τ hτ δ hδ ξ).RunExists 0 (k + 1) → t < (traj τ hτ δ hδ ξ).s 0 (k + 1)) →
      ¬ ((traj τ hτ δ hδ ξ).x ((traj τ hτ δ hδ ξ).β 0 k) t = 0 ∧
          ∃ b', (S1 τ hτ δ hδ).route b' = 0 ∧ b' ≠ (traj τ hτ δ hδ ξ).β 0 k ∧
            (traj τ hτ δ hδ ξ).Demanding b' t)) ∧
    ((traj τ hτ δ hδ ξ).RunExists 0 (k + 1) →
      (traj τ hτ δ hδ ξ).x ((traj τ hτ δ hδ ξ).β 0 k) ((traj τ hτ δ hδ ξ).s 0 (k + 1)) = 0 ∧
        (traj τ hτ δ hδ ξ).β 0 (k + 1) ≠ (traj τ hτ δ hδ ξ).β 0 k ∧
        (traj τ hτ δ hδ ξ).Demanding ((traj τ hτ δ hδ ξ).β 0 (k + 1))
          ((traj τ hτ δ hδ ξ).s 0 (k + 1))) := by
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have xv := fun (i : Fin 4) n k hk =>
    e1_xv hτ hδ h3 h4 h5 hξ hbig (hτ' := hτ) (hδ' := hδ) i n k hk
  have hR : ∀ j, (traj τ hτ δ hδ ξ).RunExists 0 j := fun j => WithTop.coe_lt_top _
  simp only [e1_ts, e1_tβ]
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · rcases n with _ | n
    · -- run 0
      have e1 : sidx 0 (2 * 0 + 1) = 0 := by rw [sidx0_odd]
      simp only [Nat.mul_zero, Nat.zero_add] at e1 ⊢
      rw [e1, e1_pS0, e1_bk_zero]
      have b0 : βf 0 0 = ex1Buf 3 := by simp [βf]
      have b1 : βf 0 1 = ex1Buf 0 := by simp [βf]
      rw [b0, b1]
      refine ⟨fun t h1 h2 => absurd (h2 (hR _)) (by linarith), fun _ => ⟨?_, by simp, dem0 _⟩⟩
      have := xv 3 0 0 (by norm_num)
      simp only [Nat.mul_zero, Nat.add_zero, e1_bk_zero] at this
      rw [this, (Xv3_tab hτ hδ h3 h4 h5 _).1]
    · -- run 2n+2 (buffer 4)
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pS_0even, show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring,
        sidx0_odd]
      have b0 : βf 0 (2 * n + 2) = ex1Buf 3 := by
        simp only [βf]; rw [if_pos trivial, if_neg (by omega)]
      have b1 : βf 0 (2 * (n + 1) + 1) = ex1Buf 0 := by
        simp only [βf]; rw [if_pos trivial, if_pos (by omega)]
      rw [b0, b1]
      obtain ⟨-, -, -, ⟨p6, p7, p8, p9, p10, p11⟩⟩ :=
        e1_Xv_pos hτ hδ h3 h4 h5 (e1_xs_big hτ hδ h3 h4 h5 hξ hbig n)
      refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, dem0 _⟩⟩
      · have h2' := h2 (hR _)
        have hpos := e1_pos_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 3) (12 * n + 6) (12 * (n + 1))
          (by
            intro j hj1 hj2
            obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
            have hk' : 7 ≤ k' ∧ k' ≤ 11 := by omega
            rw [xv 3 n k' (by omega)]
            obtain ⟨hk1, hk2⟩ := hk'
            interval_cases k' <;> assumption)
          (by
            intro j hj1 hj2
            obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
            left
            rw [xv 3 n k' (by omega)]
            have hk' : 6 ≤ k' ∧ k' ≤ 11 := by omega
            obtain ⟨hk1, hk2⟩ := hk'
            interval_cases k' <;> assumption) t h1 h2'
        rw [hc.1] at hpos; exact lt_irrefl _ hpos
      · rw [show 12 * (n + 1) = 12 * n + 12 by ring, xv 3 n 12 (by norm_num), Xv3_12 hτ hδ h3 h4 h5]
  · -- run 2n+1 (buffer 1)
    rw [pS_0odd, show 2 * n + 1 + 1 = 2 * n + 2 by ring, sidx0_even]
    have b0 : βf 0 (2 * n + 1) = ex1Buf 0 := by
      simp only [βf]; rw [if_pos trivial, if_pos (by omega)]
    have b1 : βf 0 (2 * n + 2) = ex1Buf 3 := by
      simp only [βf]; rw [if_pos trivial, if_neg (by omega)]
    rw [b0, b1]
    obtain ⟨⟨q0, q1, q2, -⟩, -, -, -⟩ :=
      e1_Xv_pos hτ hδ h3 h4 h5 (e1_xs_big hτ hδ h3 h4 h5 hξ hbig n)
    obtain ⟨-, -, -, a3, a4, a5, -⟩ := Xv0_tab hτ hδ h3 h4 h5 (xs τ δ ξ n)
    obtain ⟨-, -, -, e3, e4, e5, -⟩ := Xv3_tab hτ hδ h3 h4 h5 (xs τ δ ξ n)
    refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, ?_⟩⟩
    · have h2' := h2 (hR _)
      rcases lt_or_ge t (bk τ δ ξ (12 * n + 3)) with h | h
      · have hpos := e1_pos_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 0) (12 * n + 1) (12 * n + 3)
          (by
            intro j hj1 hj2
            obtain rfl : j = 12 * n + 2 := by omega
            rw [xv 0 n 2 (by norm_num)]; exact q2)
          (by
            intro j hj1 hj2
            left
            obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
            have hk' : 1 ≤ k' ∧ k' ≤ 2 := by omega
            rw [xv 0 n k' (by omega)]
            obtain ⟨hk1, hk2⟩ := hk'
            interval_cases k' <;> assumption) t h1 h
        rw [hc.1] at hpos; exact lt_irrefl _ hpos
      · obtain ⟨b', hb'r, hb'ne, hb'd⟩ := hc.2
        rcases ex1_m0 hb'r with hb | hb
        · exact hb'ne hb
        rw [hb] at hb'd
        have hx3 := e1_zero_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 3) (12 * n + 3) (12 * n + 5)
          (by
            intro j hj1 hj2
            obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
            have hk' : 3 ≤ k' ∧ k' ≤ 5 := by omega
            rw [xv 3 n k' (by omega)]
            obtain ⟨hk1, hk2⟩ := hk'
            interval_cases k' <;> assumption) t h h2'.le
        refine e1_notdem hτ hδ h3 h4 h5 hξ hbig (ex1Buf 3) 2 (e1_in3 hτ hδ h3 h4 h5 hξ hbig)
          (12 * n + 3) (12 * n + 5) ?_ h h2' hx3 hb'd
        intro j hj1 hj2
        obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
        have : (12 * n + k') % 12 = k' := by omega
        rw [this]
        have hk' : 3 ≤ k' ∧ k' ≤ 4 := by omega
        obtain ⟨hk1, hk2⟩ := hk'
        interval_cases k' <;> simp [osl]
    · rw [xv 0 n 5 (by norm_num), a5]
    · apply e1_dem_inc hτ hδ h3 h4 h5 hξ hbig 2 (ex1Buf 3) (e1_in3 hτ hδ h3 h4 h5 hξ hbig)
      rw [show (12 * n + 5) % 12 = 5 by omega]
      simp [osl]; exact hτ 2

theorem e1_cl1 (k : ℕ) :
    (∀ t : ℝ, (traj τ hτ δ hδ ξ).procStart 1 k < t →
      ((traj τ hτ δ hδ ξ).RunExists 1 (k + 1) → t < (traj τ hτ δ hδ ξ).s 1 (k + 1)) →
      ¬ ((traj τ hτ δ hδ ξ).x ((traj τ hτ δ hδ ξ).β 1 k) t = 0 ∧
          ∃ b', (S1 τ hτ δ hδ).route b' = 1 ∧ b' ≠ (traj τ hτ δ hδ ξ).β 1 k ∧
            (traj τ hτ δ hδ ξ).Demanding b' t)) ∧
    ((traj τ hτ δ hδ ξ).RunExists 1 (k + 1) →
      (traj τ hτ δ hδ ξ).x ((traj τ hτ δ hδ ξ).β 1 k) ((traj τ hτ δ hδ ξ).s 1 (k + 1)) = 0 ∧
        (traj τ hτ δ hδ ξ).β 1 (k + 1) ≠ (traj τ hτ δ hδ ξ).β 1 k ∧
        (traj τ hτ δ hδ ξ).Demanding ((traj τ hτ δ hδ ξ).β 1 (k + 1))
          ((traj τ hτ δ hδ ξ).s 1 (k + 1))) := by
  have hm := e1_bk_mono hτ hδ h3 h4 h5 hξ hbig
  have xv := fun (i : Fin 4) n k hk =>
    e1_xv hτ hδ h3 h4 h5 hξ hbig (hτ' := hτ) (hδ' := hδ) i n k hk
  have hR : ∀ j, (traj τ hτ δ hδ ξ).RunExists 1 j := fun j => WithTop.coe_lt_top _
  have t0 := hτ 0; have t2 := hτ 2
  have d2 := hδ 2
  simp only [e1_ts, e1_tβ]
  have bodd : ∀ j, j % 2 = 1 → βf 1 j = ex1Buf 1 := fun j hj => by
    simp only [βf]; rw [if_neg (by decide), if_pos hj]
  have beven : ∀ j, ¬ j % 2 = 1 → βf 1 j = ex1Buf 2 := fun j hj => by
    simp only [βf]; rw [if_neg (by decide), if_neg hj]
  rcases k with _ | k
  · -- run 0 (buffer 3, idle)
    rw [e1_pS0, show (0 : ℕ) + 1 = 4 * 0 + 0 + 1 by rfl, sidx1_r 0 0 (by omega),
      beven 0 (by omega), bodd 1 (by omega)]
    simp only [sidx1aux, Nat.mul_zero, Nat.zero_add]
    obtain ⟨b0, b1, -⟩ := Xv1_tab hτ hδ h3 h4 h5 (xs τ δ ξ 0)
    obtain ⟨c0, c1, -⟩ := Xv2_tab hτ hδ h3 h4 h5 (xs τ δ ξ 0)
    refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, ?_⟩⟩
    · have h2' := h2 (hR _)
      obtain ⟨b', hb'r, hb'ne, hb'd⟩ := hc.2
      rcases ex1_m1 hb'r with hb | hb
      swap
      · exact hb'ne hb
      rw [hb] at hb'd
      have hb0 : bk τ δ ξ 0 ≤ t := by rw [e1_bk_zero]; linarith
      have hx1 := e1_zero_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 1) 0 1
        (by
          intro j hj1 hj2
          interval_cases j
          · have := xv 1 0 0 (by norm_num); simp only [Nat.mul_zero, Nat.add_zero] at this
            rw [this, b0]
          · have := xv 1 0 1 (by norm_num); simp only [Nat.mul_zero, Nat.zero_add] at this
            rw [this, b1]) t hb0 h2'.le
      refine e1_notdem hτ hδ h3 h4 h5 hξ hbig (ex1Buf 1) 0 (e1_in1 hτ hδ h3 h4 h5 hξ hbig)
        0 1 ?_ hb0 h2' hx1 hb'd
      intro j hj1 hj2
      obtain rfl : j = 0 := by omega
      simp [osl]
    · have := xv 2 0 1 (by norm_num); simp only [Nat.mul_zero, Nat.zero_add] at this
      rw [this, c1]
    · apply e1_dem_inc hτ hδ h3 h4 h5 hξ hbig 0 (ex1Buf 1) (e1_in1 hτ hδ h3 h4 h5 hξ hbig)
      simp [osl]; exact t0
  · have hk : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
    have hr : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    generalize hn : k / 4 = n at hk
    generalize hrr : k % 4 = r at hk hr
    subst hk
    obtain ⟨-, ⟨p12, p13, p15, p16, p17, p18⟩, ⟨p23, p24, p25, p26, p29, p210⟩, -⟩ :=
      e1_Xv_pos hτ hδ h3 h4 h5 (e1_xs_big hτ hδ h3 h4 h5 hξ hbig n)
    obtain ⟨-, -, -, -, b4, -, -, -, -, b9, -, b11, b12⟩ := Xv1_tab hτ hδ h3 h4 h5 (xs τ δ ξ n)
    obtain ⟨-, -, -, -, -, -, -, c7, -, -, -, -, -⟩ := Xv2_tab hτ hδ h3 h4 h5 (xs τ δ ξ n)
    obtain ⟨b0', b1', -⟩ := Xv1_tab hτ hδ h3 h4 h5 (xs τ δ ξ (n + 1))
    obtain ⟨c0', c1', -⟩ := Xv2_tab hτ hδ h3 h4 h5 (xs τ δ ξ (n + 1))
    rw [pS_1 n r hr]
    interval_cases r
    · -- run 4n+1: buffer 2
      rw [sidx1_r n 1 (by omega), bodd _ (by omega), beven _ (by omega)]
      simp only [sidx1aux]
      refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, Or.inl ?_⟩⟩
      · have h2' := h2 (hR _)
        have hpos := e1_pos_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 1) (12 * n + 2) (12 * n + 4)
          (by
            intro j hj1 hj2
            obtain rfl : j = 12 * n + 3 := by omega
            rw [xv 1 n 3 (by norm_num)]; exact p13)
          (by
            intro j hj1 hj2
            left
            obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
            have hk' : 2 ≤ k' ∧ k' ≤ 3 := by omega
            rw [xv 1 n k' (by omega)]
            obtain ⟨hk1, hk2⟩ := hk'
            interval_cases k' <;> assumption) t (by simpa using h1) (by simpa using h2')
        rw [hc.1] at hpos; exact lt_irrefl _ hpos
      · rw [xv 1 n 4 (by norm_num), b4]
      · rw [xv 2 n 4 (by norm_num)]; exact p24
    · -- run 4n+2: buffer 3
      rw [show 4 * n + 1 + 1 + 1 = 4 * n + 2 + 1 by ring, sidx1_r n 2 (by omega),
        beven _ (by omega), bodd _ (by omega)]
      simp only [sidx1aux]
      refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, Or.inl ?_⟩⟩
      · have h2' := h2 (hR _)
        have hpos := e1_pos_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 2) (12 * n + 5) (12 * n + 7)
          (by
            intro j hj1 hj2
            obtain rfl : j = 12 * n + 6 := by omega
            rw [xv 2 n 6 (by norm_num)]; exact p26)
          (by
            intro j hj1 hj2
            left
            obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
            have hk' : 5 ≤ k' ∧ k' ≤ 6 := by omega
            rw [xv 2 n k' (by omega)]
            obtain ⟨hk1, hk2⟩ := hk'
            interval_cases k' <;> assumption) t (by simpa using h1) (by simpa using h2')
        rw [hc.1] at hpos; exact lt_irrefl _ hpos
      · rw [xv 2 n 7 (by norm_num), c7]
      · rw [xv 1 n 7 (by norm_num)]; exact p17
    · -- run 4n+3: buffer 2
      rw [show 4 * n + 2 + 1 + 1 = 4 * n + 3 + 1 by ring, sidx1_r n 3 (by omega),
        bodd _ (by omega), beven _ (by omega)]
      simp only [sidx1aux]
      refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, Or.inl ?_⟩⟩
      · have h2' := h2 (hR _)
        have hpos := e1_pos_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 1) (12 * n + 8) (12 * n + 9)
          (by intro j hj1 hj2; omega)
          (by
            intro j hj1 hj2
            left
            obtain rfl : j = 12 * n + 8 := by omega
            rw [xv 1 n 8 (by norm_num)]; exact p18) t (by simpa using h1) (by simpa using h2')
        rw [hc.1] at hpos; exact lt_irrefl _ hpos
      · rw [xv 1 n 9 (by norm_num), b9]
      · rw [xv 2 n 9 (by norm_num)]; exact p29
    · -- run 4n+4: buffer 3
      rw [show 4 * n + 3 + 1 + 1 = 4 * (n + 1) + 0 + 1 by ring, sidx1_r (n + 1) 0 (by omega),
        beven _ (by omega), bodd _ (by omega)]
      simp only [sidx1aux]
      have e13 : 12 * (n + 1) + 1 = 12 * n + 13 := by ring
      rw [e13]
      have x13 : ∀ i, (traj τ hτ δ hδ ξ).x (ex1Buf i) (bk τ δ ξ (12 * n + 13)) =
          Xv τ δ i 1 (xs τ δ ξ (n + 1)) := fun i => by rw [← e13]; exact xv i (n + 1) 1 (by norm_num)
      refine ⟨fun t h1 h2 hc => ?_, fun _ => ⟨?_, by simp, ?_⟩⟩
      · have h2' := h2 (hR _)
        rcases lt_or_ge t (bk τ δ ξ (12 * n + 11)) with h | h
        · have hpos := e1_pos_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 2) (12 * n + 10) (12 * n + 11)
            (by intro j hj1 hj2; omega)
            (by
              intro j hj1 hj2
              left
              obtain rfl : j = 12 * n + 10 := by omega
              rw [xv 2 n 10 (by norm_num)]; exact p210) t (by simpa using h1) h
          rw [hc.1] at hpos; exact lt_irrefl _ hpos
        · obtain ⟨b', hb'r, hb'ne, hb'd⟩ := hc.2
          rcases ex1_m1 hb'r with hb | hb
          swap
          · exact hb'ne hb
          rw [hb] at hb'd
          have hx1 := e1_zero_range hτ hδ h3 h4 h5 hξ hbig (ex1Buf 1) (12 * n + 11) (12 * n + 13)
            (by
              intro j hj1 hj2
              obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
              have hk' : 11 ≤ k' ∧ k' ≤ 13 := by omega
              obtain ⟨hk1, hk2⟩ := hk'
              interval_cases k'
              · rw [xv 1 n 11 (by norm_num), b11]
              · rw [xv 1 n 12 (by norm_num), b12]
              · rw [x13, b1']) t h h2'.le
          refine e1_notdem hτ hδ h3 h4 h5 hξ hbig (ex1Buf 1) 0 (e1_in1 hτ hδ h3 h4 h5 hξ hbig)
            (12 * n + 11) (12 * n + 13) ?_ h h2' hx1 hb'd
          intro j hj1 hj2
          obtain ⟨k', rfl⟩ : ∃ k', j = 12 * n + k' := ⟨j - 12 * n, by omega⟩
          have hk' : 11 ≤ k' ∧ k' ≤ 12 := by omega
          obtain ⟨hk1, hk2⟩ := hk'
          interval_cases k'
          · rw [show (12 * n + 11) % 12 = 11 by omega]; simp [osl]
          · rw [show (12 * n + 12) % 12 = 0 by omega]; simp [osl]
      · rw [x13, c1']
      · rw [← e13]
        apply e1_dem_inc hτ hδ h3 h4 h5 hξ hbig 0 (ex1Buf 1) (e1_in1 hτ hδ h3 h4 h5 hξ hbig)
        rw [show (12 * (n + 1) + 1) % 12 = 1 by omega]
        simp [osl]; exact t0

theorem e1_clearing : IsClearing (S1 τ hτ δ hδ) (traj τ hτ δ hδ ξ) := by
  refine ⟨e1_isTraj hτ hδ h3 h4 h5 hξ hbig, ?_⟩
  intro m k _
  fin_cases m
  · exact e1_cl0 hτ hδ h3 h4 h5 hξ hbig k
  · exact e1_cl1 hτ hδ h3 h4 h5 hξ hbig k

theorem e1_initial : Ex1Initial (traj τ hτ δ hδ ξ) ξ := by
  have z := fun i => e1_yf_zero hτ hδ h3 h4 h5 hξ hbig i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1_tx0, z]; ring
  · rw [e1_tx1, z, z]; ring
  · rw [e1_tx2, z, z]; ring
  · rw [e1_tx3, z, z]; ring
  · rw [e1_tβ]; simp [βf]
  · rw [e1_tβ]; simp [βf]

end C1Cl2
end KSR

open KumarSeidman.Reentrant in
theorem solution (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ξ₀ : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ₀ ≤ ξ →
      ∃ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
        IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T ∧ Ex1Initial T ξ :=
  ⟨KSR.xi0 τ δ, fun ξ hξ hbig => ⟨KSR.C1E.traj τ hτ δ hδ ξ,
    KSR.e1_clearing hτ hδ h3 h4 h5 hξ hbig, KSR.e1_initial hτ hδ h3 h4 h5 hξ hbig⟩⟩

