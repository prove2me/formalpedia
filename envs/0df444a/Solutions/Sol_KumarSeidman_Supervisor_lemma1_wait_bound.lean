-- Prove2me | solution 1 for KumarSeidman.Supervisor.lemma1_wait_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:55:45.081391+00:00
-- url     : https://prove2.me/submissions/98d18d83-72c4-4c7b-b199-2363f3a6954d

import Mathlib
import Definitions.Def_KumarSeidman_Supervisor_System
import Definitions.Def_KumarSeidman_Supervisor_Trajectory
import Definitions.Def_KumarSeidman_Supervisor_Mechanism



namespace KumarSeidman.Supervisor

open Trajectory

variable {P M : ℕ} {S : System P M}

lemma ks_runSetup_nonneg (β : ℕ → Buffer S) (k : ℕ) : 0 ≤ runSetup S β k := by
  cases k with
  | zero => simp [runSetup]
  | succ j => simp only [runSetup]; exact S.δ_nonneg _ _

lemma ks_all_lt (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) : ∀ k : ℕ, (k : ℕ∞) < T.N m := by
  intro k
  induction k with
  | zero => simpa using T.N_pos m
  | succ j ih => exact (hT.truncation m j ih).1

lemma ks_hasNext (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) (k : ℕ) : T.HasNext m k := ks_all_lt T hT m (k+1)

lemma ks_N_top (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) : T.N m = ⊤ := by
  by_contra h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
  have := ks_all_lt T hT m n
  rw [← hn] at this
  exact lt_irrefl _ this

lemma ks_s_succ (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) (k : ℕ) : T.s m k ≤ T.s m (k+1) := by
  have := T.setup_not_cut m k (ks_hasNext T hT m k)
  linarith [ks_runSetup_nonneg (T.β m) k]

lemma ks_s_mono (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) : Monotone (T.s m) :=
  monotone_nat_of_le_succ (ks_s_succ T hT m)

lemma ks_s_nonneg (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) (k : ℕ) : 0 ≤ T.s m k := by
  have := ks_s_mono T hT m (Nat.zero_le k)
  rwa [T.s_zero] at this

lemma ks_procStart_le (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) (k : ℕ) : T.s m k ≤ T.procStart m k ∧ T.procStart m k ≤ T.s m (k+1) := by
  unfold Trajectory.procStart
  exact ⟨by linarith [ks_runSetup_nonneg (T.β m) k], T.setup_not_cut m k (ks_hasNext T hT m k)⟩

lemma ks_exists_run (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) (σ : ℝ) (hσ : 0 ≤ σ) : ∃ j, T.s m j ≤ σ ∧ σ < T.s m (j+1) := by
  have ht := T.locally_finite m (ks_N_top T hT m)
  have hex : ∃ j, σ < T.s m j := by
    obtain ⟨j, hj⟩ := (Filter.tendsto_atTop_atTop.mp ht) (σ + 1)
    exact ⟨j, by linarith [hj j le_rfl]⟩
  classical
  let j := Nat.find hex
  have hj : σ < T.s m j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    have : σ < T.s m 0 := h0 ▸ hj
    rw [T.s_zero] at this; linarith
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨i, ?_, ?_⟩
  · have := Nat.find_min hex (show i < j by omega)
    exact not_lt.mp this
  · have e : i + 1 = j := hi.symm
    rw [e]; exact hj

lemma ks_onRun_unique (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (b : Buffer S) (σ : ℝ) (j : ℕ) (h1 : T.s (S.mach b) j ≤ σ) (h2 : σ < T.s (S.mach b) (j+1))
    (hon : T.OnRun b σ) : T.β (S.mach b) j = b := by
  obtain ⟨l, -, hlb, hl1, hl2⟩ := hon
  have hl2 := hl2 (ks_hasNext T hT _ l)
  have hmono := ks_s_mono T hT (S.mach b)
  rcases lt_trichotomy l j with h | h | h
  · have := hmono (show l + 1 ≤ j by omega); linarith
  · subst h; exact hlb
  · have := hmono (show j + 1 ≤ l by omega); linarith

lemma ks_proc_onRun (T : Trajectory S) (b : Buffer S) (σ : ℝ)
    (h : ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ) : T.OnRun b σ := by
  obtain ⟨k, hk, hN, h1, h2⟩ := h
  exact ⟨k, hN, hk, by linarith [ks_runSetup_nonneg (T.β (S.mach b)) k], h2⟩

/-- y does not increase when not processed. -/
lemma ks_y_const (T : Trajectory S) (b : Buffer S) (t₁ t₂ : ℝ) (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hnp : ∀ σ ∈ Set.Ico t₁ t₂,
      ¬ ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ) :
    T.y b t₂ ≤ T.y b t₁ := by
  have hc := T.rate_cap b t₁ t₂ h0 h12
  have hsub : Set.Icc t₁ t₂ ∩
      {σ | ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ} ⊆ {t₂} := by
    intro σ ⟨hσ, hp⟩
    by_contra hne
    exact hnp σ ⟨hσ.1, lt_of_le_of_ne hσ.2 hne⟩ hp
  have h0' : MeasureTheory.volume (Set.Icc t₁ t₂ ∩
      {σ | ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ}) = 0 :=
    MeasureTheory.measure_mono_null hsub (MeasureTheory.measure_singleton _)
  rw [h0'] at hc
  simp at hc
  linarith

lemma ks_y_lip (T : Trajectory S) (b : Buffer S) (t₁ t₂ : ℝ) (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    T.y b t₂ - T.y b t₁ ≤ (t₂ - t₁) / S.tau b := by
  have hc := T.rate_cap b t₁ t₂ h0 h12
  have hτ : 0 < S.tau b := S.τ_pos _ _
  refine hc.trans ?_
  apply div_le_div_of_nonneg_right _ hτ.le
  have : (MeasureTheory.volume (Set.Icc t₁ t₂ ∩
      {σ | ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ})) ≤
      MeasureTheory.volume (Set.Icc t₁ t₂) := MeasureTheory.measure_mono Set.inter_subset_left
  have h2 := ENNReal.toReal_mono (by simp) this
  simpa [Real.volume_Icc, h12] using h2

lemma ks_y_mono (T : Trajectory S) (b : Buffer S) (t₁ t₂ : ℝ) (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    T.y b t₁ ≤ T.y b t₂ :=
  T.y_mono b (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr (h0.trans h12)) h12

lemma ks_inflow_mono (T : Trajectory S) (b : Buffer S) (t₁ t₂ : ℝ) (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    inflow S T.y b t₁ ≤ inflow S T.y b t₂ := by
  unfold inflow
  cases S.prev b with
  | none => exact mul_le_mul_of_nonneg_left h12 (S.d_pos _).le
  | some b' => exact ks_y_mono T b' t₁ t₂ h0 h12

lemma ks_x_up (T : Trajectory S) (b : Buffer S) (t₁ t₂ : ℝ) (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (hnp : ∀ σ ∈ Set.Ico t₁ t₂,
      ¬ ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ) :
    T.x b t₁ ≤ T.x b t₂ := by
  rw [T.balance b t₁ h0, T.balance b t₂ (h0.trans h12)]
  linarith [ks_y_const T b t₁ t₂ h0 h12 hnp, ks_inflow_mono T b t₁ t₂ h0 h12]

lemma ks_x_growth (T : Trajectory S) (b : Buffer S) :
    ∃ R, 0 ≤ R ∧ ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → T.x b t₂ - T.x b t₁ ≤ R * (t₂ - t₁) := by
  have key : ∃ R, 0 ≤ R ∧ ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ →
      inflow S T.y b t₂ - inflow S T.y b t₁ ≤ R * (t₂ - t₁) := by
    unfold inflow
    cases S.prev b with
    | none => exact ⟨S.d b.1, (S.d_pos _).le, fun t₁ t₂ _ _ => by ring_nf; rfl⟩
    | some b' =>
      refine ⟨1 / S.tau b', (one_div_pos.mpr (S.τ_pos _ _)).le, fun t₁ t₂ h0 h12 => ?_⟩
      have := ks_y_lip T b' t₁ t₂ h0 h12
      simpa [div_eq_inv_mul] using this
  obtain ⟨R, hR, hk⟩ := key
  refine ⟨R, hR, fun t₁ t₂ h0 h12 => ?_⟩
  rw [T.balance b t₁ h0, T.balance b t₂ (h0.trans h12)]
  linarith [hk t₁ t₂ h0 h12, ks_y_mono T b t₁ t₂ h0 h12]


lemma ks_entry_le (T : Trajectory S) (z : Buffer S → ℝ) (b : Buffer S) (tIn t : ℝ)
    (h0 : 0 ≤ tIn) (h1 : tIn ≤ t)
    (h : ∀ σ ∈ Set.Ioo tIn t, ¬ T.OnRun b σ ∧ z b < T.x b σ) :
    T.entryTime z b t ≤ tIn := by
  unfold Trajectory.entryTime
  apply csInf_le ⟨0, fun e he => he.1.1⟩
  exact ⟨⟨h0, h1⟩, h⟩

lemma ks_entry_ge (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) (c : Buffer S) (hmc : S.mach c = m) (i : ℕ) (t : ℝ)
    (hc : T.β m i = c) (hlt : T.s m i < T.s m (i+1)) (hle : T.s m (i+1) ≤ t) :
    T.s m (i+1) ≤ T.entryTime z c t := by
  subst hmc
  unfold Trajectory.entryTime
  have h0 : 0 ≤ t := (ks_s_nonneg T hT _ _).trans hle
  refine le_csInf ⟨t, ⟨⟨h0, le_rfl⟩, fun σ hσ => absurd hσ.2 (not_lt.mpr hσ.1.le)⟩⟩ ?_
  rintro e ⟨_, he2⟩
  by_contra hne
  have hne' : e < T.s (S.mach c) (i+1) := lt_of_not_ge hne
  have ha : max e (T.s (S.mach c) i) < T.s (S.mach c) (i+1) := max_lt hne' hlt
  have hσ := he2 ((max e (T.s (S.mach c) i) + T.s (S.mach c) (i+1))/2)
    ⟨by linarith [le_max_left e (T.s (S.mach c) i)], by linarith⟩
  apply hσ.1
  exact ⟨i, ks_all_lt T hT _ i, hc, by linarith [le_max_right e (T.s (S.mach c) i)],
    fun _ => by linarith⟩

lemma ks_setupSum_nonneg (S : System P M) (m : Fin M) : 0 ≤ S.setupSum m := by
  unfold System.setupSum
  apply Finset.sum_nonneg
  intro x _
  have := Finset.le_sup' (fun b' => S.δ b' x.1) x.2
  simp only [S.δ_self] at this
  exact this

lemma ks_gamma_pos (S : System P M) (hcap : S.CapacityCondition) (γ : Fin M → ℝ)
    (hγ : GammaCondition S γ) (m : Fin M) : 0 < γ m := by
  have h1 := hcap m
  have h2 := hγ m
  have h3 := ks_setupSum_nonneg S m
  by_contra h
  push_neg at h
  nlinarith

lemma ks_zeta_pos (S : System P M) (γ : Fin M → ℝ)
    (hγ : GammaCondition S γ) (m : Fin M) : 0 < zeta S γ m := by
  have := hγ m
  unfold zeta; linarith

lemma ks_runCap_pos (S : System P M) (hcap : S.CapacityCondition) (γ : Fin M → ℝ)
    (hγ : GammaCondition S γ) (c : Buffer S) : 0 < runCap S γ c := by
  unfold runCap
  have := ks_gamma_pos S hcap γ hγ (S.mach c)
  have := S.d_pos c.1
  have : 0 < S.tau c := S.τ_pos _ _
  positivity

lemma ks_queue_pos (T : Trajectory S) (hcap : S.CapacityCondition) {γ : Fin M → ℝ}
    (hγ : GammaCondition S γ) {z : Buffer S → ℝ} (hz : ∀ b, 0 ≤ z b) (hT : T.Supervised γ z)
    (m : Fin M) (k : ℕ) (hne : (T.queueAtSwitch z m k).Nonempty) :
    T.s m (k+1) < T.s m (k+2) := by
  obtain ⟨hsel, -⟩ := hT.selection m k (ks_hasNext T hT m k) hne
  obtain ⟨-, hor⟩ := hT.queue_time m k (ks_hasNext T hT m (k+1)) hne
  have hp := ks_procStart_le T hT m (k+1)
  by_contra h
  push_neg at h
  have e1 : T.procStart m (k+1) = T.s m (k+1) := by linarith [hp.1, hp.2]
  rcases hor with h1 | h1
  · have := ks_runCap_pos S hcap γ hγ (T.β m (k+1))
    linarith
  · have hx := hsel.2
    have e2 : T.s m (k+2) = T.s m (k+1) := by linarith [hp.1, hp.2]
    rw [e2] at h1
    have := hz (T.β m (k+1))
    linarith

lemma ks_noproc_setup (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ}
    (hT : T.Supervised γ z) (b : Buffer S) (K : ℕ) :
    ∀ σ ∈ Set.Ico (T.s (S.mach b) K) (T.procStart (S.mach b) K),
      ¬ ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ := by
  intro σ hσ ⟨l, _, _, h1, h2⟩
  have h2 := h2 (ks_hasNext T hT _ l)
  have hmono := ks_s_mono T hT (S.mach b)
  have hp := ks_procStart_le T hT (S.mach b) K
  have hl0 := ks_runSetup_nonneg (T.β (S.mach b)) l
  unfold Trajectory.procStart at hσ hp
  rcases lt_trichotomy l K with h | h | h
  · have := hmono (show l + 1 ≤ K by omega); linarith [hσ.1]
  · subst h; linarith [hσ.2]
  · have := hmono (show K + 1 ≤ l by omega); linarith [hσ.2]

lemma ks_queued_switch (T : Trajectory S) (hcap : S.CapacityCondition) {γ : Fin M → ℝ}
    (hγ : GammaCondition S γ) {z : Buffer S → ℝ} (hz : ∀ b, 0 ≤ z b) (hT : T.Supervised γ z)
    (b : Buffer S) (K : ℕ) (hx : z b < T.x b (T.s (S.mach b) (K+1))) :
    T.QueuedAt z b (T.s (S.mach b) (K+1)) := by
  have hq : b ∈ T.queueAtSwitch z (S.mach b) K := ⟨rfl, hx⟩
  refine ⟨ks_s_nonneg T hT _ _, ?_⟩
  by_cases hβ : T.β (S.mach b) (K+1) = b
  · exact Or.inr ⟨K, ks_hasNext T hT _ K, rfl, hβ, hx⟩
  · left
    refine ⟨T.s (S.mach b) (K+2), ks_queue_pos T hcap hγ hz hT _ K ⟨b, hq⟩, fun σ hσ => ⟨?_, ?_⟩⟩
    · intro hon
      exact hβ (ks_onRun_unique T hT b σ (K+1) hσ.1.le hσ.2 hon)
    · refine lt_of_lt_of_le hx (ks_x_up T b _ σ (ks_s_nonneg T hT _ _) hσ.1.le ?_)
      intro σ' hσ' hp
      exact hβ (ks_onRun_unique T hT b σ' (K+1) hσ'.1 (by linarith [hσ'.2, hσ.2])
        (ks_proc_onRun T b σ' hp))

noncomputable def ksF (S : System P M) (γ : Fin M → ℝ) (m : Fin M) (c : Buffer S) : ℝ :=
  (if h : c ∈ S.B m then (S.B m).sup' ⟨c, h⟩ (fun b' => S.δ b' c) else 0) + runCap S γ c

lemma ks_sumF (S : System P M) (γ : Fin M → ℝ) (m : Fin M) :
    ∑ c ∈ S.B m, ksF S γ m c = γ m - zeta S γ m := by
  have e : γ m - zeta S γ m = S.setupSum m + γ m * S.rho m := by unfold zeta; ring
  rw [e]
  unfold ksF
  rw [Finset.sum_add_distrib]
  congr 1
  · unfold System.setupSum
    rw [← Finset.sum_attach (S.B m)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [dif_pos x.2]
  · unfold System.rho runCap
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have : S.mach c = m := (Finset.mem_filter.mp hc).2
    rw [this]; ring

lemma ks_F_nonneg (S : System P M) (hcap : S.CapacityCondition) (γ : Fin M → ℝ)
    (hγ : GammaCondition S γ) (m : Fin M) (c : Buffer S) (hc : c ∈ S.B m) :
    0 ≤ ksF S γ m c := by
  unfold ksF
  rw [dif_pos hc]
  have := Finset.le_sup' (fun b' => S.δ b' c) hc
  simp only [S.δ_self] at this
  linarith [ks_runCap_pos S hcap γ hγ c]

lemma ks_W_nonneg (S : System P M) (hcap : S.CapacityCondition) (γ : Fin M → ℝ)
    (hγ : GammaCondition S γ) (m : Fin M) : 0 ≤ γ m - zeta S γ m := by
  rw [← ks_sumF]
  exact Finset.sum_nonneg (fun c hc => ks_F_nonneg S hcap γ hγ m c hc)

lemma ks_mem_B (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) (l : ℕ) : T.β m l ∈ S.B m :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.β_mem m l (ks_all_lt T hT m l)⟩

lemma ks_run_len (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (m : Fin M) (l : ℕ) : T.s m (l+1) - T.s m l ≤ ksF S γ m (T.β m l) := by
  have hmem := ks_mem_B T hT m l
  have htr := (hT.truncation m l (ks_all_lt T hT m l)).2
  unfold Trajectory.procStart at htr
  unfold ksF
  rw [dif_pos hmem]
  have : runSetup S (T.β m) l ≤ (S.B m).sup' ⟨T.β m l, hmem⟩ (fun b' => S.δ b' (T.β m l)) := by
    cases l with
    | zero =>
      have := Finset.le_sup' (fun b' => S.δ b' (T.β m 0)) hmem
      simp only [S.δ_self] at this
      simpa [runSetup] using this
    | succ j =>
      simp only [runSetup]
      exact Finset.le_sup' (fun b' => S.δ b' (T.β m (j+1))) (ks_mem_B T hT m j)
  linarith


lemma ks_core (T : Trajectory S) (hcap : S.CapacityCondition) {γ : Fin M → ℝ}
    (hγ : GammaCondition S γ) {z : Buffer S → ℝ} (hz : ∀ b, 0 ≤ z b) (hT : T.Supervised γ z)
    (b : Buffer S) (tIn : ℝ) (hq : T.QueuedAt z b tIn) :
    ∃ K : ℕ, T.IsNextRun b tIn (K+1) ∧ b ∈ T.queueAtSwitch z (S.mach b) K ∧
      T.s (S.mach b) (K+2) - tIn ≤ γ (S.mach b) - zeta S γ (S.mach b) ∧
      (∀ σ ∈ Set.Ico tIn (T.procStart (S.mach b) (K+1)),
        ¬ ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ) := by
  have hmono := ks_s_mono T hT (S.mach b)
  have hbB : b ∈ S.B (S.mach b) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  rcases hq with ⟨h0, ⟨t1, ht1, hw⟩ | ⟨k', _, hs, hβ, hx⟩⟩
  swap
  · -- case B
    have hqk : b ∈ T.queueAtSwitch z (S.mach b) k' := ⟨rfl, by rw [hs]; exact hx⟩
    have hpos := ks_queue_pos T hcap hγ hz hT _ k' ⟨b, hqk⟩
    refine ⟨k', ⟨ks_all_lt T hT _ _, hβ, hs.ge, fun _ => by rw [← hs]; exact hpos, ?_⟩,
      hqk, ?_, ?_⟩
    · rintro j hj _ ⟨_, h2⟩
      have := hmono (show j + 1 ≤ k' + 1 by omega)
      have h2 := h2 (ks_hasNext T hT _ j)
      linarith
    · have h1 := ks_run_len T hT (S.mach b) (k'+1)
      rw [hβ] at h1
      have h2 := Finset.single_le_sum (f := ksF S γ (S.mach b))
        (fun c hc => ks_F_nonneg S hcap γ hγ _ c hc) hbB
      rw [ks_sumF] at h2
      rw [← hs]; linarith
    · rw [← hs]; exact ks_noproc_setup T hT b (k'+1)
  · -- case A
    obtain ⟨k0, hk0a, hk0b⟩ := ks_exists_run T hT (S.mach b) tIn h0
    have hβk0 : T.β (S.mach b) k0 ≠ b := by
      intro h
      have hm : tIn < min t1 (T.s (S.mach b) (k0+1)) := lt_min ht1 hk0b
      have hσ := hw ((tIn + min t1 (T.s (S.mach b) (k0+1)))/2)
        ⟨by linarith, by linarith [min_le_left t1 (T.s (S.mach b) (k0+1))]⟩
      exact hσ.1 ⟨k0, ks_all_lt T hT _ _, h, by linarith,
        fun _ => by linarith [min_le_right t1 (T.s (S.mach b) (k0+1))]⟩
    have F1 : ∀ j, (∀ l, k0 ≤ l → l < j → T.β (S.mach b) l ≠ b) →
        ∀ σ ∈ Set.Ico tIn (T.s (S.mach b) j), ¬ T.OnRun b σ := by
      intro j hc σ hσ hon
      obtain ⟨l, hl1, hl2⟩ := ks_exists_run T hT (S.mach b) σ (h0.trans hσ.1)
      have hl := ks_onRun_unique T hT b σ l hl1 hl2 hon
      have hkl : k0 ≤ l := by
        by_contra hh
        have := hmono (show l + 1 ≤ k0 by omega)
        linarith [hσ.1]
      have hlj : l < j := by
        by_contra hh
        have := hmono (show j ≤ l by omega)
        linarith [hσ.2]
      exact hc l hkl hlj hl
    have F1p : ∀ j, (∀ l, k0 ≤ l → l < j → T.β (S.mach b) l ≠ b) →
        ∀ σ ∈ Set.Ico tIn (T.s (S.mach b) j),
        ¬ ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ :=
      fun j hc σ hσ hp => F1 j hc σ hσ (ks_proc_onRun T b σ hp)
    have F2 : ∀ j, (∀ l, k0 ≤ l → l < j → T.β (S.mach b) l ≠ b) →
        ∀ σ, tIn < σ → σ ≤ T.s (S.mach b) j → z b < T.x b σ := by
      intro j hc σ h1 h2
      have hm : tIn < min σ t1 := lt_min h1 ht1
      have hσ' := hw ((tIn + min σ t1)/2) ⟨by linarith, by linarith [min_le_right σ t1]⟩
      refine lt_of_lt_of_le hσ'.2
        (ks_x_up T b _ σ (by linarith) (by linarith [min_le_left σ t1]) ?_)
      intro σ'' hσ''
      exact F1p j hc σ'' ⟨by linarith [hσ''.1], lt_of_lt_of_le hσ''.2 h2⟩
    have hkey : ∀ j, k0 ≤ j → tIn < T.s (S.mach b) (j+1) := fun j hj =>
      lt_of_lt_of_le hk0b (hmono (by omega))
    have F3 : ∀ j, (∀ l, k0 ≤ l → l < j+1 → T.β (S.mach b) l ≠ b) → k0 ≤ j →
        b ∈ T.queueAtSwitch z (S.mach b) j :=
      fun j hc hj => ⟨rfl, F2 (j+1) hc _ (hkey j hj) le_rfl⟩
    have F4 : ∀ j, (∀ l, k0 ≤ l → l < j+1 → T.β (S.mach b) l ≠ b) → k0 ≤ j →
        T.entryTime z b (T.s (S.mach b) (j+1)) ≤ tIn := by
      intro j hc hj
      apply ks_entry_le T z b tIn _ h0 (hkey j hj).le
      intro σ hσ
      exact ⟨F1 (j+1) hc σ ⟨hσ.1.le, hσ.2⟩, F2 (j+1) hc σ hσ.1 hσ.2.le⟩
    have F6 : ∀ i j, k0 ≤ i → i < j → (∀ l, k0 ≤ l → l < j → T.β (S.mach b) l ≠ b) →
        T.β (S.mach b) i ≠ T.β (S.mach b) j := by
      intro i j hi hij hc heq
      obtain ⟨j', rfl⟩ : ∃ j', j = j'+1 := ⟨j-1, by omega⟩
      have hq' := F3 j' hc (by omega)
      have hsel := hT.selection (S.mach b) j' (ks_hasNext T hT _ j') ⟨b, hq'⟩
      have h1 := hsel.2 b hq'
      have h2 := F4 j' hc (by omega)
      have hlt : T.s (S.mach b) i < T.s (S.mach b) (i+1) := by
        rcases Nat.eq_or_lt_of_le hi with h | h
        · subst h; linarith
        · obtain ⟨i', rfl⟩ : ∃ i', i = i'+1 := ⟨i-1, by omega⟩
          exact ks_queue_pos T hcap hγ hz hT _ i'
            ⟨b, F3 i' (fun l hl1 hl2 => hc l hl1 (by omega)) (by omega)⟩
      have h3 := ks_entry_ge (z := z) T hT (S.mach b) (T.β (S.mach b) (j'+1))
        (T.β_mem _ _ (ks_all_lt T hT _ _)) i _ heq hlt (hmono (show i+1 ≤ j'+1 by omega))
      have h4 := hkey i hi
      linarith
    have hex : ∃ j, k0 + 1 ≤ j ∧ T.β (S.mach b) j = b := by
      by_contra hne
      push_neg at hne
      have hcl : ∀ j, ∀ l, k0 ≤ l → l < j → T.β (S.mach b) l ≠ b := by
        intro j l hl _
        rcases Nat.eq_or_lt_of_le hl with h | h
        · subst h; exact hβk0
        · exact hne l h
      have hcard := Finset.card_le_card_of_injOn (fun i => T.β (S.mach b) (k0 + i))
        (s := Finset.range ((S.B (S.mach b)).card + 1)) (t := S.B (S.mach b))
        (fun i _ => ks_mem_B T hT _ _) (by
          intro i1 _ i2 _ heq
          by_contra hne'
          rcases lt_or_gt_of_ne hne' with h | h
          · exact F6 (k0+i1) (k0+i2) (by omega) (by omega) (hcl _) heq
          · exact F6 (k0+i2) (k0+i1) (by omega) (by omega) (hcl _) heq.symm)
      simp at hcard
    classical
    obtain ⟨K, hK, hKmin⟩ : ∃ K, (k0 + 1 ≤ K ∧ T.β (S.mach b) K = b) ∧
        ∀ l < K, ¬ (k0 + 1 ≤ l ∧ T.β (S.mach b) l = b) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun l hl => Nat.find_min hex hl⟩
    have hclK : ∀ l, k0 ≤ l → l < K → T.β (S.mach b) l ≠ b := by
      intro l hl hlK hβl
      rcases Nat.eq_or_lt_of_le hl with h | h
      · subst h; exact hβk0 hβl
      · exact hKmin l hlK ⟨h, hβl⟩
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hclK' : ∀ j ≤ K'+1, ∀ l, k0 ≤ l → l < j → T.β (S.mach b) l ≠ b :=
      fun j hj l h1 h2 => hclK l h1 (by omega)
    refine ⟨K', ⟨ks_all_lt T hT _ _, hK.2, (hkey K' (by omega)).le,
      fun _ => lt_of_lt_of_le (hkey K' (by omega)) (hmono (by omega)), ?_⟩,
      F3 K' hclK (by omega), ?_, ?_⟩
    · rintro j hj hβj ⟨h1, h2⟩
      by_cases hjk : j < k0
      · have := hmono (show j + 1 ≤ k0 by omega)
        have h2 := h2 (ks_hasNext T hT _ j)
        linarith
      · exact hclK j (by omega) hj hβj
    · obtain ⟨n, hn⟩ : ∃ n, K' + 2 = k0 + n := ⟨K' + 2 - k0, by omega⟩
      have htel : ∑ i ∈ Finset.range n,
          (T.s (S.mach b) (k0 + i + 1) - T.s (S.mach b) (k0 + i)) =
          T.s (S.mach b) (k0 + n) - T.s (S.mach b) k0 := by
        have := Finset.sum_range_sub (fun i => T.s (S.mach b) (k0 + i)) n
        simpa [add_assoc] using this
      have hle1 : ∑ i ∈ Finset.range n,
          (T.s (S.mach b) (k0 + i + 1) - T.s (S.mach b) (k0 + i)) ≤
          ∑ i ∈ Finset.range n, ksF S γ (S.mach b) (T.β (S.mach b) (k0 + i)) :=
        Finset.sum_le_sum (fun i _ => ks_run_len T hT _ _)
      have hinj : Set.InjOn (fun i => T.β (S.mach b) (k0 + i)) (Finset.range n) := by
        intro i1 hi1 i2 hi2 heq
        simp only [Finset.coe_range, Set.mem_Iio] at hi1 hi2
        by_contra hne'
        rcases lt_or_gt_of_ne hne' with h | h
        · exact F6 (k0+i1) (k0+i2) (by omega) (by omega) (hclK' _ (by omega)) heq
        · exact F6 (k0+i2) (k0+i1) (by omega) (by omega) (hclK' _ (by omega)) heq.symm
      have hle2 : ∑ i ∈ Finset.range n, ksF S γ (S.mach b) (T.β (S.mach b) (k0 + i)) ≤
          ∑ c ∈ S.B (S.mach b), ksF S γ (S.mach b) c := by
        rw [← Finset.sum_image hinj]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
          exact ks_mem_B T hT _ _
        · intro c hc _
          exact ks_F_nonneg S hcap γ hγ _ c hc
      rw [ks_sumF] at hle2
      rw [hn]
      linarith
    · intro σ hσ hp
      by_cases hσK : σ < T.s (S.mach b) (K'+1)
      · exact F1p (K'+1) hclK σ ⟨hσ.1, hσK⟩ hp
      · exact ks_noproc_setup T hT b (K'+1) σ ⟨le_of_not_gt hσK, hσ.2⟩ hp


lemma ks_nextRun_unique (T : Trajectory S) (b : Buffer S) (t : ℝ) (k k' : ℕ)
    (h : T.IsNextRun b t k) (h' : T.IsNextRun b t k') : k = k' := by
  rcases lt_trichotomy k k' with hl | hl | hl
  · exact absurd ⟨h.2.2.1, h.2.2.2.1⟩ (h'.2.2.2.2 k hl h.2.1)
  · exact hl
  · exact absurd ⟨h'.2.2.1, h'.2.2.2.1⟩ (h.2.2.2.2 k' hl h'.2.1)

theorem wait_bound_core {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn : ℝ)
    (hin : T.EntersQ z b tIn) :
    ∃ k : ℕ, T.IsNextRun b tIn k ∧ T.HasNext (S.mach b) k ∧
      T.s (S.mach b) (k + 1) - tIn ≤ γ (S.mach b) - zeta S γ (S.mach b) := by
  obtain ⟨K, h1, _, h3, _⟩ := ks_core T hcap hγ hz hT b tIn hin.1
  exact ⟨K+1, h1, ks_hasNext T hT _ _, h3⟩

end KumarSeidman.Supervisor

open KumarSeidman.Supervisor


theorem solution {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn : ℝ)
    (hin : T.EntersQ z b tIn) :
    ∃ k : ℕ, T.IsNextRun b tIn k ∧ T.HasNext (S.mach b) k ∧
      T.s (S.mach b) (k + 1) - tIn ≤ γ (S.mach b) - zeta S γ (S.mach b) := by
  exact wait_bound_core S hcap γ hγ z hz T hT b tIn hin
