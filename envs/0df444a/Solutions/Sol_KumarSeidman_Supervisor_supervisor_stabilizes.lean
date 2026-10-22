-- Prove2me | solution 1 for KumarSeidman.Supervisor.supervisor_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:02:25.836037+00:00
-- url     : https://prove2.me/submissions/88af103c-1210-4f20-90fe-a0d86ecf2d58

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


lemma ks_Iic_succ (n : ℕ) (i : ℕ) (hi : i + 1 < n) :
    (Finset.Iic (⟨i+1, hi⟩ : Fin n)) = insert ⟨i+1, hi⟩ (Finset.Iic ⟨i, by omega⟩) := by
  ext j; simp [Fin.le_def, Fin.ext_iff]; omega

lemma ks_Iic_zero (n : ℕ) (hi : 0 < n) : (Finset.Iic (⟨0, hi⟩ : Fin n)) = {⟨0, hi⟩} := by
  ext j; simp [Fin.le_def, Fin.ext_iff]

lemma ks_tele (T : Trajectory S) (p : Fin P) (t : ℝ) :
    ∀ (i : ℕ) (hi : i < S.n p), ∑ j ∈ Finset.Iic (⟨i, hi⟩ : Fin (S.n p)),
      (inflow S T.y ⟨p, j⟩ t - T.y ⟨p, j⟩ t) = S.d p * t - T.y ⟨p, ⟨i, hi⟩⟩ t := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [ks_Iic_zero _ hi, Finset.sum_singleton]
    simp [inflow, System.prev]
  | succ i ih =>
    intro hi
    rw [ks_Iic_succ _ i hi, Finset.sum_insert (by simp [Fin.le_def]), ih (by omega)]
    simp [inflow, System.prev]

lemma ks_backlog_eq (T : Trajectory S) (b : Buffer S) (t : ℝ) (ht : 0 ≤ t) :
    backlog T b t =
      S.tau b * (∑ j ∈ Finset.Iic b.2, T.x ⟨b.1, j⟩ 0 + (S.d b.1 * t - T.y b t)) := by
  obtain ⟨p, i⟩ := b
  unfold backlog
  rw [← Finset.mul_sum]
  congr 1
  have h1 : ∑ j ∈ Finset.Iic i, T.x ⟨p, j⟩ t = ∑ j ∈ Finset.Iic i,
      (T.x ⟨p, j⟩ 0 + (inflow S T.y ⟨p, j⟩ t - T.y ⟨p, j⟩ t)) :=
    Finset.sum_congr rfl (fun j _ => by rw [T.balance _ t ht]; ring)
  rw [h1, Finset.sum_add_distrib]
  have h2 := ks_tele T p t i.val i.isLt
  simp only [Fin.eta] at h2
  rw [h2]

lemma ks_backlog_diff (T : Trajectory S) (b : Buffer S) (t₁ t₂ : ℝ) (h1 : 0 ≤ t₁) (h2 : 0 ≤ t₂) :
    backlog T b t₂ - backlog T b t₁ =
      S.tau b * (S.d b.1 * (t₂ - t₁) - (T.y b t₂ - T.y b t₁)) := by
  rw [ks_backlog_eq T b t₁ h1, ks_backlog_eq T b t₂ h2]; ring

lemma ks_backlog_nonneg (T : Trajectory S) (b : Buffer S) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ backlog T b t := by
  unfold backlog
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (S.τ_pos _ _).le (T.x_nonneg _ t ht))

lemma ks_backlog_growth (T : Trajectory S) (b : Buffer S) (t₁ t₂ : ℝ) (h1 : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) :
    backlog T b t₂ ≤ backlog T b t₁ + S.tau b * S.d b.1 * (t₂ - t₁) := by
  have e := ks_backlog_diff T b t₁ t₂ h1 (h1.trans h12)
  have hy := ks_y_mono T b t₁ t₂ h1 h12
  have hτ : 0 < S.tau b := S.τ_pos _ _
  have : S.tau b * (S.d b.1 * (t₂ - t₁) - (T.y b t₂ - T.y b t₁)) ≤
      S.tau b * (S.d b.1 * (t₂ - t₁)) := mul_le_mul_of_nonneg_left (by linarith) hτ.le
  have e2 : S.tau b * (S.d b.1 * (t₂ - t₁)) = S.tau b * S.d b.1 * (t₂ - t₁) := by ring
  linarith

lemma ks_full_rate (T : Trajectory S) {γ : Fin M → ℝ} {z : Buffer S → ℝ} (hT : T.Supervised γ z)
    (b : Buffer S) (k : ℕ) (hβ : T.β (S.mach b) k = b)
    (hpos : ∀ σ ∈ Set.Ico (T.procStart (S.mach b) k) (T.s (S.mach b) (k+1)), 0 < T.x b σ) :
    (T.s (S.mach b) (k+1) - T.procStart (S.mach b) k) / S.tau b ≤
      T.y b (T.s (S.mach b) (k+1)) - T.y b (T.procStart (S.mach b) k) := by
  have hp := ks_procStart_le T hT (S.mach b) k
  have h0 : 0 ≤ T.procStart (S.mach b) k := (ks_s_nonneg T hT _ _).trans hp.1
  have hτ : 0 < S.tau b := S.τ_pos _ _
  have hfr : ∀ t₂, T.procStart (S.mach b) k ≤ t₂ → t₂ < T.s (S.mach b) (k+1) →
      T.y b t₂ - T.y b (T.procStart (S.mach b) k) = (t₂ - T.procStart (S.mach b) k) / S.tau b := by
    intro t₂ h1 h2
    apply T.full_rate b _ t₂ h0 h1
    · intro σ hσ
      exact ⟨k, hβ, ks_all_lt T hT _ _, hσ.1, fun _ => lt_of_le_of_lt hσ.2 h2⟩
    · intro σ hσ
      exact hpos σ ⟨hσ.1, lt_trans hσ.2 h2⟩
  have hY0 := ks_y_mono T b _ _ h0 hp.2
  by_contra hlt
  push_neg at hlt
  have hYτ : (T.y b (T.s (S.mach b) (k+1)) - T.y b (T.procStart (S.mach b) k)) * S.tau b <
      T.s (S.mach b) (k+1) - T.procStart (S.mach b) k := (lt_div_iff₀ hτ).mp hlt
  have hYτ0 : 0 ≤ (T.y b (T.s (S.mach b) (k+1)) - T.y b (T.procStart (S.mach b) k)) * S.tau b :=
    mul_nonneg (by linarith) hτ.le
  set Y := T.y b (T.s (S.mach b) (k+1)) - T.y b (T.procStart (S.mach b) k) with hY
  set t₂ := T.procStart (S.mach b) k + (Y * S.tau b + (T.s (S.mach b) (k+1) - T.procStart (S.mach b) k)) / 2
  have h1 : T.procStart (S.mach b) k ≤ t₂ := by simp only [t₂]; linarith
  have h2 : t₂ < T.s (S.mach b) (k+1) := by simp only [t₂]; linarith
  have h3 := hfr t₂ h1 h2
  have h4 := ks_y_mono T b t₂ (T.s (S.mach b) (k+1)) (h0.trans h1) h2.le
  have h5 : (t₂ - T.procStart (S.mach b) k) / S.tau b ≤ Y := by rw [hY]; linarith
  rw [div_le_iff₀ hτ] at h5
  simp only [t₂] at h5
  linarith

lemma ks_lemma2 (T : Trajectory S) (hcap : S.CapacityCondition) {γ : Fin M → ℝ}
    (hγ : GammaCondition S γ) {z : Buffer S → ℝ} (hz : ∀ b, 0 ≤ z b) (hT : T.Supervised γ z)
    (b : Buffer S) (tIn : ℝ) (hq : T.QueuedAt z b tIn)
    (hlevel : γ (S.mach b) * S.d b.1 ≤ T.x b tIn) :
    ∃ K : ℕ, T.IsNextRun b tIn (K+1) ∧ tIn < T.s (S.mach b) (K+2) ∧
      T.s (S.mach b) (K+2) - tIn ≤ γ (S.mach b) - zeta S γ (S.mach b) ∧
      backlog T b (T.s (S.mach b) (K+2)) ≤
        backlog T b tIn - zeta S γ (S.mach b) * S.d b.1 * S.tau b := by
  obtain ⟨K, hnr, hqK, hbd, hnp⟩ := ks_core T hcap hγ hz hT b tIn hq
  have h0 : 0 ≤ tIn := hq.1
  have hβ : T.β (S.mach b) (K+1) = b := hnr.2.1
  have hps := ks_procStart_le T hT (S.mach b) (K+1)
  have htK : tIn ≤ T.s (S.mach b) (K+1) := hnr.2.2.1
  have hpos := ks_queue_pos T hcap hγ hz hT _ K ⟨b, hqK⟩
  obtain ⟨hxpos, hor⟩ := hT.queue_time (S.mach b) K (ks_hasNext T hT _ (K+1)) ⟨b, hqK⟩
  rw [hβ] at hxpos hor
  have hxps : T.x b tIn ≤ T.x b (T.procStart (S.mach b) (K+1)) :=
    ks_x_up T b _ _ h0 (by linarith [hps.1]) hnp
  have hτ : 0 < S.tau b := S.τ_pos _ _
  have hd := S.d_pos b.1
  have hps0 : 0 ≤ T.procStart (S.mach b) (K+1) := by linarith [hps.1]
  have hps2 : T.procStart (S.mach b) (K+1) ≤ T.s (S.mach b) (K+2) := hps.2
  have hdy : γ (S.mach b) * S.d b.1 ≤
      T.y b (T.s (S.mach b) (K+2)) - T.y b (T.procStart (S.mach b) (K+1)) := by
    rcases hor with h | h
    · have hfr : (T.s (S.mach b) (K+2) - T.procStart (S.mach b) (K+1)) / S.tau b ≤
          T.y b (T.s (S.mach b) (K+2)) - T.y b (T.procStart (S.mach b) (K+1)) :=
        ks_full_rate T hT b (K+1) hβ hxpos
      have e1 : T.s (S.mach b) (K+2) - T.procStart (S.mach b) (K+1) = runCap S γ b := by
        linarith
      rw [e1] at hfr
      have e2 : runCap S γ b / S.tau b = γ (S.mach b) * S.d b.1 := by
        unfold runCap; rw [mul_div_assoc, div_self hτ.ne', mul_one]
      linarith
    · have b1 := T.balance b _ hps0
      have b2 := T.balance b _ (hps0.trans hps2)
      have hi := ks_inflow_mono T b _ _ hps0 hps2
      linarith
  have hymono := ks_y_mono T b tIn (T.procStart (S.mach b) (K+1)) h0 (by linarith [hps.1])
  have hdiff := ks_backlog_diff T b tIn (T.s (S.mach b) (K+2)) h0 (by linarith)
  have h1 : S.d b.1 * (T.s (S.mach b) (K+2) - tIn) ≤
      S.d b.1 * (γ (S.mach b) - zeta S γ (S.mach b)) := mul_le_mul_of_nonneg_left hbd hd.le
  have h3 : S.tau b * (S.d b.1 * (T.s (S.mach b) (K+2) - tIn) -
      (T.y b (T.s (S.mach b) (K+2)) - T.y b tIn)) ≤
      S.tau b * (-(zeta S γ (S.mach b) * S.d b.1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hτ.le
  have e : S.tau b * (-(zeta S γ (S.mach b) * S.d b.1)) =
      -(zeta S γ (S.mach b) * S.d b.1 * S.tau b) := by ring
  exact ⟨K, hnr, by linarith, hbd, by linarith⟩

theorem backlog_decrease_core {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn : ℝ)
    (hin : T.EntersQ z b tIn) (k : ℕ) (hk : T.IsNextRun b tIn k)
    (hnext : T.HasNext (S.mach b) k)
    (hlevel : γ (S.mach b) * S.d b.1 ≤ T.x b tIn) :
    backlog T b (T.s (S.mach b) (k + 1)) ≤
      backlog T b tIn - zeta S γ (S.mach b) * S.d b.1 * S.tau b := by
  obtain ⟨K, hnr, _, _, hb⟩ := ks_lemma2 T hcap hγ hz hT b tIn hin.1 hlevel
  have := ks_nextRun_unique T b tIn k (K+1) hk hnr
  subst this
  exact hb


lemma ks_lemma3 (T : Trajectory S) (hcap : S.CapacityCondition) {γ : Fin M → ℝ}
    (hγ : GammaCondition S γ) {z : Buffer S → ℝ} (hz : ∀ b, 0 ≤ z b) (hT : T.Supervised γ z)
    (b : Buffer S) (tIn t' : ℝ) (hq : T.QueuedAt z b tIn)
    (hge : ∀ σ ∈ Set.Icc tIn t', max (γ (S.mach b) * S.d b.1) (z b) ≤ T.x b σ)
    (hgt : ∀ σ ∈ Set.Ioc tIn t', z b < T.x b σ) :
    t' - tIn ≤
      (1 + backlog T b tIn / (zeta S γ (S.mach b) * S.d b.1 * S.tau b)) *
        (γ (S.mach b) - zeta S γ (S.mach b)) := by
  have hW := ks_W_nonneg S hcap γ hγ (S.mach b)
  have hD : 0 < zeta S γ (S.mach b) * S.d b.1 * S.tau b := by
    have := ks_zeta_pos S γ hγ (S.mach b)
    have := S.d_pos b.1
    have : 0 < S.tau b := S.τ_pos _ _
    positivity
  have h0 : 0 ≤ tIn := hq.1
  have hB0 := ks_backlog_nonneg T b tIn h0
  obtain ⟨W, hWe⟩ : ∃ W, γ (S.mach b) - zeta S γ (S.mach b) = W := ⟨_, rfl⟩
  obtain ⟨D, hDe⟩ : ∃ D, zeta S γ (S.mach b) * S.d b.1 * S.tau b = D := ⟨_, rfl⟩
  rw [hWe] at hW ⊢
  rw [hDe] at hD ⊢
  have claim : ∀ n : ℕ, (∃ c, tIn ≤ c ∧ c ≤ t' ∧ c - tIn ≤ n * W ∧
      backlog T b c ≤ backlog T b tIn - n * D ∧ T.QueuedAt z b c) ∨ t' - tIn ≤ n * W := by
    intro n
    induction n with
    | zero =>
      by_cases h : tIn ≤ t'
      · left; exact ⟨tIn, le_rfl, h, by simp, by simp, hq⟩
      · right; simp; linarith
    | succ n ih =>
      have e1 : ((n:ℝ) + 1) * W = n * W + W := by ring
      have e2 : ((n:ℝ) + 1) * D = n * D + D := by ring
      push_cast
      rcases ih with ⟨c, hc1, hc2, hc3, hc4, hc5⟩ | h
      · obtain ⟨K, _, hlt, hbd, hbk⟩ := ks_lemma2 T hcap hγ hz hT b c hc5
          (le_trans (le_max_left _ _) (hge c ⟨hc1, hc2⟩))
        rw [hWe] at hbd
        rw [hDe] at hbk
        by_cases hK : T.s (S.mach b) (K+2) ≤ t'
        · left
          refine ⟨T.s (S.mach b) (K+2), by linarith, hK, by linarith, by linarith, ?_⟩
          exact ks_queued_switch T hcap hγ hz hT b (K+1) (hgt _ ⟨by linarith, hK⟩)
        · right; linarith
      · right
        nlinarith
  have hfl := Nat.lt_floor_add_one (backlog T b tIn / D)
  have hfl2 := Nat.floor_le (div_nonneg hB0 hD.le)
  rcases claim (⌊backlog T b tIn / D⌋₊ + 1) with ⟨c, hc1, hc2, hc3, hc4, hc5⟩ | h
  · exfalso
    have := ks_backlog_nonneg T b c (h0.trans hc1)
    push_cast at hc4
    have h6 : backlog T b tIn < ((⌊backlog T b tIn / D⌋₊ : ℝ) + 1) * D :=
      (div_lt_iff₀ hD).mp hfl
    linarith
  · push_cast at h
    have : ((⌊backlog T b tIn / D⌋₊ : ℝ) + 1) * W ≤ (1 + backlog T b tIn / D) * W :=
      mul_le_mul_of_nonneg_right (by linarith) hW
    linarith

theorem large_duration_core {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (tIn t' : ℝ)
    (hin : T.EntersQ z b tIn)
    (hge : ∀ σ ∈ Set.Icc tIn t', max (γ (S.mach b) * S.d b.1) (z b) ≤ T.x b σ)
    (hgt : ∀ σ ∈ Set.Ioc tIn t', z b < T.x b σ) :
    t' - tIn ≤
      (1 + backlog T b tIn / (zeta S γ (S.mach b) * S.d b.1 * S.tau b)) *
        (γ (S.mach b) - zeta S γ (S.mach b)) :=
  ks_lemma3 T hcap hγ hz hT b tIn t' hin.1 hge hgt


theorem interval_bound_core {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) (b : Buffer S) (t t' : ℝ) (ht : 0 ≤ t)
    (hx : ∀ σ ∈ Set.Icc t t',
      max (γ (S.mach b) * S.d b.1) (z b) + γ (S.mach b) * S.d b.1 ≤ T.x b σ) :
    t' - t ≤
      (2 + (γ (S.mach b) - zeta S γ (S.mach b)) / zeta S γ (S.mach b)) *
          (γ (S.mach b) - zeta S γ (S.mach b)) +
        (γ (S.mach b) - zeta S γ (S.mach b)) /
            (zeta S γ (S.mach b) * S.d b.1 * S.tau b) * backlog T b t := by
  have hW := ks_W_nonneg S hcap γ hγ (S.mach b)
  have hζ := ks_zeta_pos S γ hγ (S.mach b)
  have hd := S.d_pos b.1
  have hτ : 0 < S.tau b := S.τ_pos _ _
  have hD : 0 < zeta S γ (S.mach b) * S.d b.1 * S.tau b := by positivity
  have hγd : 0 < γ (S.mach b) * S.d b.1 := mul_pos (ks_gamma_pos S hcap γ hγ _) hd
  have hB := ks_backlog_nonneg T b t ht
  have hmono := ks_s_mono T hT (S.mach b)
  have hbB : b ∈ S.B (S.mach b) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  obtain ⟨W, hWe⟩ : ∃ W, γ (S.mach b) - zeta S γ (S.mach b) = W := ⟨_, rfl⟩
  rw [hWe] at hW ⊢
  have hRHS : W ≤ (2 + W / zeta S γ (S.mach b)) * W +
      W / (zeta S γ (S.mach b) * S.d b.1 * S.tau b) * backlog T b t := by
    have h1 : 0 ≤ W / zeta S γ (S.mach b) * W := by positivity
    have h2 : 0 ≤ W / (zeta S γ (S.mach b) * S.d b.1 * S.tau b) * backlog T b t := by
      positivity
    have e : (2 + W / zeta S γ (S.mach b)) * W = 2 * W + W / zeta S γ (S.mach b) * W := by ring
    linarith
  by_cases htt : t' < t
  · linarith
  push_neg at htt
  have hgz : z b < max (γ (S.mach b) * S.d b.1) (z b) + γ (S.mach b) * S.d b.1 := by
    linarith [le_max_right (γ (S.mach b) * S.d b.1) (z b)]
  have hxt : ∀ σ ∈ Set.Icc t t', z b < T.x b σ := fun σ hσ => lt_of_lt_of_le hgz (hx σ hσ)
  have hge : ∀ σ ∈ Set.Icc t t', max (γ (S.mach b) * S.d b.1) (z b) ≤ T.x b σ :=
    fun σ hσ => le_trans (by linarith) (hx σ hσ)
  obtain ⟨k0, hk0a, hk0b⟩ := ks_exists_run T hT (S.mach b) t ht
  by_cases hβ : T.β (S.mach b) k0 = b
  · have hlen : T.s (S.mach b) (k0+1) - T.s (S.mach b) k0 ≤ W := by
      have h1 := ks_run_len T hT (S.mach b) k0
      rw [hβ] at h1
      have h2 := Finset.single_le_sum (f := ksF S γ (S.mach b))
        (fun c hc => ks_F_nonneg S hcap γ hγ _ c hc) hbB
      rw [ks_sumF, hWe] at h2
      linarith
    by_cases hte : t' < T.s (S.mach b) (k0+1)
    · linarith
    push_neg at hte
    have hq := ks_queued_switch T hcap hγ hz hT b k0 (hxt _ ⟨hk0b.le, hte⟩)
    have h3 := ks_lemma3 T hcap hγ hz hT b (T.s (S.mach b) (k0+1)) t' hq
      (fun σ hσ => hge σ ⟨by linarith [hσ.1], hσ.2⟩)
      (fun σ hσ => hxt σ ⟨by linarith [hσ.1], hσ.2⟩)
    rw [hWe] at h3
    have hbg := ks_backlog_growth T b t (T.s (S.mach b) (k0+1)) ht hk0b.le
    have hbg2 : backlog T b (T.s (S.mach b) (k0+1)) ≤ backlog T b t + S.tau b * S.d b.1 * W := by
      have : S.tau b * S.d b.1 * (T.s (S.mach b) (k0+1) - t) ≤ S.tau b * S.d b.1 * W :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h4 : backlog T b (T.s (S.mach b) (k0+1)) / (zeta S γ (S.mach b) * S.d b.1 * S.tau b) ≤
        (backlog T b t + S.tau b * S.d b.1 * W) / (zeta S γ (S.mach b) * S.d b.1 * S.tau b) :=
      div_le_div_of_nonneg_right hbg2 hD.le
    have h5 : (1 + backlog T b (T.s (S.mach b) (k0+1)) /
        (zeta S γ (S.mach b) * S.d b.1 * S.tau b)) * W ≤
        (1 + (backlog T b t + S.tau b * S.d b.1 * W) /
        (zeta S γ (S.mach b) * S.d b.1 * S.tau b)) * W :=
      mul_le_mul_of_nonneg_right (by linarith) hW
    have e6 : (1 + (backlog T b t + S.tau b * S.d b.1 * W) /
        (zeta S γ (S.mach b) * S.d b.1 * S.tau b)) * W + W =
        (2 + W / zeta S γ (S.mach b)) * W +
          W / (zeta S γ (S.mach b) * S.d b.1 * S.tau b) * backlog T b t := by
      field_simp
      ring
    linarith
  · have hq : T.QueuedAt z b t := by
      refine ⟨ht, Or.inl ⟨T.s (S.mach b) (k0+1), hk0b, fun σ hσ => ⟨?_, ?_⟩⟩⟩
      · intro hon
        exact hβ (ks_onRun_unique T hT b σ k0 (by linarith [hσ.1]) hσ.2 hon)
      · refine lt_of_lt_of_le (hxt t ⟨le_rfl, htt⟩) (ks_x_up T b t σ ht hσ.1.le ?_)
        intro σ' hσ' hp
        exact hβ (ks_onRun_unique T hT b σ' k0 (by linarith [hσ'.1]) (by linarith [hσ'.2, hσ.2])
          (ks_proc_onRun T b σ' hp))
    have h3 := ks_lemma3 T hcap hγ hz hT b t t' hq hge (fun σ hσ => hxt σ ⟨hσ.1.le, hσ.2⟩)
    rw [hWe] at h3
    have e6 : (1 + backlog T b t / (zeta S γ (S.mach b) * S.d b.1 * S.tau b)) * W =
        W + W / (zeta S γ (S.mach b) * S.d b.1 * S.tau b) * backlog T b t := by ring
    have h1 : 0 ≤ W / zeta S γ (S.mach b) * W := by positivity
    have e : (2 + W / zeta S γ (S.mach b)) * W = 2 * W + W / zeta S γ (S.mach b) * W := by ring
    linarith

lemma ks_backlog_split (T : Trajectory S) (p : Fin P) (i : ℕ) (hi : i < S.n p) (u : ℝ) :
    backlog T ⟨p, ⟨i, hi⟩⟩ u = S.tau ⟨p, ⟨i, hi⟩⟩ * (T.x ⟨p, ⟨i, hi⟩⟩ u +
      ∑ j ∈ Finset.Iio (⟨i, hi⟩ : Fin (S.n p)), T.x ⟨p, j⟩ u) := by
  unfold backlog
  rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons, mul_add, Finset.mul_sum]

theorem stabilizes_core {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) :
    T.IsStable := by
  have key : ∀ (p : Fin P) (i : ℕ) (hi : i < S.n p),
      ∃ C, ∀ t, 0 ≤ t → T.x ⟨p, ⟨i, hi⟩⟩ t ≤ C := by
    intro p i
    induction i using Nat.strong_induction_on with
    | _ i IH =>
    intro hi
    classical
    have hup : ∃ C', ∀ t, 0 ≤ t →
        ∑ j ∈ Finset.Iio (⟨i, hi⟩ : Fin (S.n p)), T.x ⟨p, j⟩ t ≤ C' := by
      let Cf : Fin (S.n p) → ℝ := fun j =>
        if h : j.val < i then Classical.choose (IH j.val h j.isLt) else 0
      refine ⟨∑ j ∈ Finset.Iio (⟨i, hi⟩ : Fin (S.n p)), Cf j,
        fun t ht => Finset.sum_le_sum (fun j hj => ?_)⟩
      have hj' : j.val < i := by
        have := Finset.mem_Iio.mp hj
        exact this
      simp only [Cf, dif_pos hj']
      exact Classical.choose_spec (IH j.val hj' j.isLt) t ht
    obtain ⟨C', hC'⟩ := hup
    have hC'0 : 0 ≤ C' :=
      le_trans (Finset.sum_nonneg (fun j _ => T.x_nonneg _ 0 le_rfl)) (hC' 0 le_rfl)
    have hbk0 : ∀ u, 0 ≤ u → backlog T ⟨p, ⟨i, hi⟩⟩ u ≤
        S.tau ⟨p, ⟨i, hi⟩⟩ * (T.x ⟨p, ⟨i, hi⟩⟩ u + C') := by
      intro u hu
      rw [ks_backlog_split]
      exact mul_le_mul_of_nonneg_left (by linarith [hC' u hu]) (S.τ_pos _ _).le
    obtain ⟨b, hb⟩ : ∃ b : Buffer S, b = ⟨p, ⟨i, hi⟩⟩ := ⟨_, rfl⟩
    rw [← hb] at hbk0 ⊢
    have hτ : 0 < S.tau b := S.τ_pos _ _
    have hW := ks_W_nonneg S hcap γ hγ (S.mach b)
    have hζ := ks_zeta_pos S γ hγ (S.mach b)
    have hd := S.d_pos b.1
    have hγd : 0 < γ (S.mach b) * S.d b.1 := mul_pos (ks_gamma_pos S hcap γ hγ _) hd
    obtain ⟨a, ha⟩ : ∃ a, (2 + (γ (S.mach b) - zeta S γ (S.mach b)) / zeta S γ (S.mach b)) *
          (γ (S.mach b) - zeta S γ (S.mach b)) = a := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, (γ (S.mach b) - zeta S γ (S.mach b)) /
            (zeta S γ (S.mach b) * S.d b.1 * S.tau b) = c := ⟨_, rfl⟩
    have ha0 : 0 ≤ a := by rw [← ha]; positivity
    have hc0 : 0 ≤ c := by rw [← hc]; positivity
    obtain ⟨R, hR0, hR⟩ := ks_x_growth T b
    obtain ⟨G, hG⟩ : ∃ G, G = max (max (γ (S.mach b) * S.d b.1) (z b) +
      γ (S.mach b) * S.d b.1) (T.x b 0) := ⟨_, rfl⟩
    have hgG : max (γ (S.mach b) * S.d b.1) (z b) + γ (S.mach b) * S.d b.1 ≤ G :=
      hG ▸ le_max_left _ _
    have hx0G : T.x b 0 ≤ G := hG ▸ le_max_right _ _
    have hG0 : 0 ≤ G := le_trans (T.x_nonneg b 0 le_rfl) hx0G
    have hL1 : 0 ≤ c * (S.tau b * (C' + G + 2 * R)) :=
      mul_nonneg hc0 (mul_nonneg hτ.le (by linarith))
    refine ⟨G + R * ((1 + a + c * (S.tau b * (C' + G + 2 * R))) + 1), fun t ht => ?_⟩
    let A : Set ℝ := {σ | σ ∈ Set.Icc 0 t ∧ T.x b σ ≤ G}
    have hA0 : (0:ℝ) ∈ A := ⟨⟨le_rfl, ht⟩, hx0G⟩
    have hbdd : BddAbove A := ⟨t, fun σ hσ => hσ.1.2⟩
    have ht0 : sSup A ≤ t := csSup_le ⟨0, hA0⟩ (fun σ hσ => hσ.1.2)
    have ht00 : 0 ≤ sSup A := le_csSup hbdd hA0
    obtain ⟨σ, hσA, hσlt⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ (show sSup A - 1 < sSup A by linarith)
    have hσle : σ ≤ sSup A := le_csSup hbdd hσA
    have hxσ : T.x b σ ≤ G := hσA.2
    have hσ0 : 0 ≤ σ := hσA.1.1
    have hnotA : ∀ u, sSup A < u → u ≤ t → G < T.x b u := by
      intro u h1 h2
      by_contra hh
      push_neg at hh
      have := le_csSup hbdd (show u ∈ A from ⟨⟨by linarith, h2⟩, hh⟩)
      linarith
    have hlen : t - sSup A ≤ 1 + a + c * (S.tau b * (C' + G + 2 * R)) := by
      by_cases h1 : t ≤ sSup A + 1
      · linarith
      · push_neg at h1
        have L4 := interval_bound_core S hcap γ hγ z hz T hT b (sSup A + 1) t (by linarith)
          (fun u hu => le_trans hgG (le_of_lt (hnotA u (by linarith [hu.1]) hu.2)))
        rw [ha, hc] at L4
        have hxu : T.x b (sSup A + 1) ≤ G + 2 * R := by
          have h7 := hR σ (sSup A + 1) hσ0 (by linarith)
          have h8 : R * (sSup A + 1 - σ) ≤ R * 2 := mul_le_mul_of_nonneg_left (by linarith) hR0
          linarith
        have hbku := hbk0 (sSup A + 1) (by linarith)
        have h5 : S.tau b * (T.x b (sSup A + 1) + C') ≤ S.tau b * (C' + G + 2 * R) :=
          mul_le_mul_of_nonneg_left (by linarith) hτ.le
        have h6 : c * backlog T b (sSup A + 1) ≤ c * (S.tau b * (C' + G + 2 * R)) :=
          mul_le_mul_of_nonneg_left (by linarith) hc0
        linarith
    have hxt := hR σ t hσ0 (by linarith)
    have h9 : R * (t - σ) ≤ R * ((1 + a + c * (S.tau b * (C' + G + 2 * R))) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hR0
    linarith
  intro b
  obtain ⟨p, ⟨i, hi⟩⟩ := b
  exact key p i hi

end KumarSeidman.Supervisor

open KumarSeidman.Supervisor


theorem solution {P M : ℕ} (S : System P M) (hcap : S.CapacityCondition)
    (γ : Fin M → ℝ) (hγ : GammaCondition S γ) (z : Buffer S → ℝ) (hz : ∀ b, 0 ≤ z b)
    (T : Trajectory S) (hT : T.Supervised γ z) :
    T.IsStable := by
  exact stabilizes_core S hcap γ hγ z hz T hT
