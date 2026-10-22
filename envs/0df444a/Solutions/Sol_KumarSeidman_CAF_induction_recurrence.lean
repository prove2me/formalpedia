-- Prove2me | solution 1 for KumarSeidman.CAF.induction_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:35:48.197467+00:00
-- url     : https://prove2.me/submissions/0cb42386-0393-46f3-95ed-80dae4c5a2ec

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov



namespace KumarSeidman.CAF

variable {P M : ℕ}

namespace KSAux

def blk (S : System P M) (m : Fin M) (p : Fin P) (i k : Fin (S.n p)) : Prop :=
  i ≤ k ∧ ∀ l : Fin (S.n p), i ≤ l → l ≤ k → S.μ p l = m

instance (S : System P M) (m : Fin M) (p : Fin P) (i k : Fin (S.n p)) :
    Decidable (blk S m p i k) := by unfold blk; infer_instance

noncomputable def Xb {S : System P M} (T : Trajectory S) (m : Fin M) (c : Buffer S) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => blk S m c.1 i c.2), T.x ⟨c.1, i⟩ t

lemma y_rate {S : System P M} (T : Trajectory S) (b : Buffer S) {t1 t2 : ℝ} (h1 : 0 ≤ t1)
    (h12 : t1 ≤ t2) : T.y b t2 - T.y b t1 ≤ (t2 - t1) / S.tau b := by
  have h := T.rate_cap b t1 t2 h1 h12
  have hτ : 0 < S.tau b := S.τ_pos _ _
  refine h.trans (div_le_div_of_nonneg_right ?_ hτ.le)
  calc _ ≤ (MeasureTheory.volume (Set.Icc t1 t2)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Icc])
          (MeasureTheory.measure_mono Set.inter_subset_left)
    _ = t2 - t1 := by rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

lemma y_mono' {S : System P M} (T : Trajectory S) (b : Buffer S) {t1 t2 : ℝ} (h1 : 0 ≤ t1)
    (h12 : t1 ≤ t2) : T.y b t1 ≤ T.y b t2 :=
  T.y_mono b (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (h1.trans h12)) h12

lemma dPrime_pos (S : System P M) (b : Buffer S) : 0 < S.dPrime b := by
  unfold System.dPrime
  split
  · exact S.d_pos _
  · split_ifs
    · exact one_div_pos.mpr (S.τ_pos _ _)
    · exact S.d_pos _

lemma rhoPrime_nonneg (S : System P M) (m : Fin M) : 0 ≤ S.rhoPrime m :=
  Finset.sum_nonneg (fun b _ => (mul_pos (dPrime_pos S b) (S.τ_pos _ _)).le)

lemma dPrime_congr (S : System P M) (p : Fin P) (i i' : Fin (S.n p))
    (hl : S.lam ⟨p, i⟩ = S.lam ⟨p, i'⟩) (hm : S.μ p i = S.μ p i') :
    S.dPrime ⟨p, i⟩ = S.dPrime ⟨p, i'⟩ := by
  classical
  unfold System.dPrime
  rw [hl]
  have hm' : S.mach ⟨p, i⟩ = S.mach ⟨p, i'⟩ := hm
  split
  · rfl
  · exact if_congr (by rw [hm']) rfl rfl

lemma X_step {S : System P M} (T : Trajectory S) (m : Fin M) (g : ℝ) (hg : 0 ≤ g)
    {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h12 : t1 ≤ t2)
    (H : ∀ (p : Fin P) (j : ℕ) (hj : j + 1 < S.n p), S.μ p ⟨j, by omega⟩ ≠ m →
       S.μ p ⟨j+1, hj⟩ = m → ¬ S.Dicon (S.μ p ⟨j, by omega⟩) m →
       T.y ⟨p, ⟨j, by omega⟩⟩ t2 - T.y ⟨p, ⟨j, by omega⟩⟩ t1 ≤ S.d p * (t2 - t1) + g)
    (p : Fin P) : ∀ (kv : ℕ) (hk : kv < S.n p), S.μ p ⟨kv, hk⟩ = m →
      Xb T m ⟨p, ⟨kv, hk⟩⟩ t2 - Xb T m ⟨p, ⟨kv, hk⟩⟩ t1 ≤
        S.dPrime ⟨p, ⟨kv, hk⟩⟩ * (t2 - t1) + g
          - (T.y ⟨p, ⟨kv, hk⟩⟩ t2 - T.y ⟨p, ⟨kv, hk⟩⟩ t1) := by
  intro kv
  induction kv with
  | zero =>
    intro hk hμ
    have hf : Finset.univ.filter (fun i => blk S m p i ⟨0, hk⟩) = {⟨0, hk⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      unfold blk
      constructor
      · rintro ⟨hi, -⟩
        exact Fin.ext (by have := Fin.le_def.mp hi; simp at this; omega)
      · rintro rfl
        refine ⟨le_rfl, fun l hl1 hl2 => ?_⟩
        have : l = ⟨0, hk⟩ := le_antisymm hl2 hl1
        rw [this]; exact hμ
    have hlam : S.lam ⟨p, ⟨0, hk⟩⟩ = ⊥ := by
      unfold System.lam
      rw [Finset.max_eq_bot, Finset.filter_eq_empty_iff]
      intro j _ ⟨hj, _⟩
      exact absurd hj (by simp [Fin.lt_def])
    have hd : S.dPrime ⟨p, ⟨0, hk⟩⟩ = S.d p := by
      unfold System.dPrime; rw [hlam]
    have hprev : S.prev ⟨p, ⟨0, hk⟩⟩ = none := by simp [System.prev]
    simp only [Xb, hf, Finset.sum_singleton]
    rw [T.balance _ t2 (by linarith), T.balance _ t1 h1]
    simp only [inflow, hprev, hd]
    nlinarith
  | succ j ih =>
    intro hk hμ
    have hprev : S.prev ⟨p, ⟨j+1, hk⟩⟩ = some ⟨p, ⟨j, by omega⟩⟩ := by simp [System.prev]
    have hbal : ∀ t, 0 ≤ t → T.x ⟨p, ⟨j+1, hk⟩⟩ t =
        T.x ⟨p, ⟨j+1, hk⟩⟩ 0 + T.y ⟨p, ⟨j, by omega⟩⟩ t - T.y ⟨p, ⟨j+1, hk⟩⟩ t := by
      intro t ht
      rw [T.balance _ t ht]
      simp only [inflow, hprev]
    by_cases hsame : S.μ p ⟨j, by omega⟩ = m
    · have ihj := ih (by omega) hsame
      have hf : Finset.univ.filter (fun i => blk S m p i ⟨j+1, hk⟩) =
          insert ⟨j+1, hk⟩ (Finset.univ.filter (fun i => blk S m p i ⟨j, by omega⟩)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        unfold blk
        constructor
        · rintro ⟨hi, hl⟩
          by_cases hij : i = ⟨j+1, hk⟩
          · left; exact hij
          · right
            have hi' : i.val ≤ j := by
              have := Fin.le_def.mp hi
              have : i.val ≠ j + 1 := fun h => hij (Fin.ext h)
              simp at *; omega
            refine ⟨Fin.le_def.mpr hi', fun l hl1 hl2 => hl l hl1 ?_⟩
            exact Fin.le_def.mpr (by have := Fin.le_def.mp hl2; simp at this ⊢; omega)
        · rintro (rfl | ⟨hi, hl⟩)
          · refine ⟨le_rfl, fun l hl1 hl2 => ?_⟩
            have : l = ⟨j+1, hk⟩ := le_antisymm hl2 hl1
            rw [this]; exact hμ
          · refine ⟨Fin.le_def.mpr (by have := Fin.le_def.mp hi; simp at this ⊢; omega),
              fun l hl1 hl2 => ?_⟩
            by_cases hlj : l.val ≤ j
            · exact hl l hl1 (Fin.le_def.mpr hlj)
            · have : l = ⟨j+1, hk⟩ := Fin.ext (show l.val = j + 1 by have h2 : l.val ≤ j + 1 := Fin.le_def.mp hl2; omega)
              rw [this]; exact hμ
      have hnot : (⟨j+1, hk⟩ : Fin (S.n p)) ∉
          Finset.univ.filter (fun i => blk S m p i ⟨j, by omega⟩) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        unfold blk
        rintro ⟨h, -⟩; have := Fin.le_def.mp h; simp at this
      have hlam : S.lam ⟨p, ⟨j+1, hk⟩⟩ = S.lam ⟨p, ⟨j, by omega⟩⟩ := by
        unfold System.lam
        congr 1
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, System.mach, Fin.lt_def]
        rw [hμ, hsame]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
          · exact h
          · have ha : a = ⟨j, by dsimp only; omega⟩ := Fin.ext h
            rw [ha] at h2; exact absurd hsame h2
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      have hd : S.dPrime ⟨p, ⟨j+1, hk⟩⟩ = S.dPrime ⟨p, ⟨j, by omega⟩⟩ := by
        exact dPrime_congr S p _ _ hlam (by rw [hμ, hsame])
      have hX : ∀ t, Xb T m ⟨p, ⟨j+1, hk⟩⟩ t = T.x ⟨p, ⟨j+1, hk⟩⟩ t + Xb T m ⟨p, ⟨j, by omega⟩⟩ t := by
        intro t
        simp only [Xb]
        rw [hf, Finset.sum_insert hnot]
      rw [hX, hX, hbal t2 (by linarith), hbal t1 h1, hd]
      linarith
    · have hf : Finset.univ.filter (fun i => blk S m p i ⟨j+1, hk⟩) = {⟨j+1, hk⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        unfold blk
        constructor
        · rintro ⟨hi, hl⟩
          by_contra hij
          have hi' : i.val ≤ j := by
            have := Fin.le_def.mp hi
            have : i.val ≠ j + 1 := fun h => hij (Fin.ext h)
            simp at *; omega
          exact hsame (hl ⟨j, by omega⟩ (Fin.le_def.mpr hi') (Fin.le_def.mpr (by simp)))
        · rintro rfl
          refine ⟨le_rfl, fun l hl1 hl2 => ?_⟩
          have : l = ⟨j+1, hk⟩ := le_antisymm hl2 hl1
          rw [this]; exact hμ
      have hlam : S.lam ⟨p, ⟨j+1, hk⟩⟩ = ((⟨j, by omega⟩ : Fin (S.n p)) : WithBot (Fin (S.n p))) := by
        unfold System.lam
        apply le_antisymm
        · apply Finset.max_le
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at ha
          exact WithBot.coe_le_coe.mpr (Fin.le_def.mpr (by simp at ha ⊢; omega))
        · apply Finset.le_max
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, System.mach]
          refine ⟨by simp, ?_⟩
          rw [hμ]; exact hsame
      have hX : ∀ t, Xb T m ⟨p, ⟨j+1, hk⟩⟩ t = T.x ⟨p, ⟨j+1, hk⟩⟩ t := by
        intro t
        simp only [Xb]
        rw [hf, Finset.sum_singleton]
      rw [hX, hX, hbal t2 (by linarith), hbal t1 h1]
      classical
      have hd : S.dPrime ⟨p, ⟨j+1, hk⟩⟩ = if S.Dicon (S.μ p ⟨j, by omega⟩) m
          then 1 / S.τ p ⟨j, by omega⟩ else S.d p := by
        unfold System.dPrime
        rw [hlam]
        simp only [System.mach, hμ]
      rw [hd]
      split_ifs with hdc
      · have := y_rate T ⟨p, ⟨j, by omega⟩⟩ h1 h12
        simp only [System.tau] at this
        have : (t2 - t1) / S.τ p ⟨j, by omega⟩ = 1 / S.τ p ⟨j, by omega⟩ * (t2 - t1) := by ring
        linarith
      · have := H p j hk hsame hμ hdc
        linarith

lemma V_eq {S : System P M} (T : Trajectory S) (m : Fin M) (t : ℝ) :
    T.V m t = ∑ c ∈ S.B m, S.tau c * Xb T m c t := by
  classical
  unfold Trajectory.V System.workAhead System.B Xb
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have L : ∀ i : Fin (S.n p), (if S.mach ⟨p, i⟩ = m then T.x ⟨p, i⟩ t *
      ∑ k ∈ Finset.univ.filter (fun k : Fin (S.n p) => i ≤ k ∧
        ∀ l : Fin (S.n p), i ≤ l → l ≤ k → S.μ p l = S.mach ⟨p, i⟩), S.τ p k else 0) =
      ∑ k : Fin (S.n p), if blk S m p i k then T.x ⟨p, i⟩ t * S.τ p k else 0 := by
    intro i
    split_ifs with hi
    · rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [blk, hi]
    · symm
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [if_neg]
      rintro ⟨hik, hl⟩
      exact hi (hl i le_rfl hik)
  have R : ∀ k : Fin (S.n p), (if S.mach ⟨p, k⟩ = m then S.tau ⟨p, k⟩ *
      ∑ i ∈ Finset.univ.filter (fun i => blk S m p i k), T.x ⟨p, i⟩ t else 0) =
      ∑ i : Fin (S.n p), if blk S m p i k then T.x ⟨p, i⟩ t * S.τ p k else 0 := by
    intro k
    split_ifs with hk
    · rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs <;> simp [System.tau, mul_comm]
    · symm
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [if_neg]
      rintro ⟨hik, hl⟩
      exact hk (hl k hik le_rfl)
  simp only [L, R]
  exact Finset.sum_comm

lemma V_incr {S : System P M} (T : Trajectory S) (m : Fin M) (g : ℝ) (hg : 0 ≤ g)
    {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h12 : t1 ≤ t2)
    (H : ∀ (p : Fin P) (j : ℕ) (hj : j + 1 < S.n p), S.μ p ⟨j, by omega⟩ ≠ m →
       S.μ p ⟨j+1, hj⟩ = m → ¬ S.Dicon (S.μ p ⟨j, by omega⟩) m →
       T.y ⟨p, ⟨j, by omega⟩⟩ t2 - T.y ⟨p, ⟨j, by omega⟩⟩ t1 ≤ S.d p * (t2 - t1) + g) :
    T.V m t2 - T.V m t1 ≤ S.rhoPrime m * (t2 - t1) + g * ∑ c ∈ S.B m, S.tau c
       - ∑ c ∈ S.B m, S.tau c * (T.y c t2 - T.y c t1) := by
  rw [V_eq, V_eq, ← Finset.sum_sub_distrib, System.rhoPrime, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro c hc
  have hcm : S.mach c = m := (Finset.mem_filter.mp hc).2
  obtain ⟨p, ⟨kv, hk⟩⟩ := c
  have := X_step T m g hg h1 h12 H p kv hk hcm
  have hτ : 0 < S.tau ⟨p, ⟨kv,hk⟩⟩ := S.τ_pos _ _
  nlinarith

lemma s_nonneg {S : System P M} (T : Trajectory S) (m : Fin M) :
    ∀ k : ℕ, (k : ℕ∞) < T.N m → 0 ≤ T.s m k := by
  intro k
  induction k with
  | zero => intro _; rw [T.s_zero]
  | succ j ih =>
    intro hj
    have hj' : (j : ℕ∞) < T.N m := lt_of_le_of_lt (by exact_mod_cast Nat.le_succ j) hj
    have h := T.setup_not_cut m j hj
    have hr : 0 ≤ runSetup S (T.β m) j := by
      cases j with
      | zero => simp [runSetup]
      | succ i => exact S.δ_nonneg _ _
    linarith [ih hj']

lemma delta_le_deltaBar (S : System P M) (m : Fin M) (b b' : Buffer S) (hb : b ∈ S.B m)
    (hb' : b' ∈ S.B m) (hne : b ≠ b') : S.δ b b' ≤ S.deltaBar m := by
  unfold System.deltaBar
  rw [Finset.le_fold_max]
  right
  exact ⟨(b, b'), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, hb'⟩, hne⟩, le_rfl⟩

lemma deltaBar_nonneg (S : System P M) (m : Fin M) : 0 ≤ S.deltaBar m := by
  unfold System.deltaBar
  rw [Finset.le_fold_max]
  left; exact le_rfl

lemma V_zero_of_clear {S : System P M} (T : Trajectory S) (hT : T.IsClearing) (m : Fin M)
    (k : ℕ) (hkN : (k : ℕ∞) < T.N m) (t : ℝ) (ht0 : 0 ≤ t) (hta : T.procStart m k < t)
    (hte : T.HasNext m k → t < T.s m (k+1)) (hx : T.x (T.β m k) t = 0) : T.V m t = 0 := by
  unfold Trajectory.V
  apply Finset.sum_eq_zero
  intro c hc
  have : T.x c t = 0 := by
    by_cases hcb : c = T.β m k
    · rw [hcb, hx]
    · have h := (hT m k hkN).1 t hta hte
      have hnd : ¬ T.Demanding c t := fun hd => h ⟨hx, c, hc, hcb, hd⟩
      unfold Trajectory.Demanding at hnd
      push_neg at hnd
      exact le_antisymm hnd.1 (T.x_nonneg c t ht0)
  rw [this, zero_mul]

lemma work_ge {S : System P M} (T : Trajectory S) (m : Fin M) (k : ℕ) (hkN : (k : ℕ∞) < T.N m)
    (tst : ℝ) (hst : T.procStart m k ≤ tst) (h0 : 0 ≤ T.procStart m k)
    (hpos : ∀ t, tst < t → t < T.s m (k+1) → 0 < T.x (T.β m k) t) (η : ℝ) (hη : 0 < η)
    (hle : tst ≤ T.s m (k+1)) :
    T.s m (k+1) - tst - 2 * η ≤
      S.tau (T.β m k) * (T.y (T.β m k) (T.s m (k+1)) - T.y (T.β m k) tst) := by
  have hτ : 0 < S.tau (T.β m k) := S.τ_pos _ _
  have hmono : T.y (T.β m k) tst ≤ T.y (T.β m k) (T.s m (k+1)) := y_mono' T _ (by linarith) hle
  by_cases hc : T.s m (k+1) - tst ≤ 2 * η
  · nlinarith
  · push_neg at hc
    have hbm : S.mach (T.β m k) = m := T.β_mem m k hkN
    have hfr := T.full_rate (T.β m k) (tst + η) (T.s m (k+1) - η) (by linarith) (by linarith) ?_ ?_
    · have m1 : T.y (T.β m k) tst ≤ T.y (T.β m k) (tst + η) :=
        y_mono' T _ (by linarith) (by linarith)
      have m2 : T.y (T.β m k) (T.s m (k+1) - η) ≤ T.y (T.β m k) (T.s m (k+1)) :=
        y_mono' T _ (by linarith) (by linarith)
      have key : S.tau (T.β m k) * (T.y (T.β m k) (T.s m (k+1) - η) - T.y (T.β m k) (tst + η))
          = T.s m (k+1) - η - (tst + η) := by
        rw [hfr]; field_simp
      nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr m1), mul_nonneg hτ.le (sub_nonneg.mpr m2)]
    · intro σ hσ
      rw [hbm]
      refine ⟨k, rfl, hkN, ?_, fun _ => by linarith [hσ.2]⟩
      have := hσ.1
      unfold Trajectory.procStart at hst
      linarith
    · intro σ hσ
      exact hpos σ (by linarith [hσ.1]) (by linarith [hσ.2])

lemma drift_gen {S : System P M} (T : Trajectory S) (hT : T.IsClearing) (m : Fin M) (k : ℕ)
    (hk : 1 ≤ k) (hnext : T.HasNext m k) (G : ℝ) (hG : 0 ≤ G)
    (hinc : ∀ t1 t2 : ℝ, 0 ≤ t1 → t1 ≤ t2 → T.V m t2 - T.V m t1 ≤
      S.rhoPrime m * (t2 - t1) + G - ∑ c ∈ S.B m, S.tau c * (T.y c t2 - T.y c t1))
    (hrho : S.rhoPrime m < 1) :
    T.V m (T.s m (k+1)) ≤ max G (T.V m (T.s m k) - (1 - S.rhoPrime m) *
      (T.s m (k+1) - T.s m k) + S.deltaBar m + G) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hrho0 := rhoPrime_nonneg S m
  have hkN : ((k'+1 : ℕ) : ℕ∞) < T.N m :=
    lt_trans (by exact_mod_cast Nat.lt_succ_self _) hnext
  have hk'N : ((k' : ℕ) : ℕ∞) < T.N m := lt_trans (by exact_mod_cast Nat.lt_succ_self _) hkN
  have hs0 : 0 ≤ T.s m (k'+1) := s_nonneg T m _ hkN
  have hsetup : T.procStart m (k'+1) ≤ T.s m (k'+1+1) := T.setup_not_cut m (k'+1) hnext
  have hcl := (hT m k' hk'N).2 hkN
  have hmemB : ∀ j : ℕ, (j : ℕ∞) < T.N m → T.β m j ∈ S.B m := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.β_mem m j hj⟩
  have hδ : T.procStart m (k'+1) - T.s m (k'+1) ≤ S.deltaBar m := by
    unfold Trajectory.procStart; simp only [runSetup]
    have := delta_le_deltaBar S m (T.β m k') (T.β m (k'+1)) (hmemB _ hk'N) (hmemB _ hkN)
      (Ne.symm hcl.2.1)
    linarith
  have hps : T.s m (k'+1) ≤ T.procStart m (k'+1) := by
    unfold Trajectory.procStart; simp only [runSetup]
    linarith [S.δ_nonneg (T.β m k') (T.β m (k'+1))]
  have hbB := hmemB _ hkN
  have hW : ∀ t1, 0 ≤ t1 → t1 ≤ T.s m (k'+1+1) →
      S.tau (T.β m (k'+1)) * (T.y (T.β m (k'+1)) (T.s m (k'+1+1)) - T.y (T.β m (k'+1)) t1) ≤
        ∑ c ∈ S.B m, S.tau c * (T.y c (T.s m (k'+1+1)) - T.y c t1) := by
    intro t1 h1 h2
    exact Finset.single_le_sum (f := fun c => S.tau c * (T.y c (T.s m (k'+1+1)) - T.y c t1))
      (fun c _ => mul_nonneg (S.τ_pos _ _).le (sub_nonneg.mpr (y_mono' T c h1 h2))) hbB
  by_cases hE : ∃ t, T.procStart m (k'+1) < t ∧ t < T.s m (k'+1+1) ∧ T.x (T.β m (k'+1)) t = 0
  · apply le_max_of_le_left
    let E := {t | T.procStart m (k'+1) < t ∧ t < T.s m (k'+1+1) ∧ T.x (T.β m (k'+1)) t = 0}
    have hne : E.Nonempty := hE
    have hbdd : BddAbove E := ⟨T.s m (k'+1+1), fun t ht => ht.2.1.le⟩
    obtain ⟨t0, ht0⟩ := hE
    have hts_ge : t0 ≤ sSup E := le_csSup hbdd ht0
    have hts_le : sSup E ≤ T.s m (k'+1+1) := csSup_le hne (fun t ht => ht.2.1.le)
    have hpos : ∀ t, sSup E < t → t < T.s m (k'+1+1) → 0 < T.x (T.β m (k'+1)) t := by
      intro t h1 h2
      rcases (T.x_nonneg (T.β m (k'+1)) t (by linarith [ht0.1])).lt_or_eq with h | h
      · exact h
      · exfalso
        have : t ∈ E := ⟨by linarith [ht0.1], h2, h.symm⟩
        linarith [le_csSup hbdd this]
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨t1, ht1E, ht1⟩ := exists_lt_of_lt_csSup hne (show sSup E - ε/4 < sSup E by linarith)
    have ht1le : t1 ≤ sSup E := le_csSup hbdd ht1E
    have hV1 : T.V m t1 = 0 :=
      V_zero_of_clear T hT m (k'+1) hkN t1 (by linarith [ht1E.1]) ht1E.1
        (fun _ => ht1E.2.1) ht1E.2.2
    have hwk := work_ge T m (k'+1) hkN (sSup E) (by linarith [ht0.1]) (by linarith) hpos (ε/4)
      (by linarith) hts_le
    have hinc1 := hinc t1 (T.s m (k'+1+1)) (by linarith [ht1E.1]) ht1E.2.1.le
    have hW1 := hW t1 (by linarith [ht1E.1]) ht1E.2.1.le
    have hmb : T.y (T.β m (k'+1)) t1 ≤ T.y (T.β m (k'+1)) (sSup E) :=
      y_mono' T _ (by linarith [ht1E.1]) ht1le
    have hτ : 0 < S.tau (T.β m (k'+1)) := S.τ_pos _ _
    nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hmb)]
  · push_neg at hE
    apply le_max_of_le_right
    have hpos : ∀ t, T.procStart m (k'+1) < t → t < T.s m (k'+1+1) →
        0 < T.x (T.β m (k'+1)) t := fun t h1 h2 =>
      lt_of_le_of_ne (T.x_nonneg _ t (by linarith)) (Ne.symm (hE t h1 h2))
    have hwk : T.s m (k'+1+1) - T.procStart m (k'+1) ≤ S.tau (T.β m (k'+1)) *
        (T.y (T.β m (k'+1)) (T.s m (k'+1+1)) - T.y (T.β m (k'+1)) (T.procStart m (k'+1))) := by
      apply le_of_forall_pos_lt_add
      intro ε hε
      have := work_ge T m (k'+1) hkN (T.procStart m (k'+1)) le_rfl (by linarith) hpos (ε/4)
        (by linarith) hsetup
      linarith
    have hinc1 := hinc (T.s m (k'+1)) (T.s m (k'+1+1)) hs0 (by linarith)
    have hW1 := hW (T.s m (k'+1)) hs0 (by linarith)
    have hmb : T.y (T.β m (k'+1)) (T.s m (k'+1)) ≤ T.y (T.β m (k'+1)) (T.procStart m (k'+1)) :=
      y_mono' T _ hs0 hps
    have hτ : 0 < S.tau (T.β m (k'+1)) := S.τ_pos _ _
    nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hmb)]

lemma dicon_of_minimal (S : System P M) (m : Fin M) (hmin : S.IsMinimal m) (p : Fin P) (j : ℕ)
    (hj : j + 1 < S.n p) (hne : S.μ p ⟨j, by omega⟩ ≠ m) (heq : S.μ p ⟨j+1, hj⟩ = m) :
    S.Dicon (S.μ p ⟨j, by omega⟩) m := by
  have hr : S.Reach (S.μ p ⟨j, by omega⟩) m :=
    Relation.ReflTransGen.single ⟨hne, p, ⟨j, by omega⟩, hj, rfl, heq⟩
  exact ⟨hr, hmin _ hr⟩

end KSAux

theorem drift_core {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (T : Trajectory S) (hT : T.IsClearing) (m : Fin M) (hmin : S.IsMinimal m) (k : ℕ)
    (hk : 1 ≤ k) (hnext : T.HasNext m k) :
    T.V m (T.s m (k + 1)) ≤
      max 0 (T.V m (T.s m k) - (1 - S.rhoPrime m) * (T.s m (k + 1) - T.s m k)
        + S.deltaBar m) := by
  have := KSAux.drift_gen T hT m k hk hnext 0 le_rfl (fun t1 t2 h1 h12 => by
    have := KSAux.V_incr T m 0 le_rfl h1 h12 (fun p j hj hne heq hnd =>
      absurd (KSAux.dicon_of_minimal S m hmin p j hj hne heq) hnd)
    simpa only [zero_mul, add_zero] using this) (h14 m)
  simpa only [add_zero] using this

end KumarSeidman.CAF

namespace KumarSeidman.CAF
namespace KSAux

variable {P M : ℕ}

lemma inflow_mono {S : System P M} (T : Trajectory S) (b : Buffer S) {t1 t2 : ℝ} (h1 : 0 ≤ t1)
    (h12 : t1 ≤ t2) : inflow S T.y b t1 ≤ inflow S T.y b t2 := by
  unfold inflow
  cases h : S.prev b with
  | none => simp only; exact mul_le_mul_of_nonneg_left h12 (S.d_pos _).le
  | some b' => simp only; exact y_mono' T b' h1 h12

lemma workAhead_ge (S : System P M) (b : Buffer S) : S.tau b ≤ S.workAhead b := by
  unfold System.workAhead
  have hmem : b.2 ∈ Finset.univ.filter (fun k : Fin (S.n b.1) =>
      b.2 ≤ k ∧ ∀ l : Fin (S.n b.1), b.2 ≤ l → l ≤ k → S.μ b.1 l = S.mach b) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨le_rfl, fun l h1 h2 => ?_⟩
    have : l = b.2 := le_antisymm h2 h1
    rw [this]; rfl
  exact Finset.single_le_sum (f := fun k => S.τ b.1 k) (fun k _ => (S.τ_pos _ _).le) hmem

lemma V_le_tauBar {S : System P M} (T : Trajectory S) (m : Fin M) (hB : (S.B m).Nonempty)
    (t : ℝ) (ht : 0 ≤ t) : T.V m t ≤ S.tauBar m hB * ∑ c ∈ S.B m, T.x c t := by
  unfold Trajectory.V
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  have h1 : S.workAhead c ≤ S.tauBar m hB := Finset.le_sup' S.workAhead hc
  have h2 := T.x_nonneg c t ht
  nlinarith

end KSAux

theorem gamma_core {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (ε K : Fin M → ℝ) (T : Trajectory S) (hT : T.IsCAF ε K) (m : Fin M)
    (hmin : S.IsMinimal m) (hB : (S.B m).Nonempty) (k : ℕ) (hk : 1 ≤ k)
    (hnext : T.HasNext m k) (hV : S.Gamma m hB ε K ≤ T.V m (T.s m k)) :
    T.V m (T.s m (k + 1)) ≤ T.V m (T.s m k) - S.deltaBar m := by
  obtain ⟨hcl, hε, hcaf⟩ := hT
  have hd := drift_core S h14 T hcl m hmin k hk hnext
  have hkN : (k : ℕ∞) < T.N m := lt_trans (by exact_mod_cast Nat.lt_succ_self _) hnext
  have hs0 := KSAux.s_nonneg T m k hkN
  have hsk : T.s m k ≤ T.s m (k+1) := by
    have h := T.setup_not_cut m k hnext
    have hr : 0 ≤ runSetup S (T.β m) k := by
      cases k with
      | zero => simp [runSetup]
      | succ i => exact S.δ_nonneg _ _
    linarith
  have hbB : T.β m k ∈ S.B m := Finset.mem_filter.mpr ⟨Finset.mem_univ _, T.β_mem m k hkN⟩
  have hcafk := hcaf m k hk hkN
  have hclear := ((hcl m k hkN).2 hnext).1
  have hbal1 := T.balance (T.β m k) (T.s m (k+1)) (by linarith)
  have hbal0 := T.balance (T.β m k) (T.s m k) hs0
  have hinfl := KSAux.inflow_mono T (T.β m k) hs0 hsk
  have hrate := KSAux.y_rate T (T.β m k) hs0 hsk
  have hτb : 0 < S.tau (T.β m k) := S.τ_pos _ _
  have hwork : S.tau (T.β m k) * T.x (T.β m k) (T.s m k) ≤ T.s m (k+1) - T.s m k := by
    have h1 : T.x (T.β m k) (T.s m k) ≤ T.y (T.β m k) (T.s m (k+1)) - T.y (T.β m k) (T.s m k) := by
      linarith
    have h2 : S.tau (T.β m k) * (T.y (T.β m k) (T.s m (k+1)) - T.y (T.β m k) (T.s m k))
        ≤ T.s m (k+1) - T.s m k := by
      have := mul_le_mul_of_nonneg_left hrate hτb.le
      rwa [mul_div_cancel₀ _ hτb.ne'] at this
    nlinarith
  have hlow : S.tauLow m hB ≤ S.tau (T.β m k) := Finset.inf'_le S.tau hbB
  have hlowpos : 0 < S.tauLow m hB := (Finset.lt_inf'_iff hB).mpr (fun c _ => S.τ_pos _ _)
  obtain ⟨c0, hc0⟩ := hB
  have hbarpos : 0 < S.tauBar m ⟨c0, hc0⟩ :=
    lt_of_lt_of_le (lt_of_lt_of_le (S.τ_pos _ _) (KSAux.workAhead_ge S c0))
      (Finset.le_sup' S.workAhead hc0)
  have hVle := KSAux.V_le_tauBar T m ⟨c0, hc0⟩ (T.s m k) hs0
  have hxb0 := T.x_nonneg (T.β m k) (T.s m k) hs0
  have hρ : 0 < 1 - S.rhoPrime m := by linarith [h14 m]
  have hεm := hε m
  have hG1 := le_trans (le_max_left _ _) hV
  have hG2 := le_trans (le_max_right _ _) hV
  set tb := S.tauBar m ⟨c0, hc0⟩
  set tl := S.tauLow m ⟨c0, hc0⟩
  set X := ∑ b ∈ S.B m, T.x b (T.s m k)
  set A := T.x (T.β m k) (T.s m k)
  set δb := S.deltaBar m
  set ρ := S.rhoPrime m
  set Q := 2 * δb / (tl * (1 - ρ))
  have hQ : Q * (tl * (1 - ρ)) = 2 * δb := by
    simp only [Q]; field_simp
  have hG1' : tb / ε m * (Q + K m) ≤ T.V m (T.s m k) := by
    have : tb / ε m * (Q + K m) = 2 * δb * tb / (ε m * tl * (1 - ρ)) + K m * tb / ε m := by
      simp only [Q]; field_simp
    rw [this]; exact hG1
  have h3 : tb / ε m * (Q + K m) ≤ tb * X := le_trans hG1' hVle
  have h4 : Q + K m ≤ ε m * X := by
    have h5 : (Q + K m) / ε m ≤ X := by
      have : tb * ((Q + K m) / ε m) ≤ tb * X := by
        rw [show tb * ((Q + K m) / ε m) = tb / ε m * (Q + K m) by ring]; exact h3
      exact le_of_mul_le_mul_left this hbarpos
    rwa [div_le_iff₀ hεm, mul_comm] at h5
  have h6 : Q ≤ A := by linarith
  have h7 : 2 * δb ≤ (1 - ρ) * (T.s m (k+1) - T.s m k) := by
    rw [← hQ]
    have : Q * tl ≤ A * S.tau (T.β m k) := by
      have hQ0 : 0 ≤ Q := div_nonneg (by have := KSAux.deltaBar_nonneg S m; linarith) (mul_pos hlowpos hρ).le
      nlinarith
    nlinarith
  calc T.V m (T.s m (k+1)) ≤ max 0 (T.V m (T.s m k) - (1 - ρ) * (T.s m (k + 1) - T.s m k) + δb) := hd
    _ ≤ T.V m (T.s m k) - δb := max_le (by linarith) (by linarith)

end KumarSeidman.CAF

namespace KumarSeidman.CAF
namespace KSAux

variable {P M : ℕ}

lemma sum_wa_eq (S : System P M) (m : Fin M) (f : Buffer S → ℝ) :
    ∑ b ∈ S.B m, f b * S.workAhead b =
      ∑ c ∈ S.B m, S.tau c * ∑ i ∈ Finset.univ.filter (fun i => blk S m c.1 i c.2), f ⟨c.1, i⟩ := by
  classical
  unfold System.workAhead System.B
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have L : ∀ i : Fin (S.n p), (if S.mach ⟨p, i⟩ = m then f ⟨p, i⟩ *
      ∑ k ∈ Finset.univ.filter (fun k : Fin (S.n p) => i ≤ k ∧
        ∀ l : Fin (S.n p), i ≤ l → l ≤ k → S.μ p l = S.mach ⟨p, i⟩), S.τ p k else 0) =
      ∑ k : Fin (S.n p), if blk S m p i k then f ⟨p, i⟩ * S.τ p k else 0 := by
    intro i
    split_ifs with hi
    · rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [blk, hi]
    · symm
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [if_neg]
      rintro ⟨hik, hl⟩
      exact hi (hl i le_rfl hik)
  have R : ∀ k : Fin (S.n p), (if S.mach ⟨p, k⟩ = m then S.tau ⟨p, k⟩ *
      ∑ i ∈ Finset.univ.filter (fun i => blk S m p i k), f ⟨p, i⟩ else 0) =
      ∑ i : Fin (S.n p), if blk S m p i k then f ⟨p, i⟩ * S.τ p k else 0 := by
    intro k
    split_ifs with hk
    · rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs <;> simp [System.tau, mul_comm]
    · symm
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [if_neg]
      rintro ⟨hik, hl⟩
      exact hk (hl k hik le_rfl)
  simp only [L, R]
  exact Finset.sum_comm

lemma exists_head (S : System P M) (m : Fin M) (p : Fin P) (k : Fin (S.n p))
    (hk : S.μ p k = m) : ∃ i, blk S m p i k ∧ S.IsHead ⟨p, i⟩ := by
  classical
  have hex : ∃ n, ∃ h : n < S.n p, blk S m p ⟨n, h⟩ k :=
    ⟨k.val, k.isLt, le_rfl, fun l h1 h2 => by rw [le_antisymm h2 h1]; exact hk⟩
  obtain ⟨h0, hb0⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, h0⟩, hb0, ?_⟩
  intro b' hb'
  unfold System.prev at hb'
  split_ifs at hb' with hpos
  simp only [Option.some.injEq] at hb'
  subst hb'
  intro heq
  have hμ0 : S.μ p ⟨Nat.find hex, h0⟩ = m := hb0.2 _ le_rfl hb0.1
  have hm1 : S.μ p ⟨Nat.find hex - 1, by omega⟩ = m := by
    have : S.mach ⟨p, ⟨Nat.find hex - 1, by simp only at hpos; omega⟩⟩ =
      S.mach ⟨p, ⟨Nat.find hex, h0⟩⟩ := heq
    simp only [System.mach] at this
    rw [this, hμ0]
  have hb1 : blk S m p ⟨Nat.find hex - 1, by omega⟩ k := by
    refine ⟨le_trans (Fin.le_def.mpr (by simp)) hb0.1, fun l hl1 hl2 => ?_⟩
    by_cases hl : l.val = Nat.find hex - 1
    · rw [show l = ⟨Nat.find hex - 1, by omega⟩ from Fin.ext hl]; exact hm1
    · exact hb0.2 l (Fin.le_def.mpr (show Nat.find hex ≤ l.val by
        have h2 : Nat.find hex - 1 ≤ l.val := Fin.le_def.mp hl1
        omega)) hl2
  have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by simp only at hpos; omega)
  exact this ⟨_, hb1⟩

lemma GammaBar_ge (S : System P M) (m : Fin M) (Γ : ℝ) (hΓ : 0 ≤ Γ) :
    Γ * ∑ c ∈ S.B m, S.tau c ≤ S.GammaBar m Γ := by
  classical
  unfold System.GammaBar
  rw [Finset.sum_filter]
  have key := sum_wa_eq S m (fun b => if S.IsHead b then Γ else 0)
  have e1 : (∑ b ∈ S.B m, if S.IsHead b then Γ * S.workAhead b else 0) =
      ∑ b ∈ S.B m, (if S.IsHead b then Γ else 0) * S.workAhead b :=
    Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
  rw [e1, key, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  have hcm : S.mach c = m := (Finset.mem_filter.mp hc).2
  obtain ⟨p, k⟩ := c
  obtain ⟨i, hblk, hhead⟩ := exists_head S m p k hcm
  have hmem : i ∈ Finset.univ.filter (fun i => blk S m p i k) := by simp [hblk]
  have : Γ ≤ ∑ i' ∈ Finset.univ.filter (fun i => blk S m p i k),
      (if S.IsHead ⟨p, i'⟩ then Γ else 0) := by
    calc Γ = (if S.IsHead ⟨p, i⟩ then Γ else 0) := (if_pos hhead).symm
      _ ≤ _ := Finset.single_le_sum (f := fun i' => if S.IsHead ⟨p, i'⟩ then Γ else 0)
          (fun j _ => by split_ifs <;> linarith) hmem
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left this (S.τ_pos _ _).le

lemma prefix_tel {S : System P M} (T : Trajectory S) (p : Fin P) (t : ℝ) (ht : 0 ≤ t) :
    ∀ (j : ℕ) (hj : j < S.n p),
      ∑ i ∈ Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j), T.x ⟨p, i⟩ t =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j), T.x ⟨p, i⟩ 0
          + S.d p * t - T.y ⟨p, ⟨j, hj⟩⟩ t := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hf : Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ 0) = {⟨0, hj⟩} := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact Fin.ext (by simp; omega)
      · rintro rfl; simp
    have hprev : S.prev ⟨p, ⟨0, hj⟩⟩ = none := by simp [System.prev]
    rw [hf, Finset.sum_singleton, Finset.sum_singleton, T.balance _ t ht]
    simp only [inflow, hprev]
  | succ j ih =>
    intro hj
    have hf : Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j + 1) =
        insert ⟨j+1, hj⟩ (Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases hi : i.val = j + 1
        · left; exact Fin.ext hi
        · right; omega
      · rintro (rfl | h)
        · simp
        · omega
    have hnot : (⟨j+1, hj⟩ : Fin (S.n p)) ∉
        Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j) := by simp
    have hprev : S.prev ⟨p, ⟨j+1, hj⟩⟩ = some ⟨p, ⟨j, by omega⟩⟩ := by simp [System.prev]
    rw [hf, Finset.sum_insert hnot, Finset.sum_insert hnot, T.balance _ t ht, ih (by omega)]
    simp only [inflow, hprev]
    ring

lemma H_ind {S : System P M} (T : Trajectory S) (U : Finset (Fin M)) (hU : S.UpstreamClosed U)
    (Γ : ℝ) (hΓ : ∀ t : ℝ, 0 ≤ t →
      ∑ b ∈ Finset.univ.filter (fun b : Buffer S => S.mach b ∈ U), T.x b t ≤ Γ)
    (m : Fin M) (hmin : ∀ m' : Fin M, m' ∉ U → S.Reach m' m → S.Reach m m')
    {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h12 : t1 ≤ t2) :
    ∀ (p : Fin P) (j : ℕ) (hj : j + 1 < S.n p), S.μ p ⟨j, by omega⟩ ≠ m →
       S.μ p ⟨j+1, hj⟩ = m → ¬ S.Dicon (S.μ p ⟨j, by omega⟩) m →
       T.y ⟨p, ⟨j, by omega⟩⟩ t2 - T.y ⟨p, ⟨j, by omega⟩⟩ t1 ≤ S.d p * (t2 - t1) + Γ := by
  classical
  intro p j hj hne heq hnd
  have hr : S.Reach (S.μ p ⟨j, by omega⟩) m :=
    Relation.ReflTransGen.single ⟨hne, p, ⟨j, by omega⟩, hj, rfl, heq⟩
  have hjU : S.μ p ⟨j, by omega⟩ ∈ U := by
    by_contra hc
    exact hnd ⟨hr, hmin _ hc hr⟩
  have hall : ∀ d : ℕ, ∀ i : ℕ, ∀ hi : i + d = j, S.μ p ⟨i, by omega⟩ ∈ U := by
    intro d
    induction d with
    | zero => intro i hi; subst hi; exact hjU
    | succ d ih =>
      intro i hi
      have h' := ih (i+1) (by omega)
      by_cases hs : S.μ p ⟨i, by omega⟩ = S.μ p ⟨i+1, by omega⟩
      · rw [hs]; exact h'
      · exact hU _ _ ⟨hs, p, ⟨i, by omega⟩, by simp only; omega, rfl, rfl⟩ h'
  have hsub : ∀ t, 0 ≤ t →
      ∑ i ∈ Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j), T.x ⟨p, i⟩ t ≤ Γ := by
    intro t ht
    refine le_trans ?_ (hΓ t ht)
    have hm : ∑ i ∈ Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j), T.x ⟨p, i⟩ t =
        ∑ b ∈ (Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j)).map
          (Function.Embedding.sigmaMk (β := fun p => Fin (S.n p)) p), T.x b t := by
      rw [Finset.sum_map]; rfl
    rw [hm]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      obtain ⟨i, hi, rfl⟩ := hb
      exact hall (j - i.val) i.val (by omega)
    · intro b _ _; exact T.x_nonneg b t ht
  have e1 := prefix_tel T p t1 h1 j (by omega)
  have e2 := prefix_tel T p t2 (by linarith) j (by omega)
  have hS2 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (S.n p) => i.val ≤ j), T.x ⟨p, i⟩ t2 :=
    Finset.sum_nonneg (fun i _ => T.x_nonneg _ t2 (by linarith))
  have hS1 := hsub t1 h1
  nlinarith

end KSAux

theorem ind_core {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (T : Trajectory S) (hT : T.IsClearing) (U : Finset (Fin M)) (hU : S.UpstreamClosed U)
    (Γ : ℝ) (hΓ : ∀ t : ℝ, 0 ≤ t →
      ∑ b ∈ Finset.univ.filter (fun b : Buffer S => S.mach b ∈ U), T.x b t ≤ Γ)
    (m : Fin M) (hmU : m ∉ U) (hmin : ∀ m' : Fin M, m' ∉ U → S.Reach m' m → S.Reach m m')
    (k : ℕ) (hk : 1 ≤ k) (hnext : T.HasNext m k) :
    T.V m (T.s m (k + 1)) ≤
      max (S.GammaBar m Γ) (T.V m (T.s m k) - (1 - S.rhoPrime m) * (T.s m (k + 1) - T.s m k)
        + S.deltaBar m + S.GammaBar m Γ) := by
  have hΓ0 : 0 ≤ Γ :=
    le_trans (Finset.sum_nonneg (fun b _ => T.x_nonneg b 0 le_rfl)) (hΓ 0 le_rfl)
  have hGB := KSAux.GammaBar_ge S m Γ hΓ0
  have hGB0 : 0 ≤ S.GammaBar m Γ :=
    le_trans (mul_nonneg hΓ0 (Finset.sum_nonneg (fun c _ => (S.τ_pos _ _).le))) hGB
  exact KSAux.drift_gen T hT m k hk hnext (S.GammaBar m Γ) hGB0 (fun t1 t2 h1 h12 => by
    have := KSAux.V_incr T m Γ hΓ0 h1 h12 (KSAux.H_ind T U hU Γ hΓ m hmin h1 h12)
    linarith) (h14 m)

end KumarSeidman.CAF

open KumarSeidman.CAF


theorem solution {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (T : Trajectory S) (hT : T.IsClearing) (U : Finset (Fin M)) (hU : S.UpstreamClosed U)
    (Γ : ℝ) (hΓ : ∀ t : ℝ, 0 ≤ t →
      ∑ b ∈ Finset.univ.filter (fun b : Buffer S => S.mach b ∈ U), T.x b t ≤ Γ)
    (m : Fin M) (hmU : m ∉ U) (hmin : ∀ m' : Fin M, m' ∉ U → S.Reach m' m → S.Reach m m')
    (k : ℕ) (hk : 1 ≤ k) (hnext : T.HasNext m k) :
    T.V m (T.s m (k + 1)) ≤
      max (S.GammaBar m Γ) (T.V m (T.s m k) - (1 - S.rhoPrime m) * (T.s m (k + 1) - T.s m k)
        + S.deltaBar m + S.GammaBar m Γ) := by
  exact ind_core S h14 T hT U hU Γ hΓ m hmU hmin k hk hnext
