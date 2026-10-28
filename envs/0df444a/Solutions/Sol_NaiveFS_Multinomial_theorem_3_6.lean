-- Prove2me | solution 1 for NaiveFS.Multinomial.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T17:44:45.478992+00:00
-- url     : https://prove2.me/submissions/2746f879-2e27-4998-ad68-889966fe0675

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model

set_option autoImplicit false

open Finset NaiveFS.Multinomial

lemma nfs_h_nonneg {m : ℕ} (fp fm : Fin m → ℝ) (i : Fin m) (hp : 0 < fp i) (hq : 0 < fm i)
    {α : ℝ} (ha : 0 < α) (ha1 : α < 1) : 0 ≤ h fp fm α i := by
  have hf : 0 < fp i + fm i := by linarith
  have hb : 0 < 1 - α := by linarith
  have e1 := Real.log_le_sub_one_of_pos (show 0 < α * (fp i + fm i) / fp i by positivity)
  have e2 := Real.log_le_sub_one_of_pos (show 0 < (1 - α) * (fp i + fm i) / fm i by positivity)
  rw [Real.log_div (by positivity) hp.ne', Real.log_mul ha.ne' hf.ne'] at e1
  rw [Real.log_div (by positivity) hq.ne', Real.log_mul hb.ne' hf.ne'] at e2
  have k1 := mul_le_mul_of_nonneg_left e1 hp.le
  have k2 := mul_le_mul_of_nonneg_left e2 hq.le
  have q1 : fp i * (α * (fp i + fm i) / fp i - 1) = α * (fp i + fm i) - fp i := by
    field_simp
  have q2 : fm i * ((1 - α) * (fp i + fm i) / fm i - 1) = (1 - α) * (fp i + fm i) - fm i := by
    field_simp
  simp only [h, Ctil]
  nlinarith

lemma nfs_h_tangent {m : ℕ} (fp fm : Fin m → ℝ) (i : Fin m) (hp : 0 < fp i) (hq : 0 < fm i)
    {α β : ℝ} (ha : 0 < α) (ha1 : α < 1) (hb : 0 < β) (hb1 : β < 1) :
    h fp fm α i + (β - α) * (fm i / (1 - α) - fp i / α) ≤ h fp fm β i := by
  have hα' : 0 < 1 - α := by linarith
  have hβ' : 0 < 1 - β := by linarith
  have e1 := Real.log_le_sub_one_of_pos (show 0 < β / α by positivity)
  have e2 := Real.log_le_sub_one_of_pos (show 0 < (1 - β) / (1 - α) by positivity)
  rw [Real.log_div hb.ne' ha.ne'] at e1
  rw [Real.log_div hβ'.ne' hα'.ne'] at e2
  have k1 := mul_le_mul_of_nonneg_left e1 hp.le
  have k2 := mul_le_mul_of_nonneg_left e2 hq.le
  have q1 : fp i * (β / α - 1) = (β - α) * (fp i / α) := by field_simp
  have q2 : fm i * ((1 - β) / (1 - α) - 1) = - ((β - α) * (fm i / (1 - α))) := by
    field_simp; ring
  simp only [h]
  nlinarith

lemma nfs_topSum_eq {n : ℕ} (j : ℕ) (hj : j ≤ n) (c : Fin n → ℝ)
    (hne : (univ.powersetCard j : Finset (Finset (Fin n))).Nonempty) :
    topSum j c = (univ.powersetCard j).sup' hne (fun T => ∑ i ∈ T, c i) := by
  have hmin : min j n = j := min_eq_left hj
  unfold topSum
  rw [hmin]
  apply le_antisymm
  · apply csSup_le
    · obtain ⟨T, hT⟩ := hne
      exact ⟨_, T, (mem_powersetCard.mp hT).2, rfl⟩
    · rintro v ⟨T, hT, rfl⟩
      exact le_sup' (fun T => ∑ i ∈ T, c i) (mem_powersetCard.mpr ⟨subset_univ _, hT⟩)
  · apply sup'_le
    intro T hT
    have hbdd : BddAbove {v | ∃ T : Finset (Fin n), T.card = j ∧ v = ∑ i ∈ T, c i} := by
      apply (Set.finite_range (fun T : Finset (Fin n) => ∑ i ∈ T, c i)).bddAbove.mono
      rintro v ⟨T, _, rfl⟩
      exact ⟨T, rfl⟩
    exact le_csSup hbdd ⟨T, (mem_powersetCard.mp hT).2, rfl⟩

lemma nfs_pc_nonempty {n : ℕ} (j : ℕ) (hj : j ≤ n) :
    (univ.powersetCard j : Finset (Finset (Fin n))).Nonempty := by
  apply powersetCard_nonempty.mpr
  simpa using hj

lemma nfs_phi_bdd {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) :
    BddAbove {v | ∃ θp θm : Fin m → ℝ, Feasible k θp θm ∧ v = objective fp fm θp θm} := by
  refine ⟨0, ?_⟩
  rintro v ⟨θp, θm, hF, rfl⟩
  unfold objective
  apply sum_nonpos
  intro i _
  have a1 := Real.log_nonpos (hF.1 i).1.le (hF.1 i).2
  have a2 := Real.log_nonpos (hF.2.1 i).1.le (hF.2.1 i).2
  have b1 := mul_nonpos_of_nonneg_of_nonpos (hfp i).le a1
  have b2 := mul_nonpos_of_nonneg_of_nonpos (hfm i).le a2
  linarith

/-- weak duality: every feasible point is below `C + s_k(h(α))`. -/
lemma nfs_weak {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hkm : k ≤ m) (θp θm : Fin m → ℝ) (hF : Feasible k θp θm)
    {α : ℝ} (ha : 0 < α) (ha1 : α < 1) :
    objective fp fm θp θm ≤ C fp fm + topSum k (h fp fm α) := by
  set D := univ.filter (fun i => θp i ≠ θm i) with hD
  have hS : 0 < S fp fm := by
    unfold S
    have : 0 < m := by
      by_contra h0
      have : m = 0 := by omega
      subst this
      have := hF.2.2.1
      simp at this
    exact sum_pos (fun i _ => by linarith [hfp i, hfm i]) ⟨⟨0, this⟩, mem_univ _⟩
  have hb : 0 < 1 - α := by linarith
  have per : ∀ i, fp i * Real.log (θp i) + fm i * Real.log (θm i) ≤
      S fp fm * (α * θp i + (1 - α) * θm i) - (fp i + fm i)
        - (fp i + fm i) * Real.log (S fp fm) + (fp i + fm i) * Real.log (fp i + fm i)
        + (if i ∈ D then h fp fm α i else 0) := by
    intro i
    have hp := hfp i
    have hq := hfm i
    have t1 := (hF.1 i).1
    have t2 := (hF.2.1 i).1
    by_cases hi : i ∈ D
    · rw [if_pos hi]
      have e1 := Real.log_le_sub_one_of_pos
        (show 0 < α * S fp fm * θp i / fp i by positivity)
      have e2 := Real.log_le_sub_one_of_pos
        (show 0 < (1 - α) * S fp fm * θm i / fm i by positivity)
      rw [Real.log_div (by positivity) hp.ne', Real.log_mul (by positivity) t1.ne',
        Real.log_mul ha.ne' hS.ne'] at e1
      rw [Real.log_div (by positivity) hq.ne', Real.log_mul (by positivity) t2.ne',
        Real.log_mul hb.ne' hS.ne'] at e2
      have k1 := mul_le_mul_of_nonneg_left e1 hp.le
      have k2 := mul_le_mul_of_nonneg_left e2 hq.le
      have q1 : fp i * (α * S fp fm * θp i / fp i - 1) = α * S fp fm * θp i - fp i := by
        field_simp
      have q2 : fm i * ((1 - α) * S fp fm * θm i / fm i - 1)
          = (1 - α) * S fp fm * θm i - fm i := by
        field_simp
      simp only [h, Ctil]
      nlinarith
    · rw [if_neg hi]
      have heq : θp i = θm i := by
        by_contra hne
        exact hi (by rw [hD, mem_filter]; exact ⟨mem_univ _, hne⟩)
      rw [← heq]
      have hf : 0 < fp i + fm i := by linarith
      have e1 := Real.log_le_sub_one_of_pos
        (show 0 < S fp fm * θp i / (fp i + fm i) by positivity)
      rw [Real.log_div (by positivity) hf.ne', Real.log_mul hS.ne' t1.ne'] at e1
      have k1 := mul_le_mul_of_nonneg_left e1 hf.le
      have q1 : (fp i + fm i) * (S fp fm * θp i / (fp i + fm i) - 1)
          = S fp fm * θp i - (fp i + fm i) := by
        field_simp
      nlinarith
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin m))) => per i)
  have hD' : D.card ≤ k := hF.2.2.2.2
  obtain ⟨D', hDD', -, hD'c⟩ := exists_subsuperset_card_eq (subset_univ D) hD'
    (by simpa using hkm)
  have hmono : ∑ i ∈ D, h fp fm α i ≤ ∑ i ∈ D', h fp fm α i :=
    sum_le_sum_of_subset_of_nonneg hDD'
      (fun i _ _ => nfs_h_nonneg fp fm i (hfp i) (hfm i) ha ha1)
  have htop : ∑ i ∈ D', h fp fm α i ≤ topSum k (h fp fm α) := by
    rw [nfs_topSum_eq k hkm _ (nfs_pc_nonempty k hkm)]
    exact le_sup' (fun T => ∑ i ∈ T, h fp fm α i)
      (mem_powersetCard.mpr ⟨subset_univ _, hD'c⟩)
  have hR : ∑ i, (S fp fm * (α * θp i + (1 - α) * θm i) - (fp i + fm i)
        - (fp i + fm i) * Real.log (S fp fm) + (fp i + fm i) * Real.log (fp i + fm i)
        + (if i ∈ D then h fp fm α i else 0))
      = C fp fm + ∑ i ∈ D, h fp fm α i := by
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_ite_mem, univ_inter,
      ← sum_mul]
    rw [hF.2.2.1, hF.2.2.2.1]
    unfold C S
    simp only [sum_add_distrib]
    ring
  unfold objective
  linarith

/-- the explicit point attached to a support set `T`: its value is `C + Σ_T h(p_T)`. -/
lemma nfs_construct {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (T : Finset (Fin m)) (hT : T.Nonempty) (hTk : T.card ≤ k) :
    C fp fm + ∑ i ∈ T, h fp fm ((∑ i ∈ T, fp i) / (∑ i ∈ T, fp i + ∑ i ∈ T, fm i)) i
      ≤ phi fp fm k := by
  obtain ⟨a, ha⟩ : ∃ a, a = ∑ i ∈ T, fp i := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ∑ i ∈ T, fm i := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have ha0 : 0 < a := ha ▸ sum_pos (fun i _ => hfp i) hT
  have hb0 : 0 < b := hb ▸ sum_pos (fun i _ => hfm i) hT
  have hS : 0 < S fp fm := by
    unfold S
    obtain ⟨i0, -⟩ := hT
    exact sum_pos (fun i _ => by linarith [hfp i, hfm i]) ⟨i0, mem_univ _⟩
  have hSdef : ∑ i, fp i + ∑ i, fm i = S fp fm := by unfold S; rw [sum_add_distrib]
  set Sv := S fp fm with hSv
  let θp : Fin m → ℝ := fun i => if i ∈ T then fp i * (a + b) / (Sv * a) else (fp i + fm i) / Sv
  let θm : Fin m → ℝ := fun i => if i ∈ T then fm i * (a + b) / (Sv * b) else (fp i + fm i) / Sv
  have pos_p : ∀ i, 0 < θp i := by
    intro i; have := hfp i; have := hfm i; simp only [θp]; split_ifs <;> positivity
  have pos_m : ∀ i, 0 < θm i := by
    intro i; have := hfp i; have := hfm i; simp only [θm]; split_ifs <;> positivity
  have sum_p : ∑ i, θp i = 1 := by
    have e : ∀ i, θp i = (fp i + fm i) / Sv +
        (if i ∈ T then fp i * (a + b) / (Sv * a) - (fp i + fm i) / Sv else 0) := by
      intro i; simp only [θp]; split_ifs <;> ring
    rw [sum_congr rfl (fun i _ => e i), sum_add_distrib, sum_ite_mem, univ_inter,
      sum_sub_distrib, ← sum_div, ← sum_div, ← sum_div, ← sum_mul, sum_add_distrib,
      sum_add_distrib, ← ha, ← hb, hSdef]
    field_simp
    ring
  have sum_m : ∑ i, θm i = 1 := by
    have e : ∀ i, θm i = (fp i + fm i) / Sv +
        (if i ∈ T then fm i * (a + b) / (Sv * b) - (fp i + fm i) / Sv else 0) := by
      intro i; simp only [θm]; split_ifs <;> ring
    rw [sum_congr rfl (fun i _ => e i), sum_add_distrib, sum_ite_mem, univ_inter,
      sum_sub_distrib, ← sum_div, ← sum_div, ← sum_div, ← sum_mul, sum_add_distrib,
      sum_add_distrib, ← ha, ← hb, hSdef]
    field_simp
    ring
  have feas : Feasible k θp θm := by
    refine ⟨fun i => ⟨pos_p i, ?_⟩, fun i => ⟨pos_m i, ?_⟩, sum_p, sum_m, ?_⟩
    · rw [← sum_p]
      exact single_le_sum (fun j _ => (pos_p j).le) (mem_univ i)
    · rw [← sum_m]
      exact single_le_sum (fun j _ => (pos_m j).le) (mem_univ i)
    · refine le_trans (card_le_card ?_) hTk
      intro i hi
      rw [mem_filter] at hi
      by_contra hiT
      apply hi.2
      simp only [θp, θm, if_neg hiT]
  have per : ∀ i, fp i * Real.log (θp i) + fm i * Real.log (θm i) =
      (fp i + fm i) * Real.log (fp i + fm i) - (fp i + fm i) * Real.log Sv
        + (if i ∈ T then h fp fm (a / (a + b)) i else 0) := by
    intro i
    have hp := hfp i
    have hq := hfm i
    by_cases hi : i ∈ T
    · simp only [θp, θm, if_pos hi, h, Ctil]
      have e1 : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
      rw [e1, Real.log_div (by positivity) (by positivity), Real.log_div (by positivity)
        (by positivity), Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity)]
      ring
    · simp only [θp, θm, if_neg hi]
      rw [Real.log_div (by positivity) (by positivity)]
      ring
  have hobj : objective fp fm θp θm = C fp fm + ∑ i ∈ T, h fp fm (a / (a + b)) i := by
    unfold objective
    rw [sum_congr rfl (fun i _ => per i)]
    simp only [sum_add_distrib, sum_sub_distrib, sum_ite_mem, univ_inter, ← sum_mul]
    unfold C
    rw [← hSv]
    unfold S at hSv
    rw [hSv]
    simp only [sum_add_distrib]
  rw [← hobj]
  exact le_csSup (nfs_phi_bdd fp fm hfp hfm k) ⟨θp, θm, feas, rfl⟩

lemma nfs_middle {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hkm : k < m) : phi fp fm k ≤ psi fp fm k := by
  unfold phi psi
  have hm : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  apply csSup_le
  · refine ⟨_, fun _ => 1 / (m : ℝ), fun _ => 1 / (m : ℝ), ?_, rfl⟩
    have h1 : 1 / (m : ℝ) ≤ 1 := by
      rw [div_le_one hm]; exact_mod_cast (by omega : 1 ≤ m)
    have hs : ∑ _i : Fin m, 1 / (m : ℝ) = 1 := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    refine ⟨fun i => ⟨by positivity, h1⟩, fun i => ⟨by positivity, h1⟩, hs, hs, ?_⟩
    simp
  · rintro v ⟨θp, θm, hF, rfl⟩
    have : objective fp fm θp θm - C fp fm ≤
        sInf ((fun α => topSum k (h fp fm α)) '' Set.Ioo (0 : ℝ) 1) := by
      apply le_csInf ((Set.nonempty_Ioo.mpr zero_lt_one).image _)
      rintro y ⟨α, hα, rfl⟩
      have := nfs_weak fp fm hfp hfm k hkm.le θp θm hF hα.1 hα.2
      linarith
    linarith

lemma nfs_pT_mem {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (T : Finset (Fin m)) (hT : T.Nonempty) :
    (∑ i ∈ T, fp i) / (∑ i ∈ T, fp i + ∑ i ∈ T, fm i) ∈ Set.Ioo (0 : ℝ) 1 := by
  have ha := sum_pos (fun i _ => hfp i) hT
  have hb := sum_pos (fun i _ => hfm i) hT
  exact ⟨div_pos ha (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

lemma nfs_G_tangent {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (S : Finset (Fin m)) {α β : ℝ} (ha : 0 < α) (ha1 : α < 1) (hb : 0 < β) (hb1 : β < 1) :
    ∑ i ∈ S, h fp fm α i + (β - α) * ∑ i ∈ S, (fm i / (1 - α) - fp i / α)
      ≤ ∑ i ∈ S, h fp fm β i := by
  rw [mul_sum, ← sum_add_distrib]
  exact sum_le_sum (fun i _ => nfs_h_tangent fp fm i (hfp i) (hfm i) ha ha1 hb hb1)

lemma nfs_h_contOn {m : ℕ} (fp fm : Fin m → ℝ) (i : Fin m) :
    ContinuousOn (fun α => h fp fm α i) (Set.Ioo (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fun α : ℝ => Real.log α) (Set.Ioo (0 : ℝ) 1) :=
    Real.continuousOn_log.mono (fun x hx => hx.1.ne')
  have h2 : ContinuousOn (fun α : ℝ => Real.log (1 - α)) (Set.Ioo (0 : ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).log
      (fun x hx => sub_ne_zero.mpr (ne_of_gt hx.2))
  simp only [h]
  exact (continuousOn_const.sub (continuousOn_const.mul h1)).sub (continuousOn_const.mul h2)

lemma nfs_G_contOn {m : ℕ} (fp fm : Fin m → ℝ) (S : Finset (Fin m)) :
    ContinuousOn (fun α => ∑ i ∈ S, h fp fm α i) (Set.Ioo (0 : ℝ) 1) :=
  continuousOn_finsetSum S (fun i _ => nfs_h_contOn fp fm i)

lemma nfs_D_contOn {m : ℕ} (fp fm : Fin m → ℝ) (S : Finset (Fin m)) :
    ContinuousOn (fun α => ∑ i ∈ S, (fm i / (1 - α) - fp i / α)) (Set.Ioo (0 : ℝ) 1) :=
  continuousOn_finsetSum S (fun i _ =>
    (continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun x hx => sub_ne_zero.mpr (ne_of_gt hx.2))).sub
    (continuousOn_const.div continuousOn_id (fun x hx => hx.1.ne')))

lemma nfs_g_le {m : ℕ} (fp fm : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) (α : ℝ)
    (U : Finset (Fin m)) (hU : U.card = j) :
    ∑ i ∈ U, h fp fm α i ≤ topSum j (h fp fm α) := by
  rw [nfs_topSum_eq j hj _ (nfs_pc_nonempty j hj)]
  exact le_sup' (fun T => ∑ i ∈ T, h fp fm α i) (mem_powersetCard.mpr ⟨subset_univ _, hU⟩)

lemma nfs_g_att {m : ℕ} (fp fm : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) (α : ℝ) :
    ∃ U : Finset (Fin m), U.card = j ∧ ∑ i ∈ U, h fp fm α i = topSum j (h fp fm α) := by
  rw [nfs_topSum_eq j hj _ (nfs_pc_nonempty j hj)]
  obtain ⟨U, hU, he⟩ := exists_mem_eq_sup' (nfs_pc_nonempty j hj)
    (fun T => ∑ i ∈ T, h fp fm α i)
  exact ⟨U, (mem_powersetCard.mp hU).2, he.symm⟩

lemma nfs_g_contOn {m : ℕ} (fp fm : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) :
    ContinuousOn (fun α => topSum j (h fp fm α)) (Set.Ioo (0 : ℝ) 1) := by
  have e : (fun α => topSum j (h fp fm α)) = fun α =>
      (univ.powersetCard j).sup' (nfs_pc_nonempty j hj) (fun S => ∑ i ∈ S, h fp fm α i) :=
    funext fun α => nfs_topSum_eq j hj _ (nfs_pc_nonempty j hj)
  rw [e]
  exact ContinuousOn.finset_sup'_apply (f := fun S α => ∑ i ∈ S, h fp fm α i)
    (nfs_pc_nonempty j hj) (fun S _ => nfs_G_contOn fp fm S)

lemma nfs_no_descent {m : ℕ} (fp fm : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) (α0 : ℝ)
    (hmin : ∀ α ∈ Set.Ioo (0 : ℝ) 1, topSum j (h fp fm α0) ≤ topSum j (h fp fm α))
    (l : Filter ℝ) [l.NeBot] (hl : ∀ᶠ α in l, α ∈ Set.Ioo (0 : ℝ) 1)
    (hS : ∀ S : Finset (Fin m), S.card = j →
      ∀ᶠ α in l, ∑ i ∈ S, h fp fm α i < topSum j (h fp fm α0)) : False := by
  have hall : ∀ᶠ α in l, ∀ S ∈ univ.powersetCard j,
      ∑ i ∈ S, h fp fm α i < topSum j (h fp fm α0) := by
    rw [Filter.eventually_all_finset]
    intro S hS'
    exact hS S (mem_powersetCard.mp hS').2
  obtain ⟨α, hα1, hα2⟩ := (hl.and hall).exists
  obtain ⟨U, hUc, hUe⟩ := nfs_g_att fp fm j hj α
  have := hα2 U (mem_powersetCard.mpr ⟨subset_univ _, hUc⟩)
  have := hmin α hα1
  linarith

lemma nfs_active_left {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (j : ℕ) (hj : j ≤ m) (α0 : ℝ) (hα0 : α0 ∈ Set.Ioo (0 : ℝ) 1)
    (hmin : ∀ α ∈ Set.Ioo (0 : ℝ) 1, topSum j (h fp fm α0) ≤ topSum j (h fp fm α)) :
    ∃ S : Finset (Fin m), S.card = j ∧ ∑ i ∈ S, h fp fm α0 i = topSum j (h fp fm α0) ∧
      ∑ i ∈ S, (fm i / (1 - α0) - fp i / α0) ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  apply nfs_no_descent fp fm j hj α0 hmin (nhdsWithin α0 (Set.Iio α0))
  · filter_upwards [Ioo_mem_nhdsLT hα0.1] with α hα using ⟨hα.1, hα.2.trans hα0.2⟩
  · intro S hSc
    rcases lt_or_eq_of_le (nfs_g_le fp fm j hj α0 S hSc) with hlt | heq
    · have hc := (nfs_G_contOn fp fm S).continuousAt (Ioo_mem_nhds hα0.1 hα0.2)
      exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds hlt))
    · have hD := hcon S hSc heq
      have hc := (nfs_D_contOn fp fm S).continuousAt (Ioo_mem_nhds hα0.1 hα0.2)
      have ev1 : ∀ᶠ α in nhdsWithin α0 (Set.Iio α0),
          0 < ∑ i ∈ S, (fm i / (1 - α) - fp i / α) :=
        nhdsWithin_le_nhds (hc.eventually (lt_mem_nhds hD))
      filter_upwards [ev1, Ioo_mem_nhdsLT hα0.1] with α h1 h2
      have t := nfs_G_tangent fp fm hfp hfm S (α := α) (β := α0) h2.1 (h2.2.trans hα0.2)
        hα0.1 hα0.2
      have : 0 < (α0 - α) * ∑ i ∈ S, (fm i / (1 - α) - fp i / α) :=
        mul_pos (by linarith [h2.2]) h1
      rw [← heq]; linarith

lemma nfs_active_right {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (j : ℕ) (hj : j ≤ m) (α0 : ℝ) (hα0 : α0 ∈ Set.Ioo (0 : ℝ) 1)
    (hmin : ∀ α ∈ Set.Ioo (0 : ℝ) 1, topSum j (h fp fm α0) ≤ topSum j (h fp fm α)) :
    ∃ S : Finset (Fin m), S.card = j ∧ ∑ i ∈ S, h fp fm α0 i = topSum j (h fp fm α0) ∧
      0 ≤ ∑ i ∈ S, (fm i / (1 - α0) - fp i / α0) := by
  by_contra hcon
  push_neg at hcon
  apply nfs_no_descent fp fm j hj α0 hmin (nhdsWithin α0 (Set.Ioi α0))
  · filter_upwards [Ioo_mem_nhdsGT hα0.2] with α hα using ⟨hα0.1.trans hα.1, hα.2⟩
  · intro S hSc
    rcases lt_or_eq_of_le (nfs_g_le fp fm j hj α0 S hSc) with hlt | heq
    · have hc := (nfs_G_contOn fp fm S).continuousAt (Ioo_mem_nhds hα0.1 hα0.2)
      exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds hlt))
    · have hD := hcon S hSc heq
      have hc := (nfs_D_contOn fp fm S).continuousAt (Ioo_mem_nhds hα0.1 hα0.2)
      have ev1 : ∀ᶠ α in nhdsWithin α0 (Set.Ioi α0),
          ∑ i ∈ S, (fm i / (1 - α) - fp i / α) < 0 :=
        nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds hD))
      filter_upwards [ev1, Ioo_mem_nhdsGT hα0.2] with α h1 h2
      have t := nfs_G_tangent fp fm hfp hfm S (α := α) (β := α0) (hα0.1.trans h2.1) h2.2
        hα0.1 hα0.2
      have : 0 < (α0 - α) * ∑ i ∈ S, (fm i / (1 - α) - fp i / α) :=
        mul_pos_of_neg_of_neg (by linarith [h2.1]) h1
      rw [← heq]; linarith

lemma nfs_exists_min {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ m) :
    ∃ α0 ∈ Set.Ioo (0 : ℝ) 1, ∀ α ∈ Set.Ioo (0 : ℝ) 1,
      topSum j (h fp fm α0) ≤ topSum j (h fp fm α) := by
  obtain ⟨S0, hS0⟩ := nfs_pc_nonempty (n := m) j hj
  have hS0c : S0.card = j := (mem_powersetCard.mp hS0).2
  have hS0ne : S0.Nonempty := card_pos.mp (by omega)
  set M := topSum j (h fp fm (1 / 2)) with hM
  set c0 := ∑ i ∈ S0, Ctil fp fm i with hc0
  set a0 := ∑ i ∈ S0, fp i with ha0d
  set b0 := ∑ i ∈ S0, fm i with hb0d
  have ha0 : 0 < a0 := sum_pos (fun i _ => hfp i) hS0ne
  have hb0 : 0 < b0 := sum_pos (fun i _ => hfm i) hS0ne
  have eS : ∀ α, ∑ i ∈ S0, h fp fm α i = c0 - a0 * Real.log α - b0 * Real.log (1 - α) := by
    intro α
    simp only [h, sum_sub_distrib, ← sum_mul, hc0, ha0d, hb0d]
  have lowA : ∀ α ∈ Set.Ioo (0 : ℝ) 1, c0 - a0 * Real.log α ≤ topSum j (h fp fm α) := by
    intro α hα
    refine le_trans ?_ (nfs_g_le fp fm j hj α S0 hS0c)
    have : Real.log (1 - α) ≤ 0 := Real.log_nonpos (by linarith [hα.2]) (by linarith [hα.1])
    rw [eS]; nlinarith
  have lowB : ∀ α ∈ Set.Ioo (0 : ℝ) 1, c0 - b0 * Real.log (1 - α) ≤ topSum j (h fp fm α) := by
    intro α hα
    refine le_trans ?_ (nfs_g_le fp fm j hj α S0 hS0c)
    have : Real.log α ≤ 0 := Real.log_nonpos hα.1.le hα.2.le
    rw [eS]; nlinarith
  set δ1 := Real.exp ((c0 - M) / a0) with hδ1
  set δ2 := Real.exp ((c0 - M) / b0) with hδ2
  have kA : ∀ α ∈ Set.Ioo (0 : ℝ) 1, topSum j (h fp fm α) ≤ M → δ1 ≤ α := by
    intro α hα hle
    have := lowA α hα
    have hl : (c0 - M) / a0 ≤ Real.log α := by rw [div_le_iff₀ ha0]; nlinarith
    calc δ1 ≤ Real.exp (Real.log α) := Real.exp_le_exp.mpr hl
      _ = α := Real.exp_log hα.1
  have kB : ∀ α ∈ Set.Ioo (0 : ℝ) 1, topSum j (h fp fm α) ≤ M → δ2 ≤ 1 - α := by
    intro α hα hle
    have := lowB α hα
    have hl : (c0 - M) / b0 ≤ Real.log (1 - α) := by rw [div_le_iff₀ hb0]; nlinarith
    calc δ2 ≤ Real.exp (Real.log (1 - α)) := Real.exp_le_exp.mpr hl
      _ = 1 - α := Real.exp_log (by linarith [hα.2])
  have hK : Set.Icc δ1 (1 - δ2) ⊆ Set.Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨lt_of_lt_of_le (Real.exp_pos _) hx.1, by linarith [hx.2, Real.exp_pos ((c0 - M) / b0)]⟩
  have half : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc δ1 (1 - δ2) :=
    ⟨kA _ half le_rfl, by linarith [kB _ half le_rfl]⟩
  obtain ⟨α0, hα0K, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨_, hhalf⟩
    ((nfs_g_contOn fp fm j hj).mono hK)
  refine ⟨α0, hK hα0K, fun α hα => ?_⟩
  by_cases hαK : α ∈ Set.Icc δ1 (1 - δ2)
  · exact isMinOn_iff.mp hmin α hαK
  · have hlt : M < topSum j (h fp fm α) := by
      by_contra hc
      push_neg at hc
      exact hαK ⟨kA α hα hc, by linarith [kB α hα hc]⟩
    have := isMinOn_iff.mp hmin _ hhalf
    linarith

lemma nfs_chain {m : ℕ} (j : ℕ) (v d : Fin m → ℝ) (M : ℝ)
    (hle : ∀ U : Finset (Fin m), U.card = j → ∑ i ∈ U, v i ≤ M) :
    ∀ n : ℕ, ∀ S1 S2 : Finset (Fin m), (S1 \ S2).card = n → S1.card = j → S2.card = j →
      ∑ i ∈ S1, v i = M → ∑ i ∈ S2, v i = M → ∑ i ∈ S1, d i ≤ 0 → 0 ≤ ∑ i ∈ S2, d i →
      ∃ T S S' : Finset (Fin m), T.card ≤ j + 1 ∧ S ⊆ T ∧ S' ⊆ T ∧ S.card = j ∧
        S'.card = j ∧ ∑ i ∈ S, v i = M ∧ ∑ i ∈ S', v i = M ∧ ∑ i ∈ S, d i ≤ 0 ∧
        0 ≤ ∑ i ∈ S', d i := by
  intro n
  induction n with
  | zero =>
    intro S1 S2 hn h1 h2 hv1 hv2 hd1 hd2
    have hsub : S1 ⊆ S2 := by
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hn; exact hn
    have heq : S1 = S2 := eq_of_subset_of_card_le hsub (by omega)
    subst heq
    exact ⟨S1, S1, S1, by omega, subset_refl _, subset_refl _, h1, h1, hv1, hv1, hd1, hd2⟩
  | succ n ih =>
    intro S1 S2 hn h1 h2 hv1 hv2 hd1 hd2
    obtain ⟨x, hx⟩ : (S1 \ S2).Nonempty := by
      rw [← card_pos, hn]; omega
    rw [mem_sdiff] at hx
    obtain ⟨y, hy⟩ : (S2 \ S1).Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro he
      rw [sdiff_eq_empty_iff_subset] at he
      have := eq_of_subset_of_card_le he (by omega)
      exact hx.2 (this ▸ hx.1)
    rw [mem_sdiff] at hy
    have hyn : y ∉ S1.erase x := fun h' => hy.2 (mem_of_mem_erase h')
    have hxn : x ∉ S2.erase y := fun h' => hx.2 (mem_of_mem_erase h')
    have hc3 : (insert y (S1.erase x)).card = j := by
      rw [card_insert_of_notMem hyn, card_erase_of_mem hx.1]
      have : 1 ≤ S1.card := card_pos.mpr ⟨x, hx.1⟩
      omega
    have hc4 : (insert x (S2.erase y)).card = j := by
      rw [card_insert_of_notMem hxn, card_erase_of_mem hy.1]
      have : 1 ≤ S2.card := card_pos.mpr ⟨y, hy.1⟩
      omega
    have hsum3 : ∑ i ∈ insert y (S1.erase x), v i = ∑ i ∈ S1, v i - v x + v y := by
      rw [sum_insert hyn, ← add_sum_erase S1 v hx.1]
      ring
    have hsum4 : ∑ i ∈ insert x (S2.erase y), v i = ∑ i ∈ S2, v i - v y + v x := by
      rw [sum_insert hxn, ← add_sum_erase S2 v hy.1]
      ring
    have e1 := hle _ hc3
    have e2 := hle _ hc4
    rw [hsum3] at e1
    rw [hsum4] at e2
    have hv3 : ∑ i ∈ insert y (S1.erase x), v i = M := by rw [hsum3]; linarith
    by_cases hd3 : 0 ≤ ∑ i ∈ insert y (S1.erase x), d i
    · refine ⟨insert y S1, S1, insert y (S1.erase x), ?_, subset_insert _ _, ?_, h1, hc3,
        hv1, hv3, hd1, hd3⟩
      · rw [card_insert_of_notMem hy.2]; omega
      · exact insert_subset_insert _ (erase_subset _ _)
    · push_neg at hd3
      apply ih (insert y (S1.erase x)) S2 _ hc3 h2 hv3 hv2 hd3.le hd2
      have : insert y (S1.erase x) \ S2 = (S1 \ S2).erase x := by
        ext z
        simp only [mem_sdiff, mem_insert, mem_erase]
        constructor
        · rintro ⟨hz | ⟨hzx, hz1⟩, hz2⟩
          · exact absurd (hz ▸ hy.1) hz2
          · exact ⟨hzx, hz1, hz2⟩
        · rintro ⟨hzx, hz1, hz2⟩
          exact ⟨Or.inr ⟨hzx, hz1⟩, hz2⟩
      rw [this, card_erase_of_mem (mem_sdiff.mpr hx), hn]
      rfl

lemma nfs_key {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (j k : ℕ) (hj : j < m) (hjk : j + 1 ≤ k) : psi fp fm j ≤ phi fp fm k := by
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    have h0 : ∀ α, topSum 0 (h fp fm α) = 0 := by
      intro α
      rw [nfs_topSum_eq 0 (Nat.zero_le _) _ (nfs_pc_nonempty 0 (Nat.zero_le _))]
      simp
    have hpsi : psi fp fm 0 = C fp fm := by
      unfold psi
      rw [show (fun α => topSum 0 (h fp fm α)) = fun _ => (0 : ℝ) from funext h0,
        Set.Nonempty.image_const ⟨1 / 2, by norm_num⟩, csInf_singleton, add_zero]
    rw [hpsi]
    have hTne : ({⟨0, by omega⟩} : Finset (Fin m)).Nonempty := singleton_nonempty _
    have hc := nfs_construct fp fm hfp hfm k {⟨0, by omega⟩} hTne (by simp; omega)
    have hp := nfs_pT_mem fp fm hfp hfm _ hTne
    have hnn := sum_nonneg (fun i (_ : i ∈ ({⟨0, by omega⟩} : Finset (Fin m))) =>
      nfs_h_nonneg fp fm i (hfp i) (hfm i) hp.1 hp.2)
    linarith
  · obtain ⟨α0, hα0, hmin⟩ := nfs_exists_min fp fm hfp hfm j hj1 hj.le
    obtain ⟨S1, hc1, hv1, hd1⟩ := nfs_active_left fp fm hfp hfm j hj.le α0 hα0 hmin
    obtain ⟨S2, hc2, hv2, hd2⟩ := nfs_active_right fp fm hfp hfm j hj.le α0 hα0 hmin
    obtain ⟨T, S, S', hT, hST, hS'T, hSc, hS'c, hvS, hvS', hdS, hdS'⟩ :=
      nfs_chain j (h fp fm α0) (fun i => fm i / (1 - α0) - fp i / α0)
        (topSum j (h fp fm α0)) (fun U hU => nfs_g_le fp fm j hj.le α0 U hU) _ S1 S2 rfl
        hc1 hc2 hv1 hv2 hd1 hd2
    have hTne : T.Nonempty := (card_pos.mp (by omega : 0 < S.card)).mono hST
    have hp := nfs_pT_mem fp fm hfp hfm T hTne
    set p := (∑ i ∈ T, fp i) / (∑ i ∈ T, fp i + ∑ i ∈ T, fm i) with hpdef
    have hG : topSum j (h fp fm α0) ≤ ∑ i ∈ T, h fp fm p i := by
      rcases le_total p α0 with hpa | hpa
      · have t := nfs_G_tangent fp fm hfp hfm S hα0.1 hα0.2 hp.1 hp.2
        have : 0 ≤ (p - α0) * ∑ i ∈ S, (fm i / (1 - α0) - fp i / α0) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) hdS
        have sub := sum_le_sum_of_subset_of_nonneg hST
          (fun i _ _ => nfs_h_nonneg fp fm i (hfp i) (hfm i) hp.1 hp.2)
        linarith
      · have t := nfs_G_tangent fp fm hfp hfm S' hα0.1 hα0.2 hp.1 hp.2
        have : 0 ≤ (p - α0) * ∑ i ∈ S', (fm i / (1 - α0) - fp i / α0) :=
          mul_nonneg (by linarith) hdS'
        have sub := sum_le_sum_of_subset_of_nonneg hS'T
          (fun i _ _ => nfs_h_nonneg fp fm i (hfp i) (hfm i) hp.1 hp.2)
        linarith
    have hpsi : psi fp fm j ≤ C fp fm + topSum j (h fp fm α0) := by
      unfold psi
      have : sInf ((fun α => topSum j (h fp fm α)) '' Set.Ioo (0 : ℝ) 1)
          ≤ topSum j (h fp fm α0) :=
        csInf_le ⟨topSum j (h fp fm α0), by rintro y ⟨x, hx, rfl⟩; exact hmin x hx⟩
          ⟨α0, hα0, rfl⟩
      linarith
    have := nfs_construct fp fm hfp hfm k T hTne (by omega)
    linarith

open NaiveFS.Multinomial in
theorem solution {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hk : 4 ≤ k) (hkm : k < m) :
    psi fp fm (k - 4) ≤ phi fp fm k ∧ phi fp fm k ≤ psi fp fm k ∧
      psi fp fm k ≤ phi fp fm (k + 4) := by
  exact ⟨nfs_key fp fm hfp hfm (k - 4) k (by omega) (by omega),
    nfs_middle fp fm hfp hfm k hkm, nfs_key fp fm hfp hfm k (k + 4) hkm (by omega)⟩
