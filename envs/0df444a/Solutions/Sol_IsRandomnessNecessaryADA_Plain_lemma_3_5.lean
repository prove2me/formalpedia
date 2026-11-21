-- Prove2me | solution 1 for IsRandomnessNecessaryADA.Plain.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:37:27.564772+00:00
-- url     : https://prove2.me/submissions/143be5e5-28d7-4c67-acea-13d74e14f5d6

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Survivors

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L35

open IsRandomnessNecessaryADA.Plain

noncomputable def qT {N : ℕ} (T : Finset (Fin N)) : BooleanQuery (Fin N) :=
  fun x => decide (x ∈ T)

open scoped Classical in
noncomputable def ext {N : ℕ} {X : Type} (e : Fin N ↪ X) (q : BooleanQuery (Fin N)) :
    BooleanQuery X :=
  fun x => if h : ∃ i, e i = x then q h.choose else false

theorem ext_e {N : ℕ} {X : Type} (e : Fin N ↪ X) (q : BooleanQuery (Fin N)) (i : Fin N) :
    ext e q (e i) = q i := by
  have h : ∃ j, e j = e i := ⟨i, rfl⟩
  simp only [ext, dif_pos h]
  rw [e.injective h.choose_spec]

theorem mean_ext {N : ℕ} (hN : 0 < N) {X : Type} [Fintype X] (e : Fin N ↪ X)
    (T : Finset (Fin N)) :
    populationMean (uniformSupport hN e) (liftQuery (ext e (qT T))) = (T.card : ℝ) / N := by
  classical
  unfold populationMean uniformSupport
  have hp : ∀ i, ((uniformFin N hN) i).toReal = 1 / (N : ℝ) := by
    intro i
    unfold uniformFin
    simp [PMF.uniformOfFintype_apply]
  have hmap : ∀ x : X, ((PMF.map e (uniformFin N hN)) x).toReal =
      ∑ i : Fin N, if x = e i then 1 / (N : ℝ) else 0 := by
    intro x
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : x = e i
      · simp [h, hp]
      · simp [h]
    · intro i _
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
  simp only [hmap, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, ∑ x : X, (if x = e i then 1 / (N : ℝ) else 0) *
      (liftQuery (ext e (qT T)) x).val = 1 / (N : ℝ) * (if i ∈ T then 1 else 0) := by
    intro i
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    by_cases hi : i ∈ T <;> simp [liftQuery, ext_e, qT, bitValue, hi]
  simp only [this]
  simp [Finset.sum_ite_mem, ← Finset.mul_sum]
  field_simp


theorem common_card {N n : ℕ} (H : Finset (Fin n → Fin N)) :
    (8 / 10 : ℝ) * H.card * (commonPoints H).card ≤ n * H.card := by
  classical
  set C := commonPoints H with hC
  have h1 : ∀ i ∈ C, (8 / 10 : ℝ) * H.card ≤ ((H.filter (fun s => ∃ t, s t = i)).card : ℝ) := by
    intro i hi
    simpa [hC, commonPoints] using hi
  have h2 : (C.card : ℝ) * ((8 / 10 : ℝ) * H.card) ≤
      ∑ i ∈ C, ((H.filter (fun s => ∃ t, s t = i)).card : ℝ) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ h1
  have h3 : ∑ i ∈ C, ((H.filter (fun s => ∃ t, s t = i)).card : ℝ) =
      ∑ s ∈ H, ((C.filter (fun i => ∃ t, s t = i)).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have h4 : ∀ s ∈ H, ((C.filter (fun i => ∃ t, s t = i)).card : ℝ) ≤ n := by
    intro s _
    have : C.filter (fun i => ∃ t, s t = i) ⊆ Finset.univ.image s := by
      intro i hi
      obtain ⟨t, ht⟩ := (Finset.mem_filter.1 hi).2
      exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, ht⟩
    have h5 := (Finset.card_le_card this).trans (Finset.card_image_le (s := Finset.univ) (f := s))
    simp only [Finset.card_univ, Fintype.card_fin] at h5
    exact_mod_cast h5
  have h6 : ∑ s ∈ H, ((C.filter (fun i => ∃ t, s t = i)).card : ℝ) ≤ ∑ s ∈ H, (n : ℝ) :=
    Finset.sum_le_sum h4
  simp only [Finset.sum_const, nsmul_eq_mul] at h6
  nlinarith


theorem chain {α : Type} [DecidableEq α] (C : Finset α) (b : Finset α → Prop) (S : Finset α)
    (h0 : b C) (h1 : ¬ b (C ∪ S)) :
    ∃ S' z, S' ⊆ S ∧ z ∈ S ∧ z ∉ S' ∧ b (C ∪ S') ∧ ¬ b (C ∪ insert z S') := by
  induction S using Finset.induction_on with
  | empty => exact absurd (by simpa using h0) h1
  | insert z S'' hz ih =>
    by_cases hb : b (C ∪ S'')
    · exact ⟨S'', z, Finset.subset_insert _ _, Finset.mem_insert_self _ _, hz, hb, h1⟩
    · obtain ⟨S', z', hS', hz', hz'', hb1, hb2⟩ := ih hb
      exact ⟨S', z', hS'.trans (Finset.subset_insert _ _), Finset.mem_insert_of_mem hz', hz'', hb1, hb2⟩


open scoped Classical in
noncomputable def surv {X : Type} {n N : ℕ} (m : Mechanism X n) (e : Fin N ↪ X)
    (T : Transcript (StatisticalQuery X)) : Finset (Fin n → Fin N) :=
  Finset.univ.filter (fun s => Consistent m (fun t => e (s t)) T)

open scoped Classical in
theorem sep {X : Type} [Fintype X] (n : ℕ) (hn : 0 < n) (e : Fin (20 * n) ↪ X)
    (m : Mechanism X n) (hm : IsBitNatural m)
    (T : Transcript (StatisticalQuery X)) (hT : (surv m e T).Nonempty) :
    ∃ q : BooleanQuery (Fin (20 * n)), ∀ a : ℝ,
      |a - populationMean (uniformSupport (by omega) e) (liftQuery (ext e q))| ≤ 1 / 10 →
        (((surv m e T).filter (fun s => m (fun t => e (s t)) T (liftQuery (ext e q)) = a)).card : ℝ)
          ≤ (9 / 10 : ℝ) * (surv m e T).card := by
  have hNpos : 0 < 20 * n := by omega
  set H := surv m e T with hH
  have hhpos : (0 : ℝ) < H.card := by exact_mod_cast hT.card_pos
  by_contra hns
  push Not at hns
  have hns' := hns
  set C := commonPoints H with hC
  have hCcard : (C.card : ℝ) ≤ 5 / 4 * n := by
    have := common_card H
    have h2 : (8 / 10 : ℝ) * (C.card : ℝ) ≤ n := by
      by_contra hcon
      push Not at hcon
      nlinarith
    linarith
  let b : Finset (Fin (20 * n)) → Prop := fun T' => ∃ a : ℝ, a < 1 / 2 ∧
    |a - populationMean (uniformSupport hNpos e) (liftQuery (ext e (qT T')))| ≤ 1 / 10 ∧
      (9 / 10 : ℝ) * H.card < ((H.filter (fun s => m (fun t => e (s t)) T
        (liftQuery (ext e (qT T'))) = a)).card : ℝ)
  have hN : (0 : ℝ) < ((20 * n : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hb0 : b C := by
    obtain ⟨a, ha, hbig⟩ := hns' (qT C)
    refine ⟨a, ?_, ha, hbig⟩
    rw [mean_ext] at ha
    have hmean : (C.card : ℝ) / ((20 * n : ℕ) : ℝ) ≤ 1 / 16 := by
      rw [div_le_iff₀ hN]; push_cast; nlinarith
    have := (abs_le.1 ha).2
    linarith
  have hb1 : ¬ b (C ∪ (Finset.univ \ C)) := by
    rintro ⟨a, ha1, ha, _⟩
    rw [mean_ext] at ha
    have : C ∪ (Finset.univ \ C) = Finset.univ := by simp
    rw [this] at ha
    simp only [Finset.card_univ, Fintype.card_fin] at ha
    rw [div_self hN.ne'] at ha
    have := (abs_le.1 ha).1
    linarith
  obtain ⟨S', z, hS', hz, hzS', hbS, hnb⟩ := chain C b (Finset.univ \ C) hb0 hb1
  have hzC : z ∉ C := (Finset.mem_sdiff.1 hz).2
  obtain ⟨a1, ha1, _, hbig1⟩ := hbS
  obtain ⟨a2, ha2, hbig2⟩ := hns' (qT (C ∪ insert z S'))
  have ha2' : 1 / 2 ≤ a2 := by
    by_contra hcon
    exact hnb ⟨a2, not_le.1 hcon, ha2, hbig2⟩
  set W1 := H.filter (fun s => m (fun t => e (s t)) T (liftQuery (ext e (qT (C ∪ S')))) = a1) with hW1
  set W2 := H.filter (fun s => m (fun t => e (s t)) T (liftQuery (ext e (qT (C ∪ insert z S')))) = a2) with hW2
  have hW1H : W1 ⊆ H := fun s hs => (Finset.mem_filter.1 hs).1
  have hW2H : W2 ⊆ H := fun s hs => (Finset.mem_filter.1 hs).1
  have hsub : W1 ∩ W2 ⊆ H.filter (fun s => ∃ t, s t = z) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_inter.1 hs
    refine Finset.mem_filter.2 ⟨hW1H hs1, ?_⟩
    by_contra hcon
    push Not at hcon
    have h1 : m (fun t => e (s t)) T (liftQuery (ext e (qT (C ∪ S')))) = a1 :=
      (Finset.mem_filter.1 hs1).2
    have h2 : m (fun t => e (s t)) T (liftQuery (ext e (qT (C ∪ insert z S')))) = a2 :=
      (Finset.mem_filter.1 hs2).2
    have h3 := hm (fun t => e (s t)) T (liftQuery (ext e (qT (C ∪ S'))))
      (liftQuery (ext e (qT (C ∪ insert z S'))))
      (fun t => by
        have := hcon t
        simp [liftQuery, ext_e, qT, Finset.mem_union, Finset.mem_insert, this])
    rw [h1, h2] at h3
    have e1 : responseBit a1 = false := by simp [responseBit]; linarith
    have e2 : responseBit a2 = true := by simp [responseBit]; linarith
    rw [e1, e2] at h3
    exact Bool.false_ne_true h3
  have hcard1 : ((W1 ∩ W2).card : ℝ) ≤ ((H.filter (fun s => ∃ t, s t = z)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hnc : ((H.filter (fun s => ∃ t, s t = z)).card : ℝ) < (8 / 10 : ℝ) * H.card := by
    by_contra hcon
    push Not at hcon
    apply hzC
    simpa [hC, commonPoints] using hcon
  have hu : ((W1 ∪ W2).card : ℝ) ≤ H.card := by
    exact_mod_cast Finset.card_le_card (Finset.union_subset hW1H hW2H)
  have hi : ((W1 ∪ W2).card : ℝ) + (W1 ∩ W2).card = W1.card + W2.card := by
    exact_mod_cast Finset.card_union_add_card_inter W1 W2
  linarith

end IsRandomnessNecessaryADA.Plain.Dev.L35

namespace IsRandomnessNecessaryADA.Plain.Dev.L35

open IsRandomnessNecessaryADA.Plain

theorem replay_append {X Q : Type} {n : ℕ} (m : Response X Q n) (s : Fin n → X) (h : List Q) (q : Q) :
    replayQueries m s (h ++ [q]) = replayQueries m s h ++ [(q, m s (replayQueries m s h) q)] := by
  simp [replayQueries, List.foldl_append]

theorem inter_consistent {X : Type} {n : ℕ} (m : Mechanism X n) (A : Strategy (StatisticalQuery X))
    (s : Fin n → X) (k : ℕ) : Consistent m s (interaction m A s k) := by
  induction k with
  | zero => simp [Consistent, interaction, replayQueries]
  | succ k ih =>
    unfold Consistent at ih ⊢
    simp only [interaction, List.map_append, List.map_cons, List.map_nil]
    rw [replay_append, ih]

theorem consistent_prefix {X : Type} {n : ℕ} (m : Mechanism X n) (s : Fin n → X)
    (T : Transcript (StatisticalQuery X)) (q : StatisticalQuery X) (a : ℝ)
    (h : Consistent m s (T ++ [(q, a)])) : Consistent m s T ∧ m s T q = a := by
  unfold Consistent at h ⊢
  simp only [List.map_append, List.map_cons, List.map_nil] at h
  rw [replay_append] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  refine ⟨h1, ?_⟩
  rw [h1] at h2
  simpa using (Prod.mk.inj (List.cons.inj h2).1).2

theorem mem_interaction_mono {X : Type} {n : ℕ} (m : Mechanism X n) (A : Strategy (StatisticalQuery X))
    (s : Fin n → X) {j k : ℕ} (hjk : j ≤ k) {x : StatisticalQuery X × ℝ}
    (hx : x ∈ interaction m A s j) : x ∈ interaction m A s k := by
  induction hjk with
  | refl => exact hx
  | step _ ih => simp only [interaction]; exact List.mem_append_left _ ih

end IsRandomnessNecessaryADA.Plain.Dev.L35

namespace IsRandomnessNecessaryADA.Plain

open scoped Classical in
noncomputable def Dev.L35.attacker {X : Type} [Fintype X] (n : ℕ) (hn : 0 < n) (e : Fin (20 * n) ↪ X)
    (m : Mechanism X n) (hm : IsBitNatural m) : BooleanAnalyst X :=
  fun T => if h : (Dev.L35.surv m e T).Nonempty then
    Dev.L35.ext e (Classical.choose (Dev.L35.sep n hn e m hm T h)) else fun _ => false

theorem Dev.L35.horizon_pos (n : ℕ) (hn : 0 < n) :
    ((20 * n : ℕ) : ℝ) ^ n < (10 / 9 : ℝ) ^ (attackHorizon n (20 * n)) := by
  have hl : 0 < Real.log (10 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < ((20 * n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 20 * n by omega)
  have h1 : Real.log (((20 * n : ℕ) : ℝ) ^ n) / Real.log (10 / 9 : ℝ) <
      (attackHorizon n (20 * n) : ℝ) := by
    unfold attackHorizon
    have := Nat.le_ceil (Real.log ((((20 * n : ℕ) : ℝ)) ^ n) / Real.log (10 / 9 : ℝ))
    push_cast at this ⊢
    linarith
  rw [div_lt_iff₀ hl] at h1
  have h2 : (10 / 9 : ℝ) ^ (attackHorizon n (20 * n)) =
      Real.exp ((attackHorizon n (20 * n) : ℝ) * Real.log (10 / 9 : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h2]
  calc ((20 * n : ℕ) : ℝ) ^ n = Real.exp (Real.log (((20 * n : ℕ) : ℝ) ^ n)) :=
        (Real.exp_log (by positivity)).symm
    _ < _ := Real.exp_lt_exp.2 h1

theorem Dev.L35.horizon_le (n : ℕ) (hn : 0 < n) :
    (attackHorizon n (20 * n) : ℝ) ≤ 20 * n * (Real.log ((20 * n : ℕ) : ℝ) / Real.log 2) := by
  have hl : (1 / 10 : ℝ) ≤ Real.log (10 / 9 : ℝ) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 10 / 9 by norm_num)
    norm_num at this ⊢; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL2 : Real.log 2 ≤ Real.log ((20 * n : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by push_cast; nlinarith)
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  set L := Real.log ((20 * n : ℕ) : ℝ) with hLdef
  have hlogpow : Real.log (((20 * n : ℕ) : ℝ) ^ n) = n * L := by rw [Real.log_pow]
  unfold attackHorizon
  rw [hlogpow]
  have hceil : (Nat.ceil (Real.log ((((20 * n : ℕ) : ℝ)) ^ n) / Real.log (10 / 9 : ℝ)) : ℝ) <
      Real.log ((((20 * n : ℕ) : ℝ)) ^ n) / Real.log (10 / 9 : ℝ) + 1 := Nat.ceil_lt_add_one (by
      apply div_nonneg
      · rw [hlogpow]; positivity
      · exact (by norm_num : (0:ℝ) < 1/10).le.trans hl)
  rw [hlogpow] at hceil
  have hdiv : (n * L) / Real.log (10 / 9 : ℝ) ≤ 10 * (n * L) := by
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hl)]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (by linarith : (0:ℝ) ≤ L)]
  have hL0 : 0 < Real.log 2 := by linarith
  have h28 : 28 * (n * L) ≤ 20 * n * (L / Real.log 2) := by
    have e1 : 20 * (n : ℝ) * (L / Real.log 2) = 20 * n * L / Real.log 2 := by ring
    rw [e1, le_div_iff₀ hL0]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (by linarith : (0:ℝ) ≤ L)]
  have hnL : (0.69 : ℝ) ≤ n * L := by nlinarith
  push_cast at hceil ⊢
  linarith

theorem chk_lemma_3_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type} [Fintype X] (n : ℕ) (hn : 0 < n)
      (e : Fin (20 * n) ↪ X) (m : Mechanism X n), IsBitNatural m →
      (attackHorizon n (20 * n) : ℝ) ≤ C * n * (Real.log (20 * n) / Real.log 2) ∧
      ∃ A : BooleanAnalyst X, ∀ s : Fin n → Fin (20 * n),
        interaction m (liftAnalyst A) (fun t => e (s t)) (attackHorizon n (20 * n)) ∈
          errorEvent (uniformSupport (by omega) e) (1 / 10) := by
  classical
  refine ⟨20, by norm_num, ?_⟩
  intro X _ n hn e m hm
  refine ⟨?_, Dev.L35.attacker n hn e m hm, ?_⟩
  · have := Dev.L35.horizon_le n hn
    simpa using this
  intro s
  by_contra herr
  set k := attackHorizon n (20 * n) with hk
  set p := uniformSupport (show 0 < 20 * n by omega) e with hp
  have hacc : ∀ qa ∈ interaction m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) k,
      |qa.2 - populationMean p qa.1| ≤ 1 / 10 := by
    intro qa hqa
    by_contra hq
    exact herr ⟨qa, hqa, not_le.1 hq⟩
  have key : ∀ j, j ≤ k →
      s ∈ Dev.L35.surv m e (interaction m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) j) ∧
      ((Dev.L35.surv m e (interaction m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) j)).card : ℝ)
        ≤ (9 / 10 : ℝ) ^ j * ((20 * n : ℕ) : ℝ) ^ n := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp [Dev.L35.surv, interaction, Consistent, replayQueries], ?_⟩
      have : (Dev.L35.surv m e (interaction m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) 0)).card ≤ Fintype.card (Fin n → Fin (20 * n)) :=
        Finset.card_le_univ _
      simp only [Fintype.card_fun, Fintype.card_fin] at this
      simpa using (by exact_mod_cast this : (_ : ℝ) ≤ _)
    | succ j ih =>
      intro hj
      obtain ⟨hs, hcard⟩ := ih (by omega)
      set Tj := interaction m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) j with hTj
      have hstep : interaction m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) (j + 1) =
          Tj ++ [(liftAnalyst (Dev.L35.attacker n hn e m hm) Tj,
            m (fun t => e (s t)) Tj (liftAnalyst (Dev.L35.attacker n hn e m hm) Tj))] := rfl
      have hne : (Dev.L35.surv m e Tj).Nonempty := ⟨s, hs⟩
      have hAT : liftAnalyst (Dev.L35.attacker n hn e m hm) Tj =
          liftQuery (Dev.L35.ext e (Classical.choose (Dev.L35.sep n hn e m hm Tj hne))) := by
        simp only [liftAnalyst, Dev.L35.attacker, dif_pos hne]
      have hmem : (liftAnalyst (Dev.L35.attacker n hn e m hm) Tj,
            m (fun t => e (s t)) Tj (liftAnalyst (Dev.L35.attacker n hn e m hm) Tj)) ∈
          interaction m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) k := by
        refine Dev.L35.mem_interaction_mono m _ _ (show j + 1 ≤ k from hj) ?_
        rw [hstep]; exact List.mem_append_right _ (List.mem_singleton_self _)
      have hacc1 := hacc _ hmem
      simp only [hAT] at hacc1
      have hsep := Classical.choose_spec (Dev.L35.sep n hn e m hm Tj hne)
      have hsep1 := hsep _ hacc1
      rw [hstep]
      constructor
      · have := Dev.L35.inter_consistent m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) (j + 1)
        rw [hstep] at this
        simpa [Dev.L35.surv] using this
      · have hsub : Dev.L35.surv m e (Tj ++ [(liftAnalyst (Dev.L35.attacker n hn e m hm) Tj,
            m (fun t => e (s t)) Tj (liftAnalyst (Dev.L35.attacker n hn e m hm) Tj))]) ⊆
            (Dev.L35.surv m e Tj).filter (fun s' => m (fun t => e (s' t)) Tj
              (liftQuery (Dev.L35.ext e (Classical.choose (Dev.L35.sep n hn e m hm Tj hne)))) =
                m (fun t => e (s t)) Tj
                  (liftQuery (Dev.L35.ext e (Classical.choose (Dev.L35.sep n hn e m hm Tj hne))))) := by
          intro s' hs'
          have hc : Consistent m (fun t => e (s' t)) (Tj ++ [(liftAnalyst (Dev.L35.attacker n hn e m hm) Tj,
            m (fun t => e (s t)) Tj (liftAnalyst (Dev.L35.attacker n hn e m hm) Tj))]) := by
            simpa [Dev.L35.surv] using hs'
          obtain ⟨h1, h2⟩ := Dev.L35.consistent_prefix m _ _ _ _ hc
          rw [hAT] at h2
          exact Finset.mem_filter.2 ⟨by simpa [Dev.L35.surv] using h1, h2⟩
        have hc2 : (((Dev.L35.surv m e (Tj ++ [(liftAnalyst (Dev.L35.attacker n hn e m hm) Tj,
            m (fun t => e (s t)) Tj (liftAnalyst (Dev.L35.attacker n hn e m hm) Tj))])).card : ℕ) : ℝ) ≤
            (9 / 10 : ℝ) * (Dev.L35.surv m e Tj).card :=
          le_trans (by exact_mod_cast Finset.card_le_card hsub) hsep1
        calc _ ≤ (9 / 10 : ℝ) * (Dev.L35.surv m e Tj).card := hc2
          _ ≤ (9 / 10 : ℝ) * ((9 / 10 : ℝ) ^ j * ((20 * n : ℕ) : ℝ) ^ n) := by gcongr
          _ = _ := by ring
  obtain ⟨hsk, hck⟩ := key k le_rfl
  have hpos : (1 : ℝ) ≤ ((Dev.L35.surv m e (interaction m (liftAnalyst (Dev.L35.attacker n hn e m hm)) (fun t => e (s t)) k)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨s, hsk⟩
  have hh := Dev.L35.horizon_pos n hn
  rw [← hk] at hh
  have h9 : (9 / 10 : ℝ) ^ k * (10 / 9 : ℝ) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have h10 : (9 / 10 : ℝ) ^ k * ((20 * n : ℕ) : ℝ) ^ n < 1 := by
    calc (9 / 10 : ℝ) ^ k * ((20 * n : ℕ) : ℝ) ^ n < (9 / 10 : ℝ) ^ k * (10 / 9 : ℝ) ^ k := by
          gcongr
      _ = 1 := h9
  linarith

end IsRandomnessNecessaryADA.Plain
end

theorem solution : type_of% @IsRandomnessNecessaryADA.Plain.chk_lemma_3_5 := @IsRandomnessNecessaryADA.Plain.chk_lemma_3_5
