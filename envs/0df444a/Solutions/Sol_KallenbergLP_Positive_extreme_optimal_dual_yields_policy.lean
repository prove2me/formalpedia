-- Prove2me | solution 1 for KallenbergLP.Positive.extreme_optimal_dual_yields_policy
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:00:46.166802+00:00
-- url     : https://prove2.me/submissions/51c9123d-94b5-4fdc-aebb-73c617204c08

import Definitions.Def_KallenbergLP_Positive_Dual



namespace KallenbergLP.Positive

set_option linter.unusedSectionVars false

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

theorem History.ext' {n : ℕ} {h1 h2 : History N α n} (hs : h1.states = h2.states)
    (hc : h1.chosen = h2.chosen) : h1 = h2 := by
  cases h1; cases h2; cases hs; cases hc; rfl

def History.cons {n : ℕ} (s : Fin N) (c : α) (h : History N α n) : History N α (n+1) where
  states := fun i => if hi : i.val = 0 then s else h.states ⟨i.val - 1, by have := i.isLt; omega⟩
  chosen := fun i => if hi : i.val = 0 then c else h.chosen ⟨i.val - 1, by have := i.isLt; omega⟩

def History.tail {n : ℕ} (h : History N α (n+1)) : History N α n where
  states := fun i => h.states ⟨i.val + 1, by have := i.isLt; omega⟩
  chosen := fun i => h.chosen ⟨i.val + 1, by have := i.isLt; omega⟩

def History.init (N : ℕ) (α : Type) (s : Fin N) : History N α 0 := ⟨fun _ => s, Fin.elim0⟩

def consEquiv (n : ℕ) : History N α (n+1) ≃ Fin N × α × History N α n where
  toFun h := (h.states ⟨0, by omega⟩, h.chosen ⟨0, by omega⟩, h.tail)
  invFun p := History.cons p.1 p.2.1 p.2.2
  left_inv h := by
    apply History.ext'
    · funext i
      simp only [History.cons, History.tail]
      split_ifs with hi
      · congr 1; ext; simp [hi]
      · congr 1; ext; simp; omega
    · funext i
      simp only [History.cons, History.tail]
      split_ifs with hi
      · congr 1; ext; simp [hi]
      · congr 1; ext; simp; omega
  right_inv p := by
    obtain ⟨s, c, h⟩ := p
    simp only [History.cons, History.tail, Prod.mk.injEq]
    refine ⟨by simp, by simp, ?_⟩
    apply History.ext' <;> funext i <;> simp

theorem cons_last {n : ℕ} (s : Fin N) (c : α) (h : History N α n) :
    (h.cons s c).last = h.last := by
  simp [History.cons, History.last]

theorem prefix_cons_succ {n : ℕ} (s : Fin N) (c : α) (h : History N α n) (k : Fin n) :
    (h.cons s c).prefix k.succ = (h.prefix k).cons s c := rfl

theorem prefix_cons_zero {n : ℕ} (s : Fin N) (c : α) (h : History N α n) :
    (h.cons s c).prefix ⟨0, by omega⟩ = History.init N α s := by
  apply History.ext'
  · funext i; simp [History.cons, History.prefix, History.init]
  · funext i; exact i.elim0

variable {M : MDP N α}

def Policy.cont (R : Policy M) (s : Fin N) (c : α) : Policy M where
  choose m h b := R.choose (m+1) (h.cons s c) b
  choose_nonneg := fun m h b => R.choose_nonneg _ _ _
  choose_outside := fun m h b hb => R.choose_outside _ _ _ (by rwa [cons_last])
  choose_sum_one := fun m h => R.choose_sum_one _ _

def pi0 (R : Policy M) (i : Fin N) (a : α) : ℝ := R.choose 0 (History.init N α i) a

theorem hp_cons (R : Policy M) (i : Fin N) (n : ℕ) (s : Fin N) (c : α) (h : History N α n) :
    historyProb M R i (n+1) (h.cons s c) =
      (if s = i then 1 else 0) * (pi0 R s c * M.transition s c (h.states ⟨0, by omega⟩)) *
      ∏ k : Fin n, (R.choose (k.val+1) ((h.prefix k).cons s c) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k) (h.states ⟨k.val + 1, by omega⟩)) := by
  unfold historyProb
  rw [Fin.prod_univ_succ]
  have h0 : (h.cons s c).prefix (0 : Fin (n+1)) = History.init N α s := prefix_cons_zero s c h
  have h1 : ∀ k : Fin n, (h.cons s c).prefix k.succ = (h.prefix k).cons s c := fun k => rfl
  simp only [Fin.val_zero, h0, Fin.val_succ, h1]
  simp [History.cons, pi0, mul_assoc]

theorem hp_cont (R : Policy M) (s : Fin N) (c : α) (j : Fin N) (n : ℕ) (h : History N α n) :
    historyProb M (R.cont s c) j n h =
      (if h.states ⟨0, by omega⟩ = j then 1 else 0) *
      ∏ k : Fin n, (R.choose (k.val+1) ((h.prefix k).cons s c) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k) (h.states ⟨k.val + 1, by omega⟩)) := rfl


theorem occ_zero (R : Policy M) (i k : Fin N) (b : α) :
    occupancy M R i k b 0 = if k = i then pi0 R i b else 0 := by
  unfold occupancy historyProb
  rw [Fintype.sum_eq_single (History.init N α i)]
  · by_cases hk : k = i
    · subst hk; simp [History.last, History.init, pi0]
    · simp [History.last, History.init, hk, Ne.symm hk]
  · intro h hne
    have : ¬ (h.states ⟨0, by omega⟩ = i) := by
      intro hh; apply hne
      apply History.ext'
      · funext j; rw [show j = ⟨0, by omega⟩ from Fin.ext (by omega)]; exact hh
      · funext j; exact j.elim0
    simp only [ite_mul, one_mul, zero_mul]
    split_ifs with h1 h2 <;> first | rfl | exact absurd h2 this

theorem occ_succ (R : Policy M) (i k : Fin N) (b : α) (n : ℕ) :
    occupancy M R i k b (n+1) =
      ∑ c, pi0 R i c * ∑ j, M.transition i c j * occupancy M (R.cont i c) j k b n := by
  unfold occupancy
  conv_lhs => rw [← (consEquiv n).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  have e : ∀ p : Fin N × α × History N α n, (consEquiv n).symm p = p.2.2.cons p.1 p.2.1 := fun _ => rfl
  simp only [e, cons_last, hp_cons, hp_cont]
  rw [Finset.sum_eq_single i (fun s _ hs => by simp [hs]) (by simp)]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_eq_single (h.states ⟨0, by omega⟩)]
  · split_ifs with h1 h2 <;> first | exact absurd rfl h2 | (simp [Policy.cont]; ring) | simp
  · intro j _ hj
    have : ¬ h.states 0 = j := fun e => hj (by rw [← e]; rfl)
    simp [this]
  · simp

theorem pi0_nonneg (R : Policy M) (i : Fin N) (a : α) : 0 ≤ pi0 R i a := R.choose_nonneg _ _ _

theorem pi0_outside (R : Policy M) (i : Fin N) (a : α) (ha : a ∉ M.actions i) : pi0 R i a = 0 :=
  R.choose_outside _ _ _ ha

theorem pi0_sum (R : Policy M) (i : Fin N) : ∑ a ∈ M.actions i, pi0 R i a = 1 := by
  rw [Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => pi0_outside R i a ha)]
  exact R.choose_sum_one _ _

theorem sum_univ_eq_actions (R : Policy M) (i : Fin N) (g : α → ℝ) :
    ∑ a, pi0 R i a * g a = ∑ a ∈ M.actions i, pi0 R i a * g a := by
  rw [Finset.sum_subset (Finset.subset_univ (M.actions i))]
  intro a _ ha; rw [pi0_outside R i a ha, zero_mul]

theorem occ_nonneg (n : ℕ) : ∀ (R : Policy M) (i k : Fin N) (b : α), 0 ≤ occupancy M R i k b n := by
  induction n with
  | zero => intro R i k b; rw [occ_zero]; split_ifs; exact pi0_nonneg _ _ _; exact le_rfl
  | succ n ih =>
    intro R i k b
    rw [occ_succ, sum_univ_eq_actions]
    apply Finset.sum_nonneg; intro c hc
    apply mul_nonneg (pi0_nonneg _ _ _)
    apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (M.transition_nonneg _ _ _ hc) (ih _ _ _ _)

theorem occ_outside (n : ℕ) : ∀ (R : Policy M) (i k : Fin N) (b : α), b ∉ M.actions k →
    occupancy M R i k b n = 0 := by
  induction n with
  | zero =>
    intro R i k b hb; rw [occ_zero]; split_ifs with h
    · subst h; exact pi0_outside _ _ _ hb
    · rfl
  | succ n ih =>
    intro R i k b hb
    rw [occ_succ]
    apply Finset.sum_eq_zero; intro c _
    rw [Finset.sum_eq_zero, mul_zero]; intro j _
    rw [ih _ _ _ _ hb, mul_zero]

theorem stage_zero (R : Policy M) (i : Fin N) :
    stageReward M R i 0 = ∑ a ∈ M.actions i, pi0 R i a * M.reward i a := by
  unfold stageReward
  simp only [occ_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem stage_succ (R : Policy M) (i : Fin N) (n : ℕ) :
    stageReward M R i (n+1) =
      ∑ c, pi0 R i c * ∑ j, M.transition i c j * stageReward M (R.cont i c) j n := by
  unfold stageReward
  calc _ = ∑ k, ∑ b ∈ M.actions k, ∑ c, ∑ j, pi0 R i c * (M.transition i c j *
            (occupancy M (R.cont i c) j k b n * M.reward k b)) := by
          simp only [occ_succ, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ = ∑ k, ∑ c, ∑ b ∈ M.actions k, ∑ j, pi0 R i c * (M.transition i c j *
            (occupancy M (R.cont i c) j k b n * M.reward k b)) :=
          Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ k, ∑ c, ∑ j, ∑ b ∈ M.actions k, pi0 R i c * (M.transition i c j *
            (occupancy M (R.cont i c) j k b n * M.reward k b)) :=
          Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
    _ = ∑ c, ∑ k, ∑ j, ∑ b ∈ M.actions k, pi0 R i c * (M.transition i c j *
            (occupancy M (R.cont i c) j k b n * M.reward k b)) := Finset.sum_comm
    _ = ∑ c, ∑ j, ∑ k, ∑ b ∈ M.actions k, pi0 R i c * (M.transition i c j *
            (occupancy M (R.cont i c) j k b n * M.reward k b)) :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
    _ = _ := by simp only [Finset.mul_sum]

def Spart (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, stageReward M R i t

theorem Spart_succ (R : Policy M) (i : Fin N) (n : ℕ) :
    Spart M R i (n+1) = ∑ a ∈ M.actions i, pi0 R i a * M.reward i a +
      ∑ c, pi0 R i c * ∑ j, M.transition i c j * Spart M (R.cont i c) j n := by
  unfold Spart
  rw [Finset.sum_range_succ', stage_zero, add_comm]
  congr 1
  simp only [stage_succ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.mul_sum]

theorem stage_nonneg (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a)
    (R : Policy M) (i : Fin N) (n : ℕ) : 0 ≤ stageReward M R i n := by
  unfold stageReward
  apply Finset.sum_nonneg; intro k _
  apply Finset.sum_nonneg; intro b hb
  exact mul_nonneg (occ_nonneg _ _ _ _ _) (hr _ _ hb)

theorem Spart_mono (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a)
    (R : Policy M) (i : Fin N) : Monotone (Spart M R i) := by
  apply monotone_nat_of_le_succ; intro n
  unfold Spart; rw [Finset.sum_range_succ]
  linarith [stage_nonneg hr R i n]

theorem Spart_nonneg (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a)
    (R : Policy M) (i : Fin N) (n : ℕ) : 0 ≤ Spart M R i n :=
  Finset.sum_nonneg (fun t _ => stage_nonneg hr R i t)

theorem Spart_le_super (w : Fin N → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : IsSuperharmonic M w)
    (n : ℕ) : ∀ (R : Policy M) (i : Fin N), Spart M R i n ≤ w i := by
  induction n with
  | zero => intro R i; simp [Spart, hw0]
  | succ n ih =>
    intro R i
    rw [Spart_succ, sum_univ_eq_actions R i, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ a ∈ M.actions i, pi0 R i a * w i := by
          apply Finset.sum_le_sum; intro a ha
          rw [← mul_add]
          apply mul_le_mul_of_nonneg_left _ (pi0_nonneg _ _ _)
          refine le_trans ?_ (hw i a ha)
          gcongr with j
          all_goals first | exact ih _ _ | exact M.transition_nonneg _ _ _ ha
      _ = w i := by rw [← Finset.sum_mul, pi0_sum, one_mul]

theorem ereal_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, EReal.coe_add, ih]

theorem totalReward_eq (R : Policy M) (i : Fin N) :
    totalReward M R i = ⨆ n, ((Spart M R i n : ℝ) : EReal) := rfl

noncomputable def defaultRule (M : MDP N α) : PureRule M :=
  ⟨fun i => (M.actions_nonempty i).choose, fun i => (M.actions_nonempty i).choose_spec⟩

theorem tail_last {n : ℕ} (h : History N α (n+1)) : h.tail.last = h.last := rfl

theorem tail_cons {n : ℕ} (s : Fin N) (c : α) (h : History N α n) : (h.cons s c).tail = h := by
  apply History.ext' <;> funext i <;> simp [History.cons, History.tail]

noncomputable def firstThen (M : MDP N α) (a : α) (Rs : Fin N → Policy M) : Policy M where
  choose := fun m => match m with
    | 0 => fun h b => if a ∈ M.actions h.last then (if b = a then 1 else 0)
        else (purePolicy M (defaultRule M)).choose 0 h b
    | m+1 => fun h b => (Rs (h.states ⟨1, by omega⟩)).choose m h.tail b
  choose_nonneg := by
    intro m; cases m with
    | zero => intro h b; dsimp only; split_ifs <;> first | exact Policy.choose_nonneg _ _ _ _ | norm_num
    | succ m => intro h b; exact Policy.choose_nonneg _ _ _ _
  choose_outside := by
    intro m; cases m with
    | zero =>
      intro h b hb; dsimp only
      split_ifs with h1 h2
      · exact absurd (h2 ▸ h1) hb
      · rfl
      · exact Policy.choose_outside _ _ _ _ hb
    | succ m => intro h b hb; exact Policy.choose_outside _ _ _ _ (by rwa [tail_last])
  choose_sum_one := by
    intro m; cases m with
    | zero =>
      intro h; dsimp only
      split_ifs
      · simp
      · exact Policy.choose_sum_one _ _ _
    | succ m => intro h; exact Policy.choose_sum_one _ _ _

theorem occ_congr (R1 R2 : Policy M) (j : Fin N)
    (H : ∀ m (h : History N α m), h.states ⟨0, by omega⟩ = j → R1.choose m h = R2.choose m h)
    (k : Fin N) (b : α) (n : ℕ) : occupancy M R1 j k b n = occupancy M R2 j k b n := by
  unfold occupancy historyProb
  apply Finset.sum_congr rfl; intro h _
  by_cases hj : h.states ⟨0, by omega⟩ = j
  · have e : ∀ (k : Fin n), R1.choose k.val (h.prefix k) = R2.choose k.val (h.prefix k) :=
      fun k => H _ _ hj
    simp only [e, H n h hj]
  · have hj' : ¬ h.states 0 = j := hj
    simp [hj']

theorem Spart_congr (R1 R2 : Policy M) (j : Fin N)
    (H : ∀ m (h : History N α m), h.states ⟨0, by omega⟩ = j → R1.choose m h = R2.choose m h)
    (n : ℕ) : Spart M R1 j n = Spart M R2 j n := by
  unfold Spart stageReward
  simp only [occ_congr R1 R2 j H]

theorem Spart_firstThen (a : α) (Rs : Fin N → Policy M) (i : Fin N) (ha : a ∈ M.actions i)
    (n : ℕ) : Spart M (firstThen M a Rs) i (n+1) =
      M.reward i a + ∑ j, M.transition i a j * Spart M (Rs j) j n := by
  have hpi : ∀ c, pi0 (firstThen M a Rs) i c = if c = a then 1 else 0 := by
    intro c
    show (if a ∈ M.actions (History.init N α i).last then _ else _) = _
    rw [if_pos (show a ∈ M.actions (History.init N α i).last from ha)]
  have hc : ∀ j, Spart M ((firstThen M a Rs).cont i a) j n = Spart M (Rs j) j n := by
    intro j
    apply Spart_congr
    intro m h hj
    funext b
    show (Rs ((h.cons i a).states ⟨1, by omega⟩)).choose m (h.cons i a).tail b = _
    rw [tail_cons]
    have : (h.cons i a).states ⟨1, by omega⟩ = j := by
      rw [← hj]; simp [History.cons]
    rw [this]
  rw [Spart_succ]
  simp only [hpi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ha, hc]

theorem value_nonneg (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a) (i : Fin N) :
    (0 : EReal) ≤ value M i := by
  unfold value
  refine le_iSup_of_le (purePolicy M (defaultRule M)) ?_
  rw [totalReward_eq]
  refine le_iSup_of_le 0 ?_
  simp [Spart]

theorem value_le_super (w : Fin N → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : IsSuperharmonic M w)
    (i : Fin N) : value M i ≤ (w i : EReal) := by
  unfold value
  refine iSup_le fun R => ?_
  rw [totalReward_eq]
  exact iSup_le fun n => EReal.coe_le_coe_iff.mpr (Spart_le_super w hw0 hw n R i)

theorem Spart_le_value (R : Policy M) (i : Fin N) (n : ℕ) :
    ((Spart M R i n : ℝ) : EReal) ≤ value M i := by
  unfold value
  refine le_iSup_of_le R ?_
  rw [totalReward_eq]
  exact le_iSup_of_le n le_rfl

theorem value_superharmonic (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a)
    (i : Fin N) (a : α) (ha : a ∈ M.actions i) :
    (↑(M.reward i a) : EReal) + ∑ j, (↑(M.transition i a j) : EReal) * value M j ≤ value M i := by
  have key : ∀ (Rs : Fin N → Policy M) n,
      ((M.reward i a + ∑ j, M.transition i a j * Spart M (Rs j) j n : ℝ) : EReal) ≤ value M i := by
    intro Rs n; rw [← Spart_firstThen a Rs i ha n]; exact Spart_le_value _ _ _
  have hp : ∀ j, 0 ≤ M.transition i a j := fun j => M.transition_nonneg _ _ _ ha
  have hS : ∀ R j n, 0 ≤ Spart M R j n := Spart_nonneg hr
  by_cases hA : ∃ j, 0 < M.transition i a j ∧ value M j = ⊤
  · obtain ⟨j, hpj, hVj⟩ := hA
    have : value M i = ⊤ := by
      rw [EReal.eq_top_iff_forall_lt]
      intro y
      have h1 : ((y / M.transition i a j : ℝ) : EReal) < value M j := by
        rw [hVj]; exact EReal.coe_lt_top _
      unfold value at h1
      obtain ⟨R, hR⟩ := lt_iSup_iff.mp h1
      rw [totalReward_eq] at hR
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp hR
      have hn' := EReal.coe_lt_coe_iff.mp hn
      refine lt_of_lt_of_le ?_ (key (fun _ => R) n)
      apply EReal.coe_lt_coe_iff.mpr
      have h2 : y < M.transition i a j * Spart M R j n := by
        rw [div_lt_iff₀ hpj] at hn'; linarith
      have h3 : M.transition i a j * Spart M R j n ≤ ∑ j', M.transition i a j' * Spart M R j' n :=
        Finset.single_le_sum (f := fun j' => M.transition i a j' * Spart M R j' n)
          (fun j' _ => mul_nonneg (hp j') (hS _ _ _)) (Finset.mem_univ j)
      linarith [hr i a ha]
    rw [this]; exact le_top
  · push_neg at hA
    obtain ⟨t, ht⟩ : ∃ t : Fin N → ℝ, t = fun j => (value M j).toReal := ⟨_, rfl⟩
    have hVt : ∀ j, 0 < M.transition i a j → value M j = (t j : EReal) := by
      intro j hj
      rw [ht]
      exact (EReal.coe_toReal (hA j hj)
        (ne_bot_of_le_ne_bot EReal.zero_ne_bot (value_nonneg hr j))).symm
    have hterm : ∀ j, (M.transition i a j : EReal) * value M j =
        ((M.transition i a j * t j : ℝ) : EReal) := by
      intro j
      rcases (hp j).lt_or_eq with hj | hj
      · rw [hVt j hj, EReal.coe_mul]
      · rw [← hj]; simp
    simp only [hterm]
    rw [← ereal_coe_sum, ← EReal.coe_add]
    by_cases hVi : value M i = ⊤
    · rw [hVi]; exact le_top
    have hVi' : value M i = ((value M i).toReal : EReal) :=
      (EReal.coe_toReal hVi (ne_bot_of_le_ne_bot EReal.zero_ne_bot (value_nonneg hr i))).symm
    rw [hVi', EReal.coe_le_coe_iff]
    apply le_of_forall_pos_le_add
    intro ε hε
    have hch : ∀ j, ∃ R : Policy M, ∃ n : ℕ, 0 < M.transition i a j → t j - ε < Spart M R j n := by
      intro j
      by_cases hj : 0 < M.transition i a j
      · have h1 : ((t j - ε : ℝ) : EReal) < value M j := by
          rw [hVt j hj, EReal.coe_lt_coe_iff]; linarith
        unfold value at h1
        obtain ⟨R, hR⟩ := lt_iSup_iff.mp h1
        rw [totalReward_eq] at hR
        obtain ⟨n, hn⟩ := lt_iSup_iff.mp hR
        exact ⟨R, n, fun _ => EReal.coe_lt_coe_iff.mp hn⟩
      · exact ⟨purePolicy M (defaultRule M), 0, fun h => absurd h hj⟩
    choose Rs ns hRs using hch
    have hk := EReal.coe_le_coe_iff.mp ((key Rs (Finset.univ.sup ns)).trans hVi'.le)
    have hsum : ∑ j, M.transition i a j * t j - ε ≤
        ∑ j, M.transition i a j * Spart M (Rs j) j (Finset.univ.sup ns) := by
      have hp1 : ∑ j, M.transition i a j ≤ 1 := M.transition_subprob i a ha
      have h1 : ∑ j, M.transition i a j * (t j - ε) ≤
          ∑ j, M.transition i a j * Spart M (Rs j) j (Finset.univ.sup ns) := by
        apply Finset.sum_le_sum; intro j _
        rcases (hp j).lt_or_eq with hj | hj
        · apply mul_le_mul_of_nonneg_left _ (hp j)
          exact le_trans (hRs j hj).le (Spart_mono hr _ _ (Finset.le_sup (Finset.mem_univ j)))
        · rw [← hj]; simp
      have e : ∑ j, M.transition i a j * (t j - ε) =
          ∑ j, M.transition i a j * t j - ε * ∑ j, M.transition i a j := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      have h2 : ε * ∑ j, M.transition i a j ≤ ε := by nlinarith
      linarith
    linarith

theorem value_smallest_core
    (M : MDP N α)
    (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a) :
    (∀ i : Fin N, (0 : EReal) ≤ value M i) ∧
    (∀ i (a : α), a ∈ M.actions i →
      (↑(M.reward i a) : EReal) +
        ∑ j : Fin N, (↑(M.transition i a j) : EReal) * value M j ≤ value M i) ∧
    (∀ w : Fin N → ℝ, (∀ i, 0 ≤ w i) → IsSuperharmonic M w →
      ∀ i, value M i ≤ (↑(w i) : EReal)) :=
  ⟨value_nonneg hr, value_superharmonic hr, value_le_super⟩


theorem sum4' {A B C D : Type*} (s1 : Finset A) (s2 : Finset B) (s3 : Finset C) (s4 : Finset D)
    (F : A → B → C → D → ℝ) :
    ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, F a b c d =
      ∑ c ∈ s3, ∑ d ∈ s4, ∑ a ∈ s1, ∑ b ∈ s2, F a b c d := by
  calc _ = ∑ a ∈ s1, ∑ c ∈ s3, ∑ b ∈ s2, ∑ d ∈ s4, F a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ a ∈ s1, ∑ c ∈ s3, ∑ d ∈ s4, ∑ b ∈ s2, F a b c d :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
    _ = ∑ c ∈ s3, ∑ a ∈ s1, ∑ d ∈ s4, ∑ b ∈ s2, F a b c d := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

theorem sum4 {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → C → D → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d :=
  sum4' _ _ _ _ F

theorem fwd (n : ℕ) : ∀ (R : Policy M) (i k : Fin N),
    ∑ b, occupancy M R i k b (n+1) = ∑ j, ∑ a, occupancy M R i j a n * M.transition j a k := by
  induction n with
  | zero =>
    intro R i k
    simp only [occ_succ, occ_zero, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ite_mul, zero_mul]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp only [if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have : ∑ b, pi0 (R.cont i c) k b = 1 := Policy.choose_sum_one _ _ _
    rw [this]; ring
  | succ n ih =>
    intro R i k
    calc ∑ b, occupancy M R i k b (n+1+1)
        = ∑ c, pi0 R i c * ∑ j, M.transition i c j * ∑ b, occupancy M (R.cont i c) j k b (n+1) := by
          simp only [occ_succ (n := n+1), Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro c _
          rw [Finset.sum_comm]
      _ = ∑ c, pi0 R i c * ∑ j, M.transition i c j * ∑ j', ∑ a,
            occupancy M (R.cont i c) j j' a n * M.transition j' a k := by
          simp only [ih]
      _ = ∑ j', ∑ a, ∑ c, ∑ j, pi0 R i c * (M.transition i c j *
            (occupancy M (R.cont i c) j j' a n * M.transition j' a k)) := by
          simp only [Finset.mul_sum]
          exact sum4 (fun c j j' a => pi0 R i c * (M.transition i c j *
            (occupancy M (R.cont i c) j j' a n * M.transition j' a k)))
      _ = _ := by
          simp only [occ_succ, Finset.sum_mul, Finset.mul_sum, mul_assoc]


theorem sub_sum (i' : Fin N) (F : α → ℝ) (hF : ∀ a ∉ M.actions i', F a = 0) :
    ∑ a : M.actions i', F a.val = ∑ a, F a := by
  rw [Finset.sum_coe_sort (M.actions i') F]
  exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hF a ha)

theorem weak_dual (β : Fin N → ℝ) (hβ : ∀ j, 0 ≤ β j) (x : Flow M) (hx : IsDualOptimal M β x)
    (R : Policy M) (n : ℕ) : ∑ i, β i * Spart M R i n ≤ dualObjective M x := by
  set Y : Fin N → α → ℝ := fun j a => ∑ i, β i * ∑ t ∈ Finset.range n, occupancy M R i j a t with hYdef
  have hYout : ∀ j a, a ∉ M.actions j → Y j a = 0 := by
    intro j a ha; simp only [hYdef]
    apply Finset.sum_eq_zero; intro i _
    rw [Finset.sum_eq_zero, mul_zero]; intro t _; exact occ_outside _ _ _ _ _ ha
  let y : Flow M := fun j a => Y j a.val
  have hy : y ∈ dualFeasible M β := by
    refine ⟨fun j a => ?_, fun j => ?_⟩
    · show 0 ≤ Y j a.val
      simp only [hYdef]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hβ i)
        (Finset.sum_nonneg (fun t _ => occ_nonneg _ _ _ _ _)))
    unfold dualBalance
    rw [sub_sum j (fun a => Y j a) (hYout j)]
    rw [Finset.sum_congr rfl (fun i' _ => sub_sum i' (fun a => M.transition i' a j * Y i' a)
      (fun a ha => by simp [hYout i' a ha]))]
    have e1 : ∑ a, Y j a = ∑ i, β i * ∑ t ∈ Finset.range n, ∑ b, occupancy M R i j b t := by
      simp only [hYdef, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
    have e2 : ∑ i', ∑ a, M.transition i' a j * Y i' a =
        ∑ i, β i * ∑ t ∈ Finset.range n, ∑ b, occupancy M R i j b (t+1) := by
      simp only [fwd, hYdef, Finset.mul_sum]
      rw [sum4' Finset.univ Finset.univ Finset.univ (Finset.range n)]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro t _
      apply Finset.sum_congr rfl; intro i' _
      apply Finset.sum_congr rfl; intro a _
      ring
    rw [e1, e2, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [← mul_sub, ← Finset.sum_sub_distrib,
        Finset.sum_range_sub' (fun t => ∑ b, occupancy M R i j b t)])]
    have hq0 : ∀ i, ∑ b, occupancy M R i j b 0 = if j = i then 1 else 0 := by
      intro i
      simp only [occ_zero]
      split_ifs with h
      · exact R.choose_sum_one _ _
      · simp
    simp only [hq0, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have : 0 ≤ ∑ i, β i * ∑ b, occupancy M R i j b n :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hβ i)
        (Finset.sum_nonneg (fun b _ => occ_nonneg _ _ _ _ _)))
    linarith
  have hobj : dualObjective M y = ∑ i, β i * Spart M R i n := by
    unfold dualObjective
    rw [Finset.sum_congr rfl (fun j _ => sub_sum j (fun a => M.reward j a * Y j a)
      (fun a ha => by simp [hYout j a ha]))]
    simp only [hYdef, Spart, stageReward, Finset.mul_sum]
    rw [sum4' Finset.univ Finset.univ Finset.univ (Finset.range n)]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_subset (Finset.subset_univ (M.actions j))]
    · apply Finset.sum_congr rfl; intro a _; ring
    · intro a _ ha; rw [occ_outside _ _ _ _ _ ha]; ring
  rw [← hobj]; exact hx.2 y hy


def mixPolicy (Rs : Fin N → Policy M) : Policy M where
  choose m h b := (Rs (h.states ⟨0, by omega⟩)).choose m h b
  choose_nonneg m h b := Policy.choose_nonneg _ _ _ _
  choose_outside m h b hb := Policy.choose_outside _ _ _ _ hb
  choose_sum_one m h := Policy.choose_sum_one _ _ _

theorem Spart_mix (Rs : Fin N → Policy M) (i : Fin N) (n : ℕ) :
    Spart M (mixPolicy Rs) i n = Spart M (Rs i) i n := by
  apply Spart_congr
  intro m h hh; funext b
  show (Rs (h.states ⟨0, by omega⟩)).choose m h b = _
  rw [hh]

theorem cs_core (β : Fin N → ℝ) (x : Flow M) (hxf : x ∈ dualFeasible M β)
    (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvs : IsSuperharmonic M v)
    (hle : ∑ j, β j * v j ≤ dualObjective M x) :
    (∀ i (a : M.actions i), 0 < x i a →
      v i = M.reward i a.val + ∑ j, M.transition i a.val j * v j) ∧
    (∀ j, dualBalance M x j < β j → v j = 0) := by
  have iden : ∑ i, ∑ a : M.actions i, (v i - ∑ j, M.transition i a.val j * v j) * x i a =
      ∑ j, v j * dualBalance M x j := by
    unfold dualBalance
    simp only [sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, Finset.sum_mul]
    congr 1
    calc _ = ∑ i, ∑ j, ∑ a : M.actions i, M.transition i a.val j * v j * x i a :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ j, ∑ i, ∑ a : M.actions i, M.transition i a.val j * v j * x i a := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl; intro j _
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro a _
          ring
  set T : (i : Fin N) → M.actions i → ℝ := fun i a =>
    (v i - ∑ j, M.transition i a.val j * v j - M.reward i a.val) * x i a with hT
  have hT0 : ∀ i a, 0 ≤ T i a := by
    intro i a; simp only [hT]
    apply mul_nonneg _ (hxf.1 i a)
    have := hvs i a.val a.2; linarith
  set B : Fin N → ℝ := fun j => v j * (β j - dualBalance M x j) with hB
  have hB0 : ∀ j, 0 ≤ B j := fun j => mul_nonneg (hv0 j) (by linarith [hxf.2 j])
  have hsum : ∑ i, ∑ a : M.actions i, T i a + ∑ j, B j = ∑ j, β j * v j - dualObjective M x := by
    have e1 : ∑ i, ∑ a : M.actions i, T i a =
        ∑ j, v j * dualBalance M x j - dualObjective M x := by
      rw [← iden]; unfold dualObjective
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro a _
      simp only [hT]; ring
    have e2 : ∑ j, B j = ∑ j, β j * v j - ∑ j, v j * dualBalance M x j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      simp only [hB]; ring
    rw [e1, e2]; ring
  have hTs : 0 ≤ ∑ i, ∑ a : M.actions i, T i a :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ => hT0 i a))
  have hBs : 0 ≤ ∑ j, B j := Finset.sum_nonneg (fun j _ => hB0 j)
  have hT00 : ∑ i, ∑ a : M.actions i, T i a = 0 := by linarith
  have hB00 : ∑ j, B j = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun a _ => hT0 i a))]
    at hT00
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hB0 j)] at hB00
  constructor
  · intro i a hxa
    have h1 := hT00 i (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hT0 i a)] at h1
    have h2 := h1 a (Finset.mem_univ _)
    simp only [hT] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · linarith
  · intro j hj
    have h2 := hB00 j (Finset.mem_univ _)
    simp only [hB] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · linarith


theorem dualBalance_add (x d : Flow M) (j : Fin N) :
    dualBalance M (x + d) j = dualBalance M x j + dualBalance M d j := by
  unfold dualBalance
  simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  ring

theorem dualBalance_sub (x d : Flow M) (j : Fin N) :
    dualBalance M (x - d) j = dualBalance M x j - dualBalance M d j := by
  unfold dualBalance
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]
  ring

theorem extreme_w_zero (β : Fin N → ℝ) (x : Flow M)
    (hext : x ∈ Set.extremePoints ℝ (dualFeasible M β)) (f : PureRule M)
    (v : Fin N → ℝ) (hE : ∀ j, 0 < v j → 0 < x j ⟨f.choose j, f.admissible j⟩)
    (w : Fin N → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hwv : ∀ j, w j ≤ v j)
    (hwP : ∀ j, w j = ∑ k, M.transition j (f.choose j) k * w k) : w = 0 := by
  by_contra hne
  have hxf := hext.1
  have pnn : ∀ j k, 0 ≤ M.transition j (f.choose j) k :=
    fun j k => M.transition_nonneg _ _ _ (f.admissible j)
  set P : Matrix (Fin N) (Fin N) ℝ := fun j k =>
    if 0 < v j ∧ 0 < v k then M.transition j (f.choose j) k else 0 with hP
  have hPnn : ∀ j k, 0 ≤ P j k := by
    intro j k; simp only [hP]; split_ifs; exact pnn j k; exact le_rfl
  have hPle : ∀ j k, P j k ≤ M.transition j (f.choose j) k := by
    intro j k; simp only [hP]; split_ifs; exact le_rfl; exact pnn j k
  have hPw : Matrix.mulVec (1 - P) w = 0 := by
    funext j
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.zero_apply]
    rw [sub_eq_zero]
    show w j = ∑ k, P j k * w k
    by_cases hj : 0 < v j
    · rw [hwP j]
      apply Finset.sum_congr rfl; intro k _
      simp only [hP]
      by_cases hk : 0 < v k
      · simp [hj, hk]
      · have : w k = 0 := le_antisymm (by linarith [hwv k]) (hw0 k)
        simp [this]
    · have : w j = 0 := le_antisymm (by linarith [hwv j]) (hw0 j)
      rw [this]; symm
      apply Finset.sum_eq_zero; intro k _
      simp [hP, hj]
  have hdet : (1 - P).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hne, hPw⟩
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hyk : ∀ k, y k = ∑ j, y j * P j k := by
    intro k
    have := congrFun hy k
    simp only [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply, Pi.zero_apply] at this
    rw [sub_eq_zero] at this
    exact this
  set z : Fin N → ℝ := fun j => |y j| with hz
  have hz0 : ∀ j, 0 ≤ z j := fun j => abs_nonneg _
  have hz1 : ∀ k, z k ≤ ∑ j, z j * P j k := by
    intro k
    simp only [hz]
    rw [hyk k]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl; intro j _
    rw [abs_mul, abs_of_nonneg (hPnn j k)]
  have hrow : ∀ j, ∑ k, P j k ≤ 1 :=
    fun j => (Finset.sum_le_sum (fun k _ => hPle j k)).trans
      (M.transition_subprob _ _ (f.admissible j))
  have hswap : ∑ k, ∑ j, z j * P j k = ∑ j, z j * ∑ k, P j k := by
    rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  have hsum : ∑ k, ∑ j, z j * P j k ≤ ∑ k, z k := by
    rw [hswap]
    apply Finset.sum_le_sum; intro j _
    calc z j * ∑ k, P j k ≤ z j * 1 := mul_le_mul_of_nonneg_left (hrow j) (hz0 j)
      _ = z j := mul_one _
  have heq : ∀ k, z k = ∑ j, z j * P j k := by
    have hD : ∑ k, (∑ j, z j * P j k - z k) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg (fun k _ => by linarith [hz1 k])
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by linarith [hz1 k])] at hD
    intro k; linarith [hD k (Finset.mem_univ _)]
  have hrow1 : ∀ j, 0 < z j → ∑ k, P j k = 1 := by
    have hD : ∑ j, z j * (1 - ∑ k, P j k) = 0 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [← hswap, ← Finset.sum_congr rfl (fun k _ => heq k)]
      ring
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hz0 j) (by linarith [hrow j]))] at hD
    intro j hj
    have := hD j (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hvz : ∀ j, 0 < z j → 0 < v j := by
    intro j hj
    by_contra hvj
    have : y j = 0 := by
      rw [hyk j]
      apply Finset.sum_eq_zero; intro i _
      simp [hP, hvj]
    simp [hz, this] at hj
  have hPeq : ∀ j k, 0 < z j → M.transition j (f.choose j) k = P j k := by
    intro j k hj
    have h1 := hrow1 j hj
    have h2 := M.transition_subprob _ _ (f.admissible j)
    have hD : ∑ k, (M.transition j (f.choose j) k - P j k) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg (fun k _ => by linarith [hPle j k])
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by linarith [hPle j k])] at hD
    linarith [hD k (Finset.mem_univ _)]
  have hbal : ∀ k, z k = ∑ j, z j * M.transition j (f.choose j) k := by
    intro k
    rw [heq k]
    apply Finset.sum_congr rfl; intro j _
    rcases (hz0 j).lt_or_eq with hj | hj
    · rw [hPeq j k hj]
    · rw [← hj]; ring
  -- step size
  have hNe : Nonempty (Fin N) := ⟨⟨0, M.states_nonempty⟩⟩
  have hδj : ∀ j, ∃ δ : ℝ, 0 < δ ∧ δ * z j ≤ x j ⟨f.choose j, f.admissible j⟩ := by
    intro j
    rcases (hz0 j).lt_or_eq with hj | hj
    · have hx := hE j (hvz j hj)
      refine ⟨x j ⟨f.choose j, f.admissible j⟩ / z j, div_pos hx hj, le_of_eq ?_⟩
      field_simp
    · exact ⟨1, one_pos, by rw [← hj, mul_zero]; exact hxf.1 _ _⟩
  choose δs hδpos hδle using hδj
  set δ := Finset.univ.inf' Finset.univ_nonempty δs with hδ
  have hδ0 : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun j _ => hδpos j)
  have hδz : ∀ j, δ * z j ≤ x j ⟨f.choose j, f.admissible j⟩ := fun j =>
    le_trans (mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ j)) (hz0 j)) (hδle j)
  set d : Flow M := fun j a => if a.val = f.choose j then δ * z j else 0 with hd
  have hdsum : ∀ j (g : α → ℝ), ∑ a : M.actions j, g a.val * d j a = g (f.choose j) * (δ * z j) := by
    intro j g
    rw [sub_sum j (fun a => g a * (if a = f.choose j then δ * z j else 0))]
    · simp
    · intro a ha
      have : a ≠ f.choose j := fun h => ha (h ▸ f.admissible j)
      simp [this]
  have hdbal : ∀ k, dualBalance M d k = 0 := by
    intro k
    unfold dualBalance
    have e1 : ∑ a : M.actions k, d k a = δ * z k := by
      have := hdsum k (fun _ => 1); simpa using this
    have e2 : ∑ i, ∑ a : M.actions i, M.transition i a.val k * d i a =
        ∑ i, M.transition i (f.choose i) k * (δ * z i) :=
      Finset.sum_congr rfl (fun i _ => hdsum i (fun a => M.transition i a k))
    rw [e1, e2, hbal k, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro j _; ring
  have hdx : ∀ j (a : M.actions j), |d j a| ≤ x j a := by
    intro j a
    simp only [hd]
    split_ifs with ha
    · have : a = ⟨f.choose j, f.admissible j⟩ := Subtype.ext ha
      rw [this, abs_of_nonneg (mul_nonneg hδ0.le (hz0 j))]; exact hδz j
    · simp; exact hxf.1 j a
  have hx1 : x + d ∈ dualFeasible M β := by
    refine ⟨fun j a => ?_, fun j => ?_⟩
    · simp only [Pi.add_apply]; linarith [neg_abs_le (d j a), hdx j a]
    · rw [dualBalance_add, hdbal]; simpa using hxf.2 j
  have hx2 : x - d ∈ dualFeasible M β := by
    refine ⟨fun j a => ?_, fun j => ?_⟩
    · simp only [Pi.sub_apply]; linarith [le_abs_self (d j a), hdx j a]
    · rw [dualBalance_sub, hdbal]; simpa using hxf.2 j
  have hseg : x ∈ openSegment ℝ (x + d) (x - d) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext j a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have := ((mem_extremePoints.mp hext).2 _ hx1 _ hx2 hseg).1
  have hd0 : ∀ j, δ * z j = 0 := by
    intro j
    have := congrFun (congrFun this j) ⟨f.choose j, f.admissible j⟩
    simp only [Pi.add_apply, add_eq_left, hd] at this
    simpa using this
  apply hy0
  funext j
  have h1 := hd0 j
  rcases mul_eq_zero.mp h1 with h | h
  · linarith
  · simpa [hz] using h


theorem Policy.ext' {R1 R2 : Policy M} (h : R1.choose = R2.choose) : R1 = R2 := by
  cases R1; cases R2; cases h; rfl

theorem Spart_pure (f : PureRule M) (i : Fin N) (n : ℕ) :
    Spart M (purePolicy M f) i (n+1) = M.reward i (f.choose i) +
      ∑ j, M.transition i (f.choose i) j * Spart M (purePolicy M f) j n := by
  have hpi : ∀ c, pi0 (purePolicy M f) i c = if c = f.choose i then 1 else 0 := fun c => rfl
  have hc : ∀ c, (purePolicy M f).cont i c = purePolicy M f := by
    intro c
    apply Policy.ext'
    funext m h b
    show (if b = f.choose (h.cons i c).last then (1:ℝ) else 0) = _
    rw [cons_last]; rfl
  rw [Spart_succ]
  simp only [hpi, hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    f.admissible i]

def gseq (M : MDP N α) (f : PureRule M) (v : Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => v
  | n+1 => fun j => ∑ k, M.transition j (f.choose j) k * gseq M f v n k

theorem goal_core
    (M : MDP N α) (β : Fin N → ℝ)
    (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a)
    (hβ : ∀ j, 0 < β j)
    (x : Flow M)
    (hx : IsDualOptimal M β x)
    (hext : x ∈ Set.extremePoints ℝ (dualFeasible M β)) :
    ∀ f : PureRule M,
      (∀ i, i ∈ occupiedStates M x →
        0 < x i ⟨f.choose i, f.admissible i⟩) →
      ∀ i : Fin N, totalReward M (purePolicy M f) i = value M i := by
  intro f hf i
  have hβ0 : ∀ j, 0 ≤ β j := fun j => (hβ j).le
  have hSb : ∀ R j n, Spart M R j n ≤ dualObjective M x / β j := by
    intro R j n
    rw [le_div_iff₀ (hβ j)]
    have h1 := weak_dual β hβ0 x hx R n
    have h2 : β j * Spart M R j n ≤ ∑ i, β i * Spart M R i n :=
      Finset.single_le_sum (f := fun i => β i * Spart M R i n)
        (fun i _ => mul_nonneg (hβ0 i) (Spart_nonneg hr _ _ _)) (Finset.mem_univ j)
    linarith
  have hVle : ∀ j, value M j ≤ ((dualObjective M x / β j : ℝ) : EReal) := by
    intro j; unfold value; refine iSup_le fun R => ?_; rw [totalReward_eq]
    exact iSup_le fun n => EReal.coe_le_coe_iff.mpr (hSb R j n)
  obtain ⟨v, hvdef⟩ : ∃ v : Fin N → ℝ, v = fun j => (value M j).toReal := ⟨_, rfl⟩
  have hv : ∀ j, value M j = (v j : EReal) := by
    intro j; rw [hvdef]
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hVle j))
      (ne_bot_of_le_ne_bot EReal.zero_ne_bot (value_nonneg hr j))).symm
  have hv0 : ∀ j, 0 ≤ v j := fun j => by
    have := value_nonneg hr j; rw [hv j] at this; exact_mod_cast this
  have hvs : IsSuperharmonic M v := by
    intro j a ha
    have := value_superharmonic hr j a ha
    simp only [hv, ← EReal.coe_mul] at this
    rw [← ereal_coe_sum, ← EReal.coe_add] at this
    exact_mod_cast this
  have hlev : ∑ j, β j * v j ≤ dualObjective M x := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hBs : 0 ≤ ∑ j, β j := Finset.sum_nonneg (fun j _ => hβ0 j)
    obtain ⟨δ, hδdef⟩ : ∃ δ, δ = ε / (∑ j, β j + 1) := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδdef]; positivity
    have hδB : δ * (∑ j, β j + 1) = ε := by rw [hδdef]; field_simp
    have hch : ∀ j, ∃ R : Policy M, ∃ n : ℕ, v j - δ < Spart M R j n := by
      intro j
      have h1 : ((v j - δ : ℝ) : EReal) < value M j := by
        rw [hv j, EReal.coe_lt_coe_iff]; linarith
      unfold value at h1
      obtain ⟨R, hR⟩ := lt_iSup_iff.mp h1
      rw [totalReward_eq] at hR
      obtain ⟨n, hn⟩ := lt_iSup_iff.mp hR
      exact ⟨R, n, EReal.coe_lt_coe_iff.mp hn⟩
    choose Rs ns hRs using hch
    have h1 := weak_dual β hβ0 x hx (mixPolicy Rs) (Finset.univ.sup ns)
    simp only [Spart_mix] at h1
    have h2 : ∑ j, β j * (v j - δ) ≤ ∑ j, β j * Spart M (Rs j) j (Finset.univ.sup ns) := by
      apply Finset.sum_le_sum; intro j _
      apply mul_le_mul_of_nonneg_left _ (hβ0 j)
      exact le_trans (hRs j).le (Spart_mono hr _ _ (Finset.le_sup (Finset.mem_univ j)))
    have e : ∑ j, β j * (v j - δ) = ∑ j, β j * v j - δ * ∑ j, β j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    nlinarith
  obtain ⟨hcs1, hcs2⟩ := cs_core β x hx.1 v hv0 hvs hlev
  have hE : ∀ j, 0 < v j → 0 < x j ⟨f.choose j, f.admissible j⟩ := by
    intro j hj
    have hjE : j ∈ occupiedStates M x := by
      by_contra hn
      simp only [occupiedStates, Set.mem_setOf_eq, not_lt] at hn
      have hbal : dualBalance M x j < β j := by
        unfold dualBalance
        have : 0 ≤ ∑ i, ∑ a : M.actions i, M.transition i a.val j * x i a :=
          Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ =>
            mul_nonneg (M.transition_nonneg _ _ _ a.2) (hx.1.1 i a)))
        linarith [hβ j]
      linarith [hcs2 j hbal]
    exact hf j hjE
  have hcons : ∀ j, v j = M.reward j (f.choose j) + ∑ k, M.transition j (f.choose j) k * v k := by
    intro j
    rcases (hv0 j).lt_or_eq with hj | hj
    · exact hcs1 j ⟨f.choose j, f.admissible j⟩ (hE j hj)
    · have h0 := hvs j (f.choose j) (f.admissible j)
      have h1 := hr j _ (f.admissible j)
      have h2 : 0 ≤ ∑ k, M.transition j (f.choose j) k * v k :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (M.transition_nonneg _ _ _ (f.admissible j)) (hv0 k))
      linarith
  have pnn : ∀ j k, 0 ≤ M.transition j (f.choose j) k :=
    fun j k => M.transition_nonneg _ _ _ (f.admissible j)
  have hSg : ∀ n j, Spart M (purePolicy M f) j n = v j - gseq M f v n j := by
    intro n
    induction n with
    | zero => intro j; simp [Spart, gseq]
    | succ n ih =>
      intro j
      rw [Spart_pure]
      simp only [ih, gseq, mul_sub, Finset.sum_sub_distrib]
      linarith [hcons j]
  have hg0 : ∀ n j, 0 ≤ gseq M f v n j := by
    intro n
    induction n with
    | zero => exact hv0
    | succ n ih => intro j; exact Finset.sum_nonneg (fun k _ => mul_nonneg (pnn j k) (ih k))
  have hganti : ∀ n j, gseq M f v (n+1) j ≤ gseq M f v n j := by
    intro n
    induction n with
    | zero =>
      intro j
      show ∑ k, M.transition j (f.choose j) k * v k ≤ v j
      linarith [hcons j, hr j _ (f.admissible j)]
    | succ n ih =>
      intro j
      show ∑ k, M.transition j (f.choose j) k * gseq M f v (n+1) k ≤
        ∑ k, M.transition j (f.choose j) k * gseq M f v n k
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (ih k) (pnn j k))
  set w : Fin N → ℝ := fun j => ⨅ n, gseq M f v n j with hw
  have hbdd : ∀ j, BddBelow (Set.range fun n => gseq M f v n j) :=
    fun j => ⟨0, by rintro _ ⟨n, rfl⟩; exact hg0 n j⟩
  have hT : ∀ j, Filter.Tendsto (fun n => gseq M f v n j) Filter.atTop (nhds (w j)) := by
    intro j
    exact tendsto_atTop_ciInf (antitone_nat_of_succ_le (fun n => hganti n j)) (hbdd j)
  have hw0 : ∀ j, 0 ≤ w j := fun j => le_ciInf (fun n => hg0 n j)
  have hwv : ∀ j, w j ≤ v j := fun j => ciInf_le (hbdd j) 0
  have hwP : ∀ j, w j = ∑ k, M.transition j (f.choose j) k * w k := by
    intro j
    have h1 : Filter.Tendsto (fun n => gseq M f v (n+1) j) Filter.atTop (nhds (w j)) :=
      (hT j).comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun n => gseq M f v (n+1) j) Filter.atTop
        (nhds (∑ k, M.transition j (f.choose j) k * w k)) := by
      show Filter.Tendsto (fun n => ∑ k, M.transition j (f.choose j) k * gseq M f v n k) _ _
      exact tendsto_finset_sum _ (fun k _ => (hT k).const_mul _)
    exact tendsto_nhds_unique h1 h2
  have hw00 := extreme_w_zero β x hext f v hE w hw0 hwv hwP
  have hwi : w i = 0 := by rw [hw00]; rfl
  apply le_antisymm
  · exact le_iSup (fun R => totalReward M R i) _
  · rw [hv i, totalReward_eq]
    have ht : Filter.Tendsto (fun n => Spart M (purePolicy M f) i n) Filter.atTop (nhds (v i)) := by
      simp only [hSg]
      have := (tendsto_const_nhds (x := v i)).sub (hT i)
      rwa [hwi, sub_zero] at this
    exact le_of_tendsto' (EReal.tendsto_coe.mpr ht) (fun n => le_iSup (fun n =>
      ((Spart M (purePolicy M f) i n : ℝ) : EReal)) n)

end KallenbergLP.Positive

open KallenbergLP.Positive


theorem solution
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (β : Fin N → ℝ)
    (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a)
    (hβ : ∀ j, 0 < β j)
    (x : Flow M)
    (hx : IsDualOptimal M β x)
    (hext : x ∈ Set.extremePoints ℝ (dualFeasible M β)) :
    ∀ f : PureRule M,
      (∀ i, i ∈ occupiedStates M x →
        0 < x i ⟨f.choose i, f.admissible i⟩) →
      ∀ i : Fin N, totalReward M (purePolicy M f) i = value M i := by
  exact goal_core M β hr hβ x hx hext
