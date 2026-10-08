-- Prove2me | solution 1 for KallenbergLP.Positive.value_smallest_nonnegative_superharmonic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:51:45.258558+00:00
-- url     : https://prove2.me/submissions/ac8abf83-b5cd-47e4-b0e8-e06f684820c9

import Definitions.Def_KallenbergLP_Positive_Value



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

end KallenbergLP.Positive

open KallenbergLP.Positive


theorem solution
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α] (M : MDP N α)
    (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a) :
    (∀ i : Fin N, (0 : EReal) ≤ value M i) ∧
    (∀ i (a : α), a ∈ M.actions i →
      (↑(M.reward i a) : EReal) +
        ∑ j : Fin N, (↑(M.transition i a j) : EReal) * value M j ≤ value M i) ∧
    (∀ w : Fin N → ℝ, (∀ i, 0 ≤ w i) → IsSuperharmonic M w →
      ∀ i, value M i ≤ (↑(w i) : EReal)) := by
  exact value_smallest_core M hr
