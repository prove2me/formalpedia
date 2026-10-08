-- Prove2me | solution 1 for KallenbergLP.Transient.transientPureStationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:17:39.429901+00:00
-- url     : https://prove2.me/submissions/4b2a2e21-071f-45eb-8158-2f42472c516a

import Mathlib
import Definitions.Def_KallenbergLP_Transient_Criteria
import Definitions.Def_KallenbergLP_Transient_Policy
set_option autoImplicit false


namespace KallenbergLP.Transient

set_option linter.unusedSectionVars false
variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

def kt_hext {n : ℕ} (h : History N α n) (a : α) (j : Fin N) : History N α (n+1) :=
  ⟨Fin.snoc (α := fun _ => Fin N) h.states j, Fin.snoc (α := fun _ => α) h.chosen a⟩

def kt_histEquiv (n : ℕ) : History N α n × α × Fin N ≃ History N α (n+1) where
  toFun p := kt_hext p.1 p.2.1 p.2.2
  invFun H := (⟨Fin.init H.states, Fin.init H.chosen⟩, H.chosen (Fin.last n),
    H.states (Fin.last (n+1)))
  left_inv := by rintro ⟨⟨s, c⟩, a, j⟩; simp [kt_hext]
  right_inv := by rintro ⟨s, c⟩; simp [kt_hext]

lemma kt_hext_last {n : ℕ} (h : History N α n) (a : α) (j : Fin N) :
    (kt_hext h a j).last = j := by
  simp [History.last, kt_hext, Fin.snoc]

lemma kt_hext_prefix_cast {n : ℕ} (h : History N α n) (a : α) (j : Fin N) (k : Fin n) :
    (kt_hext h a j).prefix (Fin.castSucc k) = h.prefix k := by
  simp only [History.prefix, kt_hext]
  congr 1
  · funext i
    have : i.val < n + 1 := by omega
    simp [Fin.snoc, this]
  · funext i
    have : i.val < n := by omega
    simp [Fin.snoc, this]

lemma kt_hext_prefix_last {n : ℕ} (h : History N α n) (a : α) (j : Fin N) :
    (kt_hext h a j).prefix (Fin.last n) = h := by
  rcases h with ⟨s, c⟩
  simp only [History.prefix, kt_hext]
  congr 1
  · funext i
    have : i.val < n + 1 := by omega
    simp [Fin.snoc, this]
  · funext i
    have : i.val < n := by omega
    simp [Fin.snoc, this]

lemma kt_historyProb_hext (M : MDP N α) (R : Policy M) (i : Fin N) {n : ℕ}
    (h : History N α n) (a : α) (j : Fin N) :
    historyProb M R i (n+1) (kt_hext h a j) =
      historyProb M R i n h * (R.choose n h a * M.transition h.last a j) := by
  unfold historyProb
  rw [Fin.prod_univ_castSucc, ← mul_assoc]
  have h0 : (kt_hext h a j).states ⟨0, by omega⟩ = h.states ⟨0, by omega⟩ := by
    simp [kt_hext, Fin.snoc]
  have hP : ∀ k : Fin n, R.choose (Fin.castSucc k).val ((kt_hext h a j).prefix (Fin.castSucc k))
      ((kt_hext h a j).chosen (Fin.castSucc k)) *
      M.transition ((kt_hext h a j).states ⟨(Fin.castSucc k).val, by omega⟩)
        ((kt_hext h a j).chosen (Fin.castSucc k))
        ((kt_hext h a j).states ⟨(Fin.castSucc k).val + 1, by omega⟩) =
      R.choose k.val (h.prefix k) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k) (h.states ⟨k.val + 1, by omega⟩) := by
    intro k
    rw [kt_hext_prefix_cast]
    have hk1 : k.val < n + 1 := by omega
    have hk2 : k.val + 1 < n + 1 := by omega
    simp [kt_hext, Fin.snoc, hk1, hk2, k.isLt]
  have hL : R.choose (Fin.last n).val ((kt_hext h a j).prefix (Fin.last n))
      ((kt_hext h a j).chosen (Fin.last n)) *
      M.transition ((kt_hext h a j).states ⟨(Fin.last n).val, by omega⟩)
        ((kt_hext h a j).chosen (Fin.last n))
        ((kt_hext h a j).states ⟨(Fin.last n).val + 1, by omega⟩) =
      R.choose n h a * M.transition h.last a j := by
    rw [kt_hext_prefix_last]
    simp [kt_hext, Fin.snoc, History.last]
  rw [h0, Finset.prod_congr rfl (fun k _ => hP k), hL]

lemma kt_historyProb_nonneg (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ)
    (h : History N α n) : 0 ≤ historyProb M R i n h := by
  unfold historyProb
  apply mul_nonneg
  · split_ifs <;> norm_num
  · apply Finset.prod_nonneg
    intro k _
    by_cases ha : h.chosen k ∈ M.actions (h.prefix k).last
    · exact mul_nonneg (R.choose_nonneg _ _ _) (M.transition_nonneg _ _ _ ha)
    · rw [R.choose_outside _ _ _ ha, zero_mul]

lemma kt_occ_nonneg (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α) (n : ℕ) :
    0 ≤ occupancy M R i j a n := by
  unfold occupancy
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact mul_nonneg (kt_historyProb_nonneg M R i n h) (R.choose_nonneg _ _ _)
  · exact le_refl _

lemma kt_st_nonneg (M : MDP N α) (R : Policy M) (i j : Fin N) (n : ℕ) :
    0 ≤ stateProb M R i j n := by
  unfold stateProb
  apply Finset.sum_nonneg
  intro h _
  split_ifs
  · exact kt_historyProb_nonneg M R i n h
  · exact le_refl _

lemma kt_occ_outside (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α) (n : ℕ)
    (ha : a ∉ M.actions j) : occupancy M R i j a n = 0 := by
  unfold occupancy
  apply Finset.sum_eq_zero
  intro h _
  split_ifs with hj
  · rw [R.choose_outside _ _ _ (by rw [hj]; exact ha), mul_zero]
  · rfl

lemma kt_occ_sum (M : MDP N α) (R : Policy M) (i j : Fin N) (n : ℕ) :
    ∑ a, occupancy M R i j a n = stateProb M R i j n := by
  unfold occupancy stateProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs
  · rw [← Finset.mul_sum, R.choose_sum_one, mul_one]
  · simp

lemma kt_st_succ (M : MDP N α) (R : Policy M) (i j' : Fin N) (n : ℕ) :
    stateProb M R i j' (n+1) =
      ∑ j, ∑ a, occupancy M R i j a n * M.transition j a j' := by
  unfold stateProb
  rw [← (kt_histEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [kt_histEquiv, Equiv.coe_fn_mk, kt_hext_last, kt_historyProb_hext]
  simp only [Fintype.sum_prod_type, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold occupancy
  have key : ∀ x : History N α n, ∑ j, ∑ a, (if x.last = j then
      historyProb M R i n x * R.choose n x a * M.transition j a j' else 0) =
      ∑ a, historyProb M R i n x * (R.choose n x a * M.transition x.last a j') := by
    intro x
    rw [Finset.sum_eq_single x.last]
    · simp only [if_true]; apply Finset.sum_congr rfl; intro a _; ring
    · intro b _ hb; apply Finset.sum_eq_zero; intro a _; rw [if_neg (Ne.symm hb)]
    · simp

  rw [← Finset.sum_congr rfl (fun x _ => key x)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro x _
  split_ifs <;> simp

lemma kt_st_zero (M : MDP N α) (R : Policy M) (i j : Fin N) :
    stateProb M R i j 0 = if j = i then 1 else 0 := by
  unfold stateProb historyProb
  let e : History N α 0 ≃ Fin N :=
    { toFun := fun h => h.states 0
      invFun := fun k => ⟨fun _ => k, Fin.elim0⟩
      left_inv := by
        rintro ⟨s, c⟩
        dsimp only
        congr 1
        · funext x; fin_cases x; rfl
        · funext x; exact Fin.elim0 x
      right_inv := by intro k; rfl }
  rw [← e.symm.sum_comp]
  simp [e, History.last]

/-- push-forward identity -/
lemma kt_push (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) (g : Fin N → ℝ) :
    ∑ j', stateProb M R i j' (n+1) * g j' =
      ∑ j, ∑ a, occupancy M R i j a n * ∑ j', M.transition j a j' * g j' := by
  simp only [kt_st_succ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro j' _
  ring

/-- drift inequality -/
lemma kt_drift (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) (g hh : Fin N → ℝ)
    (hg : ∀ j a, a ∈ M.actions j → ∑ j', M.transition j a j' * g j' ≤ hh j) :
    ∑ j', stateProb M R i j' (n+1) * g j' ≤ ∑ j, stateProb M R i j n * hh j := by
  rw [kt_push]
  apply Finset.sum_le_sum; intro j _
  rw [← kt_occ_sum, Finset.sum_mul]
  apply Finset.sum_le_sum; intro a _
  by_cases ha : a ∈ M.actions j
  · exact mul_le_mul_of_nonneg_left (hg j a ha) (kt_occ_nonneg _ _ _ _ _ _)
  · simp [kt_occ_outside M R i j a n ha]

lemma kt_mass_le (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) :
    ∑ j, stateProb M R i j n ≤ 1 := by
  induction n with
  | zero => simp [kt_st_zero]
  | succ n ih =>
    have := kt_drift M R i n (fun _ => 1) (fun _ => 1) (by
      intro j a ha; simpa using M.transition_subprob j a ha)
    simp only [mul_one] at this
    linarith

lemma kt_st_le_one (M : MDP N α) (R : Policy M) (i j : Fin N) (n : ℕ) :
    stateProb M R i j n ≤ 1 :=
  le_trans (Finset.single_le_sum (f := fun j => stateProb M R i j n)
    (fun k _ => kt_st_nonneg M R i k n) (Finset.mem_univ j)) (kt_mass_le M R i n)

lemma kt_occ_le_st (M : MDP N α) (R : Policy M) (i j : Fin N) (a : α) (n : ℕ) :
    occupancy M R i j a n ≤ stateProb M R i j n := by
  rw [← kt_occ_sum]
  exact Finset.single_le_sum (f := fun a => occupancy M R i j a n)
    (fun b _ => kt_occ_nonneg M R i j b n) (Finset.mem_univ a)

lemma kt_occ_memoryless (M : MDP N α) (R : Policy M) (q : ℕ → Fin N → α → ℝ)
    (hq : ∀ n (h : History N α n) a, R.choose n h a = q n h.last a)
    (i j : Fin N) (a : α) (n : ℕ) :
    occupancy M R i j a n = stateProb M R i j n * q n j a := by
  unfold occupancy stateProb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs with hj
  · rw [hq, hj]
  · simp

lemma kt_occ_pure (M : MDP N α) (f : PureRule M) (i j : Fin N) (a : α) (n : ℕ) :
    occupancy M (purePolicy M f) i j a n =
      if a = f.choose j then stateProb M (purePolicy M f) i j n else 0 := by
  rw [kt_occ_memoryless M (purePolicy M f) (fun _ j a => if a = f.choose j then 1 else 0)
    (fun _ _ _ => rfl)]
  split_ifs <;> simp

lemma kt_w_le (M : MDP N α) (t : ℕ) (i : Fin N) (a : α) (ha : a ∈ M.actions i) :
    ∑ j, M.transition i a j * survivalIterate M t j ≤ survivalIterate M (t+1) i := by
  rw [survivalIterate]
  exact Finset.le_sup' (fun a => ∑ j, M.transition i a j * survivalIterate M t j) ha

theorem kt_surv_core (M : MDP N α) (f : ℕ → PureRule M) (R₀ : Policy M)
    (hf : ∀ t : ℕ, 0 < t → ∀ i : Fin N,
      survivalIterate M t i =
        ∑ j : Fin N, M.transition i ((f t).choose i) j * survivalIterate M (t - 1) j) :
    ∀ (t : ℕ) (i : Fin N),
      survivalIterate M t i = survivalProb M (extremalPolicy M f R₀ t) i t ∧
        ∀ R : Policy M, survivalProb M R i t ≤ survivalIterate M t i := by
  intro t i
  constructor
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [extremalPolicy, survivalProb, survivalIterate, kt_st_zero]
    · have hE : extremalPolicy M f R₀ t = backwardPolicy M f t := by
        simp [extremalPolicy, ht.ne']
      rw [hE]
      have key : ∀ k, k ≤ t → ∑ j, stateProb M (backwardPolicy M f t) i j t =
          ∑ j, stateProb M (backwardPolicy M f t) i j (t - k) * survivalIterate M k j := by
        intro k
        induction k with
        | zero => intro _; simp [survivalIterate]
        | succ k ih =>
          intro hk
          rw [ih (by omega)]
          have ht' : t - k = (t - (k+1)) + 1 := by omega
          rw [ht', kt_push]
          apply Finset.sum_congr rfl; intro j _
          rw [hf (k+1) (by omega) j]
          have hlt : t - (k+1) < t := by omega
          have hsub : t - (t - (k+1)) = k + 1 := by omega
          have hocc : ∀ a, occupancy M (backwardPolicy M f t) i j a (t - (k+1)) =
              stateProb M (backwardPolicy M f t) i j (t - (k+1)) *
                (if a = (f (k+1)).choose j then 1 else 0) := by
            intro a
            rw [kt_occ_memoryless M _ (fun n j a =>
              if a = (f (if n < t then t - n else 1)).choose j then 1 else 0) (fun _ _ _ => rfl)]
            simp only [if_pos hlt, hsub]
          simp only [hocc, Nat.add_sub_cancel]
          simp [Finset.sum_ite_eq']
      have := key t le_rfl
      simp only [Nat.sub_self, kt_st_zero] at this
      unfold survivalProb; rw [this]; simp
  · intro R
    have key : ∀ k, k ≤ t → ∑ j, stateProb M R i j t ≤
        ∑ j, stateProb M R i j (t - k) * survivalIterate M k j := by
      intro k
      induction k with
      | zero => intro _; simp [survivalIterate]
      | succ k ih =>
        intro hk
        refine le_trans (ih (by omega)) ?_
        have ht' : t - k = (t-(k+1))+1 := by omega
        rw [ht']
        exact kt_drift M R i _ _ _ (fun j a ha => kt_w_le M k j a ha)
    have := key t le_rfl
    simp only [Nat.sub_self, kt_st_zero] at this
    unfold survivalProb; simpa using this

lemma kt_w_succ (M : MDP N α) (t : ℕ) (i : Fin N) :
    survivalIterate M (t+1) i = (M.actions i).sup' (M.actions_nonempty i)
      (fun a => ∑ j, M.transition i a j * survivalIterate M t j) := by
  rw [survivalIterate]

lemma kt_w_bounds (M : MDP N α) : ∀ t i, 0 ≤ survivalIterate M t i ∧ survivalIterate M t i ≤ 1 := by
  intro t
  induction t with
  | zero => intro i; simp [survivalIterate]
  | succ t ih =>
    intro i
    rw [kt_w_succ]
    obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup' (M.actions_nonempty i)
      (fun a => ∑ j, M.transition i a j * survivalIterate M t j)
    rw [he]
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (M.transition_nonneg i a j ha) (ih j).1
    · calc ∑ j, M.transition i a j * survivalIterate M t j ≤ ∑ j, M.transition i a j :=
            Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (M.transition_nonneg i a j ha) (ih j).2
        _ ≤ 1 := M.transition_subprob i a ha

lemma kt_w_anti (M : MDP N α) : ∀ t i, survivalIterate M (t+1) i ≤ survivalIterate M t i := by
  intro t
  induction t with
  | zero => intro i; simpa [survivalIterate] using (kt_w_bounds M 1 i).2
  | succ t ih =>
    intro i
    rw [kt_w_succ M (t+1), kt_w_succ M t]
    exact Finset.sup'_le _ _ fun a ha => Finset.le_sup'_of_le _ ha
      (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (M.transition_nonneg i a j ha))

def KtClosed (M : MDP N α) (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∃ a ∈ M.actions i, ∑ j ∈ S, M.transition i a j = 1

lemma kt_sum_ind (S : Finset (Fin N)) (g : Fin N → ℝ) :
    ∑ j, g j * (if j ∈ S then (1:ℝ) else 0) = ∑ j ∈ S, g j := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma kt_nontransient_of_closed (M : MDP N α) (S : Finset (Fin N)) (hne : S.Nonempty)
    (hS : KtClosed M S) : ∃ f : PureRule M, ¬ IsTransient M (purePolicy M f) := by
  classical
  let g : Fin N → α := fun i =>
    if h : i ∈ S then (hS i h).choose else (M.actions_nonempty i).choose
  have hg : ∀ i, g i ∈ M.actions i := by
    intro i
    by_cases h : i ∈ S
    · simp only [g, dif_pos h]; exact (hS i h).choose_spec.1
    · simp only [g, dif_neg h]; exact (M.actions_nonempty i).choose_spec
  have hgS : ∀ i ∈ S, ∑ j ∈ S, M.transition i (g i) j = 1 := by
    intro i h
    simp only [g, dif_pos h]; exact (hS i h).choose_spec.2
  let f : PureRule M := ⟨g, hg⟩
  obtain ⟨i0, hi0⟩ := hne
  have key : ∀ n, 1 ≤ ∑ j ∈ S, stateProb M (purePolicy M f) i0 j n := by
    intro n
    induction n with
    | zero => simp [kt_st_zero, hi0]
    | succ n ih =>
      rw [← kt_sum_ind, kt_push]
      calc (1:ℝ) ≤ ∑ j ∈ S, stateProb M (purePolicy M f) i0 j n := ih
        _ = ∑ j ∈ S, ∑ a, occupancy M (purePolicy M f) i0 j a n *
              ∑ j', M.transition j a j' * (if j' ∈ S then (1:ℝ) else 0) := by
            apply Finset.sum_congr rfl; intro j hj
            simp only [kt_occ_pure, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
            rw [kt_sum_ind]
            have : f.choose j = g j := rfl
            rw [this, hgS j hj, mul_one]
        _ ≤ ∑ j, ∑ a, occupancy M (purePolicy M f) i0 j a n *
              ∑ j', M.transition j a j' * (if j' ∈ S then (1:ℝ) else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            intro j _ _
            apply Finset.sum_nonneg; intro a _
            by_cases ha : a ∈ M.actions j
            · exact mul_nonneg (kt_occ_nonneg _ _ _ _ _ _) (Finset.sum_nonneg fun j' _ =>
                mul_nonneg (M.transition_nonneg j a j' ha) (by split_ifs <;> norm_num))
            · simp [kt_occ_outside _ _ _ _ _ _ ha]
  refine ⟨f, fun hT => ?_⟩
  have hs : Summable (fun n => ∑ j ∈ S, stateProb M (purePolicy M f) i0 j n) :=
    summable_sum fun j _ => hT i0 j
  obtain ⟨n, hn⟩ := (hs.tendsto_atTop_zero.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))).exists
  linarith [key n, show ∑ j ∈ S, stateProb M (purePolicy M f) i0 j n < 1 from hn]

lemma kt_closed_of_not_lt (M : MDP N α) (h : ¬ ∀ i, survivalIterate M N i < 1) :
    ∃ S : Finset (Fin N), S.Nonempty ∧ KtClosed M S := by
  classical
  push_neg at h
  obtain ⟨i1, hi1⟩ := h
  let S : ℕ → Finset (Fin N) := fun t => Finset.univ.filter (fun i => survivalIterate M t i = 1)
  have hmem : ∀ t i, i ∈ S t ↔ survivalIterate M t i = 1 := by simp [S]
  have hsub : ∀ t, S (t+1) ⊆ S t := by
    intro t i hi
    rw [hmem] at hi ⊢
    exact le_antisymm (kt_w_bounds M t i).2 (hi ▸ kt_w_anti M t i)
  have hanti : ∀ s t, s ≤ t → S t ⊆ S s := by
    intro s t hst
    induction hst with
    | refl => exact subset_rfl
    | step _ ih => exact (hsub _).trans ih
  have hN : i1 ∈ S N := (hmem N i1).2 (le_antisymm (kt_w_bounds M N i1).2 hi1)
  have hex : ∃ k, k < N ∧ S (k+1) = S k := by
    by_contra hc
    push_neg at hc
    have hcard : ∀ k, k ≤ N → (S k).card + k ≤ N := by
      intro k
      induction k with
      | zero => intro _; simpa using Finset.card_le_univ (S 0)
      | succ k ih =>
        intro hk
        have h1 := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub k, hc k (by omega)⟩)
        have h2 := ih (by omega)
        omega
    have h1 := hcard N le_rfl
    have h2 : 0 < (S N).card := Finset.card_pos.2 ⟨i1, hN⟩
    omega
  obtain ⟨k, hk, hkeq⟩ := hex
  refine ⟨S k, ⟨i1, hanti k N hk.le hN⟩, ?_⟩
  intro i hi
  rw [← hkeq, hmem, kt_w_succ] at hi
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup' (M.actions_nonempty i)
    (fun a => ∑ j, M.transition i a j * survivalIterate M k j)
  rw [he] at hi
  refine ⟨a, ha, ?_⟩
  have hd : ∀ j, 0 ≤ M.transition i a j * (1 - survivalIterate M k j) := fun j =>
    mul_nonneg (M.transition_nonneg i a j ha) (by linarith [(kt_w_bounds M k j).2])
  have hsum : ∑ j, M.transition i a j * (1 - survivalIterate M k j) = 0 := by
    have h1 := M.transition_subprob i a ha
    have h2 : ∑ j, M.transition i a j * (1 - survivalIterate M k j) =
        ∑ j, M.transition i a j - ∑ j, M.transition i a j * survivalIterate M k j := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
    have h3 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hd j)
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd j)).1 hsum
  rw [← hi]
  show ∑ j ∈ Finset.univ.filter _, _ = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro j _
  split_ifs with hj
  · rw [hj, mul_one]
  · have h0 := hz j (Finset.mem_univ j)
    have hlt : survivalIterate M k j < 1 := lt_of_le_of_ne (kt_w_bounds M k j).2 hj
    have : M.transition i a j = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exfalso; linarith
    rw [this, zero_mul]

lemma kt_contracting_of_lt (M : MDP N α) (h : ∀ i, survivalIterate M N i < 1) : Contracting M := by
  have hN : 0 < N := M.states_nonempty
  obtain ⟨i1, _, hi1⟩ := Finset.exists_max_image Finset.univ (fun i => survivalIterate M N i)
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hρ : survivalIterate M N i1 < 1 := h i1
  have hρ0 : 0 ≤ survivalIterate M N i1 := (kt_w_bounds M N i1).1
  generalize hr : survivalIterate M N i1 = ρ at hρ hρ0 hi1
  let μ : Fin N → ℝ := fun i => ∑ t ∈ Finset.range N, survivalIterate M t i
  have hμ1 : ∀ i, 1 ≤ μ i := by
    intro i
    have := Finset.single_le_sum (f := fun t => survivalIterate M t i)
      (fun t _ => (kt_w_bounds M t i).1) (Finset.mem_range.2 hN)
    simpa [survivalIterate] using this
  have hμN : ∀ i, μ i ≤ N := by
    intro i
    calc μ i ≤ ∑ t ∈ Finset.range N, (1:ℝ) := Finset.sum_le_sum fun t _ => (kt_w_bounds M t i).2
      _ = N := by simp
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨μ, 1 - (1 - ρ) / N, fun i => by linarith [hμ1 i], ?_, ?_, ?_⟩
  · have : (1 - ρ) / N ≤ 1 := by rw [div_le_one hNr]; linarith
    linarith
  · have : 0 < (1 - ρ) / N := div_pos (by linarith) hNr
    linarith
  · intro i a ha
    have step : ∑ j, M.transition i a j * μ j ≤ ∑ t ∈ Finset.range N, survivalIterate M (t+1) i := by
      simp only [μ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun t _ => kt_w_le M t i a ha
    have tele : ∑ t ∈ Finset.range N, survivalIterate M (t+1) i = μ i - 1 + survivalIterate M N i := by
      have h1 := Finset.sum_range_succ' (fun t => survivalIterate M t i) N
      have h2 := Finset.sum_range_succ (fun t => survivalIterate M t i) N
      have hw0 : survivalIterate M 0 i = 1 := rfl
      simp only [μ]
      linarith
    have h3 : (1 - ρ) * μ i / N ≤ 1 - ρ := by
      rw [div_le_iff₀ hNr]; nlinarith [hμN i]
    have h4 : (1 - (1 - ρ) / N) * μ i = μ i - (1 - ρ) * μ i / N := by ring
    rw [h4]
    linarith [hi1 i (Finset.mem_univ i)]

lemma kt_transient_of_weight (M : MDP N α) (R : Policy M) (μ : Fin N → ℝ) (c : ℝ)
    (hμ : ∀ i, 0 < μ i) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (H : ∀ i n j a, occupancy M R i j a n * ∑ k, M.transition j a k * μ k ≤
      occupancy M R i j a n * (c * μ j)) : IsTransient M R := by
  intro i j
  have hE : ∀ n, ∑ k, stateProb M R i k n * μ k ≤ c ^ n * μ i := by
    intro n
    induction n with
    | zero => simp [kt_st_zero]
    | succ n ih =>
      rw [kt_push]
      calc _ ≤ ∑ j, ∑ a, occupancy M R i j a n * (c * μ j) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ => H i n j a
        _ = c * ∑ k, stateProb M R i k n * μ k := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
            rw [← Finset.sum_mul, kt_occ_sum]; ring
        _ ≤ c * (c^n * μ i) := mul_le_mul_of_nonneg_left ih hc0
        _ = c^(n+1) * μ i := by ring
  have hb : ∀ n, stateProb M R i j n ≤ (μ i / μ j) * c ^ n := by
    intro n
    have h1 : stateProb M R i j n * μ j ≤ c ^ n * μ i :=
      le_trans (Finset.single_le_sum (f := fun k => stateProb M R i k n * μ k)
        (fun k _ => mul_nonneg (kt_st_nonneg _ _ _ _ _) (hμ k).le) (Finset.mem_univ j)) (hE n)
    rw [div_mul_eq_mul_div, le_div_iff₀ (hμ j)]; linarith
  exact Summable.of_nonneg_of_le (fun n => kt_st_nonneg _ _ _ _ _) hb
    ((summable_geometric_of_lt_one hc0 hc1).mul_left _)

lemma kt_transient_of_contracting (M : MDP N α) (h : Contracting M) (R : Policy M) :
    IsTransient M R := by
  obtain ⟨μ, c, hμ, hc0, hc1, hC⟩ := h
  apply kt_transient_of_weight M R μ c hμ hc0 hc1
  intro i n j a
  by_cases ha : a ∈ M.actions j
  · exact mul_le_mul_of_nonneg_left (hC j a ha) (kt_occ_nonneg _ _ _ _ _ _)
  · simp [kt_occ_outside _ _ _ _ _ _ ha]

lemma kt_transient_of_LP (M : MDP N α) (β : Fin N → ℝ) (hβ : ∀ j, 0 < β j)
    (h : LPFinite M β) (R : Policy M) : IsTransient M R := by
  obtain ⟨xs, _, hopt⟩ := h
  have hN : 0 < N := M.states_nonempty
  obtain ⟨j1, _, hj1⟩ := Finset.exists_min_image Finset.univ β ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hmb : 0 < β j1 := hβ j1
  generalize hmbd : β j1 = mb at hmb hj1
  intro i0 j0
  have e : ∀ k j', ∑ i, ∑ a ∈ M.actions i, M.transition i a j' * occupancy M R i0 i a k =
      stateProb M R i0 j' (k+1) := by
    intro k j'
    rw [kt_st_succ]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_subset (Finset.subset_univ (M.actions i))]
    · apply Finset.sum_congr rfl; intro a _; ring
    · intro a _ ha; simp [kt_occ_outside _ _ _ _ _ _ ha]
  have e2 : ∀ k j', ∑ a ∈ M.actions j', occupancy M R i0 j' a k = stateProb M R i0 j' k := by
    intro k j'
    rw [← kt_occ_sum]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha; exact kt_occ_outside _ _ _ _ _ _ ha
  let x : ℕ → Fin N → α → ℝ := fun n j a => mb * ∑ k ∈ Finset.range n, occupancy M R i0 j a k
  have hfeas : ∀ n, LPFeasible M β (x n) := by
    intro n
    constructor
    · intro i a _
      exact mul_nonneg hmb.le (Finset.sum_nonneg fun k _ => kt_occ_nonneg _ _ _ _ _ _)
    · intro j
      have hA : ∑ i, ∑ a ∈ M.actions i, (if i = j then (1:ℝ) else 0) * x n i a =
          mb * ∑ k ∈ Finset.range n, stateProb M R i0 j k := by
        rw [Finset.sum_eq_single j]
        · simp only [if_true, one_mul, x]
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl; intro k _; exact e2 k j
        · intro b _ hb; simp [hb]
        · simp
      have hB : ∑ i, ∑ a ∈ M.actions i, M.transition i a j * x n i a =
          mb * ∑ k ∈ Finset.range n, stateProb M R i0 j (k+1) := by
        have h1 : ∀ i a, M.transition i a j * x n i a =
            mb * ∑ k ∈ Finset.range n, M.transition i a j * occupancy M R i0 i a k := by
          intro i a; simp only [x, Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
        simp only [h1, ← Finset.mul_sum]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
        apply Finset.sum_congr rfl; intro k _; exact e k j
      simp only [sub_mul, Finset.sum_sub_distrib, hA, hB]
      rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_sub', kt_st_zero]
      have h0 := kt_st_nonneg M R i0 j n
      have := hj1 j (Finset.mem_univ j)
      split_ifs <;> nlinarith
  have hobj : ∀ n, LPObjective M (x n) =
      mb * ∑ k ∈ Finset.range n, ∑ j, stateProb M R i0 j k := by
    intro n
    unfold LPObjective
    simp only [x, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    exact e2 k j
  have hsum : Summable (fun k => ∑ j, stateProb M R i0 j k) := by
    apply summable_of_sum_range_le (c := LPObjective M xs / mb)
    · intro k; exact Finset.sum_nonneg fun j _ => kt_st_nonneg _ _ _ _ _
    · intro n
      rw [le_div_iff₀ hmb, mul_comm, ← hobj]
      exact hopt _ (hfeas n)
  exact Summable.of_nonneg_of_le (fun k => kt_st_nonneg _ _ _ _ _)
    (fun k => Finset.single_le_sum (f := fun j => stateProb M R i0 j k)
      (fun j _ => kt_st_nonneg _ _ _ _ _) (Finset.mem_univ j0)) hsum

lemma kt_cont_lin (c : Fin N → α → ℝ) (s : Fin N → Finset α) :
    Continuous (fun x : Fin N → α → ℝ => ∑ i, ∑ a ∈ s i, c i a * x i a) :=
  continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun a _ =>
    continuous_const.mul ((continuous_apply a).comp (continuous_apply i))

lemma kt_LP_of_contracting (M : MDP N α) (β : Fin N → ℝ) (hβ : ∀ j, 0 < β j)
    (h : Contracting M) : LPFinite M β := by
  classical
  obtain ⟨μ, c, hμ, hc0, hc1, hC⟩ := h
  have hN : 0 < N := M.states_nonempty
  obtain ⟨j1, _, hj1⟩ := Finset.exists_min_image Finset.univ μ ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hm : 0 < μ j1 := hμ j1
  generalize hmd : μ j1 = m at hm hj1
  have hcm : 0 < (1 - c) * m := mul_pos (by linarith) hm
  set B := (∑ j, β j * μ j) / ((1 - c) * m) with hBdef
  have hbound : ∀ x, LPFeasible M β x → LPObjective M x ≤ B := by
    intro x hxf
    obtain ⟨hx0, hx⟩ := hxf
    have key : ∑ j, μ j * (∑ i, ∑ a ∈ M.actions i,
        ((if i = j then (1:ℝ) else 0) - M.transition i a j) * x i a) ≤ ∑ j, β j * μ j :=
      Finset.sum_le_sum fun j _ => by
        rw [mul_comm (β j)]; exact mul_le_mul_of_nonneg_left (hx j) (hμ j).le
    have lhs : ∑ j, μ j * (∑ i, ∑ a ∈ M.actions i,
        ((if i = j then (1:ℝ) else 0) - M.transition i a j) * x i a) =
        ∑ i, ∑ a ∈ M.actions i, x i a * (μ i - ∑ j, M.transition i a j * μ j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
      have : ∀ j, μ j * (((if i = j then (1:ℝ) else 0) - M.transition i a j) * x i a) =
          x i a * (if i = j then μ j else 0) - x i a * (M.transition i a j * μ j) := by
        intro j; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]; ring
    have low : (1 - c) * m * LPObjective M x ≤
        ∑ i, ∑ a ∈ M.actions i, x i a * (μ i - ∑ j, M.transition i a j * μ j) := by
      unfold LPObjective
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro a ha
      have h1 := hC i a ha
      have h2 := hj1 i (Finset.mem_univ i)
      have h3 := hx0 i a ha
      nlinarith [mul_nonneg h3 (sub_nonneg.2 h2), mul_nonneg h3 (sub_nonneg.2 hc1.le)]
    rw [hBdef, le_div_iff₀ hcm]
    linarith
  let K : Set (Fin N → α → ℝ) :=
    (⋂ i, ⋂ a ∈ M.actions i, {x | 0 ≤ x i a}) ∩
    (⋂ j, {x | ∑ i, ∑ a ∈ M.actions i,
        ((if i = j then (1:ℝ) else 0) - M.transition i a j) * x i a ≤ β j}) ∩
    (⋂ i, ⋂ a ∈ (M.actions i)ᶜ, {x | x i a = 0})
  have hKmem : ∀ x, x ∈ K ↔ LPFeasible M β x ∧ ∀ i a, a ∉ M.actions i → x i a = 0 := by
    intro x
    simp only [K, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_compl,
      LPFeasible]
  have hKc : IsClosed K := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun i => isClosed_biInter fun a _ =>
        isClosed_le continuous_const ((continuous_apply a).comp (continuous_apply i))
    · exact isClosed_iInter fun j => isClosed_le (kt_cont_lin _ _) continuous_const
    · exact isClosed_iInter fun i => isClosed_biInter fun a _ =>
        isClosed_eq ((continuous_apply a).comp (continuous_apply i)) continuous_const
  have hKsub : K ⊆ Set.Icc 0 (fun _ _ => B) := by
    intro x hx
    rw [hKmem] at hx
    obtain ⟨hf, hz⟩ := hx
    constructor
    · intro i a
      by_cases ha : a ∈ M.actions i
      · exact hf.1 i a ha
      · simp [hz i a ha]
    · intro i a
      by_cases ha : a ∈ M.actions i
      · refine le_trans ?_ (hbound x hf)
        unfold LPObjective
        refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ a ∈ M.actions i, x i a)
          (fun i _ => Finset.sum_nonneg fun a ha => hf.1 i a ha) (Finset.mem_univ i))
        exact Finset.single_le_sum (f := fun a => x i a) (fun a ha => hf.1 i a ha) ha
      · show x i a ≤ B
        rw [hz i a ha]
        have : 0 ≤ ∑ j, β j * μ j :=
          Finset.sum_nonneg fun j _ => mul_nonneg (hβ j).le (hμ j).le
        exact div_nonneg this hcm.le
  have hcomp : IsCompact K := isCompact_Icc.of_isClosed_subset hKc hKsub
  have hne : K.Nonempty := by
    refine ⟨0, (hKmem 0).2 ⟨⟨fun _ _ _ => le_refl _, fun j => ?_⟩, fun _ _ _ => rfl⟩⟩
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact (hβ j).le
  obtain ⟨xs, hxs, hmax⟩ := hcomp.exists_isMaxOn hne
    (kt_cont_lin (fun _ _ => (1:ℝ)) M.actions).continuousOn
  refine ⟨xs, ((hKmem xs).1 hxs).1, fun y hy => ?_⟩
  let y' : Fin N → α → ℝ := fun i a => if a ∈ M.actions i then y i a else 0
  have hy' : y' ∈ K := by
    rw [hKmem]
    refine ⟨⟨fun i a ha => ?_, fun j => ?_⟩, fun i a ha => ?_⟩
    · simp only [y', if_pos ha]; exact hy.1 i a ha
    · refine le_trans (le_of_eq ?_) (hy.2 j)
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro a ha
      simp only [y', if_pos ha]
    · simp only [y', if_neg ha]
  have hobj : LPObjective M y = ∑ i, ∑ a ∈ M.actions i, (1:ℝ) * y' i a := by
    unfold LPObjective
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro a ha
    simp only [y', if_pos ha, one_mul]
  have hxs' : LPObjective M xs = ∑ i, ∑ a ∈ M.actions i, (1:ℝ) * xs i a := by
    unfold LPObjective; simp
  rw [hobj, hxs']
  exact hmax hy'

theorem kt_five_core (M : MDP N α) (β : Fin N → ℝ) (hβ : ∀ j, 0 < β j) :
    ((∀ f : PureRule M, IsTransient M (purePolicy M f)) ↔
       (∀ R : Policy M, IsTransient M R)) ∧
    ((∀ R : Policy M, IsTransient M R) ↔
       (∀ i : Fin N, survivalIterate M N i < 1)) ∧
    ((∀ i : Fin N, survivalIterate M N i < 1) ↔ Contracting M) ∧
    (Contracting M ↔ LPFinite M β) := by
  have p13 : (∀ f : PureRule M, IsTransient M (purePolicy M f)) →
      (∀ i : Fin N, survivalIterate M N i < 1) := by
    intro hP
    by_contra hc
    obtain ⟨S, hne, hS⟩ := kt_closed_of_not_lt M hc
    obtain ⟨f, hf⟩ := kt_nontransient_of_closed M S hne hS
    exact hf (hP f)
  have p34 := kt_contracting_of_lt M
  have p42 := kt_transient_of_contracting M
  have p21 : (∀ R : Policy M, IsTransient M R) →
      (∀ f : PureRule M, IsTransient M (purePolicy M f)) := fun h f => h _
  have p45 := kt_LP_of_contracting M β hβ
  have p52 := kt_transient_of_LP M β hβ
  refine ⟨⟨fun h => p42 (p34 (p13 h)), p21⟩, ⟨fun h => p13 (p21 h), fun h => p42 (p34 h)⟩,
    ⟨p34, fun h => p13 (p21 (p42 h))⟩, ⟨p45, fun h => p34 (p13 (p21 (p52 h)))⟩⟩

def ktU (M : MDP N α) : ℕ → Fin N → ℝ
  | 0, _ => 0
  | t + 1, i => 1 + (M.actions i).inf' (M.actions_nonempty i)
      (fun a => ∑ j, M.transition i a j * ktU M t j)

lemma kt_U_succ (M : MDP N α) (t : ℕ) (i : Fin N) :
    ktU M (t+1) i = 1 + (M.actions i).inf' (M.actions_nonempty i)
      (fun a => ∑ j, M.transition i a j * ktU M t j) := by
  rw [ktU]

lemma kt_U_nonneg (M : MDP N α) : ∀ t i, 0 ≤ ktU M t i := by
  intro t
  induction t with
  | zero => intro i; simp [ktU]
  | succ t ih =>
    intro i
    rw [kt_U_succ]
    have : 0 ≤ (M.actions i).inf' (M.actions_nonempty i)
        (fun a => ∑ j, M.transition i a j * ktU M t j) :=
      Finset.le_inf' _ _ fun a ha => Finset.sum_nonneg fun j _ =>
        mul_nonneg (M.transition_nonneg i a j ha) (ih j)
    linarith

lemma kt_U_mono (M : MDP N α) : ∀ t i, ktU M t i ≤ ktU M (t+1) i := by
  intro t
  induction t with
  | zero => intro i; simpa [ktU] using kt_U_nonneg M 1 i
  | succ t ih =>
    intro i
    rw [kt_U_succ M (t+1), kt_U_succ M t]
    have : (M.actions i).inf' (M.actions_nonempty i) (fun a => ∑ j, M.transition i a j * ktU M t j)
        ≤ (M.actions i).inf' (M.actions_nonempty i) (fun a => ∑ j, M.transition i a j * ktU M (t+1) j) :=
      Finset.le_inf' _ _ fun a ha => Finset.inf'_le_of_le _ ha
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (M.transition_nonneg i a j ha))
    linarith

lemma kt_U_mono' (M : MDP N α) (i : Fin N) : Monotone (fun t => ktU M t i) :=
  monotone_nat_of_le_succ fun t => kt_U_mono M t i

lemma kt_drift_ge (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) (g hh : Fin N → ℝ)
    (hg : ∀ j a, a ∈ M.actions j → hh j ≤ ∑ j', M.transition j a j' * g j') :
    ∑ j, stateProb M R i j n * hh j ≤ ∑ j', stateProb M R i j' (n+1) * g j' := by
  rw [kt_push]
  apply Finset.sum_le_sum; intro j _
  rw [← kt_occ_sum, Finset.sum_mul]
  apply Finset.sum_le_sum; intro a _
  by_cases ha : a ∈ M.actions j
  · exact mul_le_mul_of_nonneg_left (hg j a ha) (kt_occ_nonneg _ _ _ _ _ _)
  · simp [kt_occ_outside M R i j a n ha]

lemma kt_U_le (M : MDP N α) (R : Policy M) (i : Fin N) (t : ℕ) :
    ktU M t i ≤ ∑ n ∈ Finset.range t, ∑ j, stateProb M R i j n := by
  have key : ∀ k, k ≤ t → ktU M t i ≤ ∑ n ∈ Finset.range k, ∑ j, stateProb M R i j n +
      ∑ j, stateProb M R i j k * ktU M (t - k) j := by
    intro k
    induction k with
    | zero => intro _; simp [kt_st_zero]
    | succ k ih =>
      intro hk
      refine le_trans (ih (by omega)) ?_
      have ht' : t - k = (t - (k+1)) + 1 := by omega
      rw [ht', Finset.sum_range_succ]
      have := kt_drift_ge M R i k (ktU M (t - (k+1))) (fun j => ktU M (t - (k+1) + 1) j - 1)
        (by
          intro j a ha
          rw [kt_U_succ]
          have := Finset.inf'_le (fun a => ∑ j', M.transition j a j' * ktU M (t - (k+1)) j') ha
          linarith)
      have e : ∑ j, stateProb M R i j k * (ktU M (t - (k+1) + 1) j - 1) =
          ∑ j, stateProb M R i j k * ktU M (t - (k+1) + 1) j - ∑ j, stateProb M R i j k := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
      linarith
  have := key t le_rfl
  simpa [ktU] using this

theorem kt_tps_core (M : MDP N α) (h : ∃ R : Policy M, IsTransient M R) :
    ∃ f : PureRule M, IsTransient M (purePolicy M f) := by
  classical
  obtain ⟨R, hR⟩ := h
  have hN : 0 < N := M.states_nonempty
  let V : Fin N → ℝ := fun i => ∑ j, ∑' n, stateProb M R i j n
  have hUV : ∀ t i, ktU M t i ≤ V i := by
    intro t i
    refine le_trans (kt_U_le M R i t) ?_
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ =>
      (hR i j).sum_le_tsum _ (fun n _ => kt_st_nonneg _ _ _ _ _)
  have hbdd : ∀ i, BddAbove (Set.range fun t => ktU M t i) := fun i =>
    ⟨V i, by rintro _ ⟨t, rfl⟩; exact hUV t i⟩
  let u : Fin N → ℝ := fun i => ⨆ t, ktU M t i
  have hle : ∀ t i, ktU M t i ≤ u i := fun t i => le_ciSup (hbdd i) t
  have htend : ∀ i, Filter.Tendsto (fun t => ktU M t i) Filter.atTop (nhds (u i)) :=
    fun i => tendsto_atTop_ciSup (kt_U_mono' M i) (hbdd i)
  have hact : ∀ i, ∃ a ∈ M.actions i, ∑ j, M.transition i a j * u j ≤ u i - 1 := by
    intro i
    have hex : ∃ a ∈ M.actions i, ∀ t, ∑ j, M.transition i a j * ktU M t j ≤ u i - 1 := by
      by_contra hc
      push_neg at hc
      choose! T hT using hc
      let T0 := (M.actions i).sup T
      have h1 : ∀ a ∈ M.actions i, u i - 1 < ∑ j, M.transition i a j * ktU M T0 j := by
        intro a ha
        refine lt_of_lt_of_le (hT a ha) ?_
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (kt_U_mono' M j (Finset.le_sup ha)) (M.transition_nonneg i a j ha)
      have h2 : u i - 1 < (M.actions i).inf' (M.actions_nonempty i)
          (fun a => ∑ j, M.transition i a j * ktU M T0 j) :=
        (Finset.lt_inf'_iff _).2 h1
      have h3 := hle (T0+1) i
      rw [kt_U_succ] at h3
      linarith
    obtain ⟨a, ha, hat⟩ := hex
    refine ⟨a, ha, ?_⟩
    have ht : Filter.Tendsto (fun t => ∑ j, M.transition i a j * ktU M t j) Filter.atTop
        (nhds (∑ j, M.transition i a j * u j)) :=
      tendsto_finset_sum _ fun j _ => (htend j).const_mul _
    exact le_of_tendsto' ht hat
  choose g hg hgu using hact
  let f : PureRule M := ⟨g, hg⟩
  have hu1 : ∀ i, 1 ≤ u i := by
    intro i
    refine le_trans ?_ (hle 1 i)
    rw [kt_U_succ]
    have : 0 ≤ (M.actions i).inf' (M.actions_nonempty i)
        (fun a => ∑ j, M.transition i a j * ktU M 0 j) :=
      Finset.le_inf' _ _ fun a ha => Finset.sum_nonneg fun j _ =>
        mul_nonneg (M.transition_nonneg i a j ha) (kt_U_nonneg M 0 j)
    linarith
  obtain ⟨i1, _, hi1⟩ := Finset.exists_max_image Finset.univ u ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hM1 : 1 ≤ u i1 := hu1 i1
  have hMpos : 0 < u i1 := by linarith
  refine ⟨f, kt_transient_of_weight M (purePolicy M f) u (1 - 1 / u i1)
    (fun i => by linarith [hu1 i]) ?_ ?_ ?_⟩
  · have : 1 / u i1 ≤ 1 := by rw [div_le_one hMpos]; exact hM1
    linarith
  · have : 0 < 1 / u i1 := by positivity
    linarith
  · intro i n j a
    rw [kt_occ_pure]
    split_ifs with hfa
    · apply mul_le_mul_of_nonneg_left _ (kt_st_nonneg _ _ _ _ _)
      have h1 := hgu j
      have hfa' : a = g j := hfa
      rw [hfa']
      have h2 : u j / u i1 ≤ 1 := by rw [div_le_one hMpos]; exact hi1 j (Finset.mem_univ j)
      have h3 : (1 - 1 / u i1) * u j = u j - u j / u i1 := by ring
      rw [h3]; linarith
    · simp

end KallenbergLP.Transient

open KallenbergLP.Transient


theorem solution
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α)
    (h : ∃ R : Policy M, IsTransient M R) :
    ∃ f : PureRule M, IsTransient M (purePolicy M f) := by
  exact kt_tps_core M h
