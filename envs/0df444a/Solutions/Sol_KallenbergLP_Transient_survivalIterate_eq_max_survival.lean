-- Prove2me | solution 1 for KallenbergLP.Transient.survivalIterate_eq_max_survival
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:08:02.22699+00:00
-- url     : https://prove2.me/submissions/892d4fa9-4261-4fde-9fa0-3e7fb68c5a52

import Mathlib
import Definitions.Def_KallenbergLP_Transient_Criteria
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

end KallenbergLP.Transient

open KallenbergLP.Transient


theorem solution
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (f : ℕ → PureRule M) (R₀ : Policy M)
    (hf : ∀ t : ℕ, 0 < t → ∀ i : Fin N,
      survivalIterate M t i =
        ∑ j : Fin N, M.transition i ((f t).choose i) j * survivalIterate M (t - 1) j) :
    ∀ (t : ℕ) (i : Fin N),
      survivalIterate M t i = survivalProb M (extremalPolicy M f R₀ t) i t ∧
        ∀ R : Policy M, survivalProb M R i t ≤ survivalIterate M t i := by
  exact kt_surv_core M f R₀ hf
