-- Prove2me | solution 1 for KallenbergLP.Transient.dermanStrauch
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:10:49.593976+00:00
-- url     : https://prove2.me/submissions/b70bf2cd-65ea-4ca6-a424-8ac61c3b18d3

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

lemma kt_summ (w : ℕ → ℝ) (hw₀ : ∀ k, 0 ≤ w k) (hw : Summable w) (X : ℕ → ℝ)
    (h0 : ∀ k, 0 ≤ X k) (h1 : ∀ k, X k ≤ 1) : Summable (fun k => w k * X k) :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (hw₀ k) (h0 k))
    (fun k => mul_le_of_le_one_right (hw₀ k) (h1 k)) hw

lemma kt_bocc_bounds (M : MDP N α) (β : Fin N → ℝ) (hβ₀ : ∀ i, 0 ≤ β i)
    (hβ₁ : (∑ i : Fin N, β i) = 1) (R : Policy M) (j : Fin N) (a : α) (n : ℕ) :
    0 ≤ ∑ i, β i * occupancy M R i j a n ∧ ∑ i, β i * occupancy M R i j a n ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hβ₀ i) (kt_occ_nonneg _ _ _ _ _ _)
  · calc ∑ i, β i * occupancy M R i j a n ≤ ∑ i, β i * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (le_trans (kt_occ_le_st _ _ _ _ _ _) (kt_st_le_one _ _ _ _ _)) (hβ₀ i)
      _ = 1 := by simp [hβ₁]

lemma kt_bst_bounds (M : MDP N α) (β : Fin N → ℝ) (hβ₀ : ∀ i, 0 ≤ β i)
    (hβ₁ : (∑ i : Fin N, β i) = 1) (R : Policy M) (j : Fin N) (n : ℕ) :
    0 ≤ ∑ i, β i * stateProb M R i j n ∧ ∑ i, β i * stateProb M R i j n ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hβ₀ i) (kt_st_nonneg _ _ _ _ _)
  · calc ∑ i, β i * stateProb M R i j n ≤ ∑ i, β i * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (kt_st_le_one _ _ _ _ _) (hβ₀ i)
      _ = 1 := by simp [hβ₁]

noncomputable def ktO (M : MDP N α) (β : Fin N → ℝ) (R : ℕ → Policy M) (w : ℕ → ℝ)
    (n : ℕ) (j : Fin N) (a : α) : ℝ :=
  ∑' k, w k * ∑ i, β i * occupancy M (R k) i j a n

noncomputable def ktD (M : MDP N α) (β : Fin N → ℝ) (R : ℕ → Policy M) (w : ℕ → ℝ)
    (n : ℕ) (j : Fin N) : ℝ :=
  ∑' k, w k * ∑ i, β i * stateProb M (R k) i j n

section DS
variable (M : MDP N α) (β : Fin N → ℝ) (hβ₀ : ∀ i, 0 ≤ β i)
    (hβ₁ : (∑ i : Fin N, β i) = 1) (R : ℕ → Policy M) (w : ℕ → ℝ)
    (hw₀ : ∀ k, 0 ≤ w k) (hw₁ : HasSum w 1)

include hβ₀ hβ₁ hw₀ hw₁

lemma kt_O_summ (n : ℕ) (j : Fin N) (a : α) :
    Summable (fun k => w k * ∑ i, β i * occupancy M (R k) i j a n) :=
  kt_summ w hw₀ hw₁.summable _ (fun k => (kt_bocc_bounds M β hβ₀ hβ₁ (R k) j a n).1)
    (fun k => (kt_bocc_bounds M β hβ₀ hβ₁ (R k) j a n).2)

lemma kt_D_summ (n : ℕ) (j : Fin N) :
    Summable (fun k => w k * ∑ i, β i * stateProb M (R k) i j n) :=
  kt_summ w hw₀ hw₁.summable _ (fun k => (kt_bst_bounds M β hβ₀ hβ₁ (R k) j n).1)
    (fun k => (kt_bst_bounds M β hβ₀ hβ₁ (R k) j n).2)

lemma kt_O_nonneg (n : ℕ) (j : Fin N) (a : α) : 0 ≤ ktO M β R w n j a :=
  tsum_nonneg fun k => mul_nonneg (hw₀ k) (kt_bocc_bounds M β hβ₀ hβ₁ (R k) j a n).1

lemma kt_D_nonneg (n : ℕ) (j : Fin N) : 0 ≤ ktD M β R w n j :=
  tsum_nonneg fun k => mul_nonneg (hw₀ k) (kt_bst_bounds M β hβ₀ hβ₁ (R k) j n).1

lemma kt_O_le_D (n : ℕ) (j : Fin N) (a : α) : ktO M β R w n j a ≤ ktD M β R w n j := by
  unfold ktO ktD
  refine Summable.tsum_le_tsum (fun k => ?_) (kt_O_summ M β hβ₀ hβ₁ R w hw₀ hw₁ n j a)
    (kt_D_summ M β hβ₀ hβ₁ R w hw₀ hw₁ n j)
  apply mul_le_mul_of_nonneg_left _ (hw₀ k)
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (kt_occ_le_st _ _ _ _ _ _) (hβ₀ i)

lemma kt_O_outside (n : ℕ) (j : Fin N) (a : α) (ha : a ∉ M.actions j) :
    ktO M β R w n j a = 0 := by
  unfold ktO
  simp [kt_occ_outside _ _ _ _ _ _ ha]

lemma kt_O_sum (n : ℕ) (j : Fin N) : ∑ a, ktO M β R w n j a = ktD M β R w n j := by
  unfold ktO ktD
  rw [← Summable.tsum_finsetSum (fun a _ => kt_O_summ M β hβ₀ hβ₁ R w hw₀ hw₁ n j a)]
  apply tsum_congr; intro k
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.mul_sum, kt_occ_sum]

end DS

noncomputable def ktq (M : MDP N α) (β : Fin N → ℝ) (R : ℕ → Policy M) (w : ℕ → ℝ)
    (n : ℕ) (j : Fin N) (a : α) : ℝ :=
  if 0 < ktD M β R w n j then ktO M β R w n j a / ktD M β R w n j
  else if a = (M.actions_nonempty j).choose then 1 else 0

lemma kt_derman_core
    (M : MDP N α) (β : Fin N → ℝ) (hβ₀ : ∀ i, 0 ≤ β i)
    (hβ₁ : (∑ i : Fin N, β i) = 1)
    (R : ℕ → Policy M) (w : ℕ → ℝ)
    (hw₀ : ∀ k, 0 ≤ w k) (hw₁ : HasSum w 1) :
    ∃ Q : Policy M, Memoryless M Q ∧
      ∀ (t : ℕ) (j : Fin N) (a : α), a ∈ M.actions j →
        (∑ i : Fin N, β i * occupancy M Q i j a t) =
          ∑' k : ℕ, w k *
            (∑ i : Fin N, β i * occupancy M (R k) i j a t) := by
  let q := ktq M β R w
  have q_nonneg : ∀ n j a, 0 ≤ q n j a := by
    intro n j a
    simp only [q, ktq]
    split_ifs with h
    · exact div_nonneg (kt_O_nonneg M β hβ₀ hβ₁ R w hw₀ hw₁ n j a) h.le
    · norm_num
    · norm_num
  have q_out : ∀ n j a, a ∉ M.actions j → q n j a = 0 := by
    intro n j a ha
    simp only [q, ktq]
    split_ifs with h h2
    · rw [kt_O_outside M β hβ₀ hβ₁ R w hw₀ hw₁ n j a ha, zero_div]
    · exact absurd (h2 ▸ (M.actions_nonempty j).choose_spec) ha
    · rfl
  have q_sum : ∀ n j, ∑ a, q n j a = 1 := by
    intro n j
    simp only [q, ktq]
    split_ifs with h
    · rw [← Finset.sum_div, kt_O_sum M β hβ₀ hβ₁ R w hw₀ hw₁ n j, div_self h.ne']
    · simp
  let Q : Policy M :=
    { choose := fun n h a => q n h.last a
      choose_nonneg := fun n h a => q_nonneg n h.last a
      choose_outside := fun n h a ha => q_out n h.last a ha
      choose_sum_one := fun n h => q_sum n h.last }
  have hQ : ∀ n (h : History N α n) a, Q.choose n h a = q n h.last a := fun _ _ _ => rfl
  have occQ : ∀ i j a n, occupancy M Q i j a n = stateProb M Q i j n * q n j a :=
    fun i j a n => kt_occ_memoryless M Q q hQ i j a n
  have claim : ∀ n j, ∑ i, β i * stateProb M Q i j n = ktD M β R w n j := by
    intro n
    induction n with
    | zero =>
      intro j
      simp only [ktD, kt_st_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [tsum_mul_right, hw₁.tsum_eq, one_mul]
    | succ n ih =>
      have hO : ∀ j a, ∑ i, β i * occupancy M Q i j a n = ktO M β R w n j a := by
        intro j a
        simp only [occQ, ← mul_assoc, ← Finset.sum_mul, ih]
        simp only [q, ktq]
        split_ifs with h
        · field_simp
        · have h0 : ktD M β R w n j = 0 :=
            le_antisymm (not_lt.mp h) (kt_D_nonneg M β hβ₀ hβ₁ R w hw₀ hw₁ n j)
          have : ktO M β R w n j a = 0 := le_antisymm
            (h0 ▸ kt_O_le_D M β hβ₀ hβ₁ R w hw₀ hw₁ n j a) (kt_O_nonneg M β hβ₀ hβ₁ R w hw₀ hw₁ n j a)
          rw [h0, this, zero_mul]
        · have h0 : ktD M β R w n j = 0 :=
            le_antisymm (not_lt.mp h) (kt_D_nonneg M β hβ₀ hβ₁ R w hw₀ hw₁ n j)
          have : ktO M β R w n j a = 0 := le_antisymm
            (h0 ▸ kt_O_le_D M β hβ₀ hβ₁ R w hw₀ hw₁ n j a) (kt_O_nonneg M β hβ₀ hβ₁ R w hw₀ hw₁ n j a)
          rw [h0, this, zero_mul]
      intro j'
      have e1 : ∀ R' : Policy M, ∑ i, β i * stateProb M R' i j' (n+1) =
          ∑ j, ∑ a, (∑ i, β i * occupancy M R' i j a n) * M.transition j a j' := by
        intro R'
        simp only [kt_st_succ, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro i _
        ring
      rw [e1 Q]
      simp only [hO]
      unfold ktD ktO
      simp only [e1]
      have hs : ∀ j a, Summable (fun k => w k * (∑ i, β i * occupancy M (R k) i j a n) *
          M.transition j a j') := fun j a =>
        (kt_O_summ M β hβ₀ hβ₁ R w hw₀ hw₁ n j a).mul_right _
      simp only [← tsum_mul_right]
      symm
      have hk : ∀ k, w k * ∑ j, ∑ a, (∑ i, β i * occupancy M (R k) i j a n) * M.transition j a j'
          = ∑ j, ∑ a, (w k * ∑ i, β i * occupancy M (R k) i j a n) * M.transition j a j' := by
        intro k
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        ring
      rw [tsum_congr hk, Summable.tsum_finsetSum (fun j _ => summable_sum fun a _ => hs j a)]
      apply Finset.sum_congr rfl; intro j _
      rw [Summable.tsum_finsetSum (fun a _ => hs j a)]
  refine ⟨Q, ⟨q, hQ⟩, ?_⟩
  intro t j a _
  show _ = ktO M β R w t j a
  simp only [occQ, ← mul_assoc, ← Finset.sum_mul, claim]
  simp only [q, ktq]
  have hOD : ¬ 0 < ktD M β R w t j → ktD M β R w t j = 0 ∧ ktO M β R w t j a = 0 := by
    intro h
    have h0 : ktD M β R w t j = 0 :=
      le_antisymm (not_lt.mp h) (kt_D_nonneg M β hβ₀ hβ₁ R w hw₀ hw₁ t j)
    exact ⟨h0, le_antisymm (h0 ▸ kt_O_le_D M β hβ₀ hβ₁ R w hw₀ hw₁ t j a)
      (kt_O_nonneg M β hβ₀ hβ₁ R w hw₀ hw₁ t j a)⟩
  split_ifs with h
  · field_simp
  · rw [(hOD h).1, (hOD h).2, zero_mul]
  · rw [(hOD h).1, (hOD h).2, zero_mul]

lemma kt_markov_core (M : MDP N α) (i : Fin N) (R : Policy M) :
    ∃ R₀ : Policy M, Memoryless M R₀ ∧
      ∀ (t : ℕ) (j : Fin N) (a : α), a ∈ M.actions j →
        occupancy M R₀ i j a t = occupancy M R i j a t := by
  obtain ⟨Q, hQ, h⟩ := kt_derman_core M (fun k => if k = i then 1 else 0)
    (fun k => by split_ifs <;> norm_num) (by simp) (fun _ => R)
    (fun k => if k = 0 then 1 else 0) (fun k => by split_ifs <;> norm_num)
    (hasSum_ite_eq 0 1)
  refine ⟨Q, hQ, fun t j a ha => ?_⟩
  have := h t j a ha
  simpa [ite_mul, tsum_ite_eq] using this

end KallenbergLP.Transient

open KallenbergLP.Transient


theorem solution
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (β : Fin N → ℝ) (hβ₀ : ∀ i, 0 ≤ β i)
    (hβ₁ : (∑ i : Fin N, β i) = 1)
    (R : ℕ → Policy M) (w : ℕ → ℝ)
    (hw₀ : ∀ k, 0 ≤ w k) (hw₁ : HasSum w 1) :
    ∃ Q : Policy M, Memoryless M Q ∧
      ∀ (t : ℕ) (j : Fin N) (a : α), a ∈ M.actions j →
        (∑ i : Fin N, β i * occupancy M Q i j a t) =
          ∑' k : ℕ, w k *
            (∑ i : Fin N, β i * occupancy M (R k) i j a t) := by
  exact kt_derman_core M β hβ₀ hβ₁ R w hw₀ hw₁
