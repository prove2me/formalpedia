-- Prove2me | solution 1 for JohnsonApprox.MaxSatGreedy.halt_sub_ge_k_left
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:21:44.034969+00:00
-- url     : https://prove2.me/submissions/ea78fc5e-3962-4c6b-9360-d15c53b71581

import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1
import Definitions.Def_JohnsonApprox_MaxSatGreedy_ExampleK3
import Mathlib



namespace JohnsonApprox.MaxSatGreedy

open Finset Shared

lemma neg_neg (l : Literal) : l.neg.neg = l := by
  cases l with | mk v p => simp [Literal.neg]

lemma neg_var (l : Literal) : l.neg.var = l.var := rfl

lemma neg_eq_iff (l y : Literal) : l.neg = y ↔ l = y.neg := by
  constructor
  · rintro rfl; rw [neg_neg]
  · rintro rfl; rw [neg_neg]

lemma same_var (l l' : Literal) (h : l'.var = l.var) : l' = l ∨ l' = l.neg := by
  cases l with | mk v p =>
  cases l' with | mk v' p' =>
  simp only [Literal.neg, Literal.mk.injEq] at h ⊢
  subst h
  cases p <;> cases p' <;> simp

lemma neg_ne (l : Literal) : l.neg ≠ l := by
  cases l with | mk v p => cases p <;> simp [Literal.neg]

/-- The number of wounds of a clause: literals whose negation has been set true. -/
def wounds (T : Finset Literal) (C : Clause) : ℕ := (C.filter (fun l => l.neg ∈ T)).card

def W (σ : State) : ℕ := ∑ C ∈ σ.LEFT, wounds σ.TRUE C

/-- Invariants of reachable states. -/
lemma inv (S : Finset Clause) (σ : State) (hσ : Reachable S σ) :
    Disjoint σ.SUB σ.LEFT ∧ σ.SUB ∪ σ.LEFT = S ∧ (∀ l ∈ σ.TRUE, l.var ∈ σ.decided) ∧
      (∀ v ∈ σ.decided, ∃ l ∈ σ.TRUE, l.var = v) ∧ (∀ C ∈ σ.LEFT, ∀ l ∈ C, l ∉ σ.TRUE) ∧
      W σ ≤ σ.SUB.card := by
  induction hσ with
  | refl =>
    refine ⟨disjoint_empty_left _, empty_union _, by simp [init], by simp [init], by simp [init], ?_⟩
    simp [W, init, wounds]
  | @tail σ₁ σ₂ _ hstep ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    obtain ⟨y, _, hyLIT, hmax, rfl⟩ := hstep
    have hyT : y ∉ σ₁.TRUE := fun hy => hyLIT (h3 y hy)
    have hYTsub : σ₁.YT y ⊆ σ₁.LEFT := filter_subset _ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Disjoint (σ₁.SUB ∪ σ₁.YT y) (σ₁.LEFT \ σ₁.YT y)
      rw [disjoint_union_left]
      exact ⟨disjoint_of_subset_right sdiff_subset h1, disjoint_sdiff⟩
    · show σ₁.SUB ∪ σ₁.YT y ∪ (σ₁.LEFT \ σ₁.YT y) = S
      rw [union_assoc, union_sdiff_of_subset hYTsub, h2]
    · intro l hl
      rcases mem_insert.1 hl with rfl | hl
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (h3 l hl)
    · intro v hv
      rcases mem_insert.1 hv with rfl | hv
      · exact ⟨y, mem_insert_self _ _, rfl⟩
      · obtain ⟨l, hl, hlv⟩ := h4 v hv
        exact ⟨l, mem_insert_of_mem hl, hlv⟩
    · intro C hC l hl hlT
      rw [mem_sdiff] at hC
      rcases mem_insert.1 hlT with rfl | hlT
      · exact hC.2 (mem_filter.2 ⟨hC.1, hl⟩)
      · exact h5 C hC.1 l hl hlT
    · -- potential
      show ∑ C ∈ σ₁.LEFT \ σ₁.YT y, wounds (insert y σ₁.TRUE) C ≤ (σ₁.SUB ∪ σ₁.YT y).card
      rw [card_union_of_disjoint (disjoint_of_subset_right hYTsub h1)]
      have hw : ∀ C, wounds (insert y σ₁.TRUE) C ≤ wounds σ₁.TRUE C + if y.neg ∈ C then 1 else 0 := by
        intro C
        unfold wounds
        have hsub : C.filter (fun l => l.neg ∈ insert y σ₁.TRUE) ⊆
            C.filter (fun l => l.neg ∈ σ₁.TRUE) ∪ (C.filter (fun l => l = y.neg)) := by
          intro l hl
          rw [mem_filter, mem_insert] at hl
          rw [mem_union, mem_filter, mem_filter]
          rcases hl.2 with h | h
          · right; exact ⟨hl.1, (neg_eq_iff l y).1 h⟩
          · left; exact ⟨hl.1, h⟩
        refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add le_rfl ?_))
        split_ifs with hy
        · rw [filter_eq' C]; simp [hy]
        · rw [filter_eq' C]; simp [hy]
      have hsum1 : ∑ C ∈ σ₁.LEFT \ σ₁.YT y, wounds (insert y σ₁.TRUE) C ≤
          ∑ C ∈ σ₁.LEFT \ σ₁.YT y, wounds σ₁.TRUE C +
            ∑ C ∈ σ₁.LEFT \ σ₁.YT y, (if y.neg ∈ C then 1 else 0) := by
        rw [← sum_add_distrib]; exact sum_le_sum (fun C _ => hw C)
      have hsum2 : ∑ C ∈ σ₁.LEFT \ σ₁.YT y, wounds σ₁.TRUE C ≤ W σ₁ :=
        sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => Nat.zero_le _)
      have hsum3 : ∑ C ∈ σ₁.LEFT \ σ₁.YT y, (if y.neg ∈ C then 1 else 0) ≤ (σ₁.YT y).card := by
        rw [← card_filter]
        have hneg : σ₁.inLIT y.neg := hyLIT
        have := hmax y.neg hneg
        refine le_trans (card_le_card ?_) this
        intro C hC
        rw [mem_filter] at hC
        exact mem_filter.2 ⟨(mem_sdiff.1 hC.1).1, hC.2⟩
      omega

theorem saved_ge_wounded (σ σ' : State) (y : Shared.Literal) (h : StepWith σ y σ') :
    (σ'.LEFT.filter (fun C => y.neg ∈ C)).card ≤ (σ.YT y).card := by
  obtain ⟨_, hyLIT, hmax, rfl⟩ := h
  have := hmax y.neg hyLIT
  refine le_trans (card_le_card ?_) this
  intro C hC
  rw [mem_filter] at hC
  exact mem_filter.2 ⟨(mem_sdiff.1 hC.1).1, hC.2⟩

theorem halt_left_dead (S : Finset Shared.Clause) (σ : State) (hσ : Reachable S σ) (hh : Halts σ) :
    ∀ C ∈ σ.LEFT, ∀ l ∈ C, l ∉ σ.TRUE ∧ l.neg ∈ σ.TRUE := by
  obtain ⟨_, _, _, h4, h5, _⟩ := inv S σ hσ
  intro C hC l hl
  have hnot := h5 C hC l hl
  refine ⟨hnot, ?_⟩
  have hdec : l.var ∈ σ.decided := by
    have := hh C hC l hl
    unfold State.inLIT at this
    push Not at this
    exact this
  obtain ⟨l', hl', hvar⟩ := h4 _ hdec
  rcases same_var l l' hvar with rfl | rfl
  · exact absurd hl' hnot
  · exact hl'

theorem halt_sub_ge_k_left (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) (σ : State)
    (hσ : Reachable S σ) (hh : Halts σ) :
    k * σ.LEFT.card ≤ σ.SUB.card ∧ Disjoint σ.SUB σ.LEFT ∧ σ.SUB ∪ σ.LEFT = S := by
  obtain ⟨h1, h2, _, _, _, h6⟩ := inv S σ hσ
  refine ⟨?_, h1, h2⟩
  have hdead := halt_left_dead S σ hσ hh
  have hwC : ∀ C ∈ σ.LEFT, k ≤ wounds σ.TRUE C := by
    intro C hC
    have hCS : C ∈ S := by rw [← h2]; exact mem_union_right _ hC
    unfold wounds
    rw [filter_true_of_mem (fun l hl => (hdead C hC l hl).2)]
    exact hS C hCS
  calc k * σ.LEFT.card = ∑ _C ∈ σ.LEFT, k := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ C ∈ σ.LEFT, wounds σ.TRUE C := sum_le_sum hwC
    _ ≤ σ.SUB.card := h6

lemma opt_le_card (S : Finset Clause) : opt S ≤ S.card := by
  unfold opt
  apply Finset.sup'_le
  intro S' hS'
  unfold solutions at hS'
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS'
  exact card_le_card hS'.1

lemma card_le_opt (S : Finset Clause) (hsat : Satisfiable S) : S.card ≤ opt S := by
  unfold opt
  exact Finset.le_sup' Finset.card (by
    unfold solutions; simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_refl _, hsat⟩)

/-! ### Runs on inputs whose clauses are pairwise disjoint -/

def stepState (σ : State) (y : Literal) : State :=
  ⟨σ.SUB ∪ σ.YT y, σ.LEFT \ σ.YT y, insert y σ.TRUE, insert y.var σ.decided⟩

lemma count_le_one (σ : State) (hdis : ∀ C ∈ σ.LEFT, ∀ C' ∈ σ.LEFT, ∀ z, z ∈ C → z ∈ C' → C = C')
    (z : Literal) : σ.count z ≤ 1 := by
  unfold State.count State.YT
  apply card_le_one.2
  intro C hC C' hC'
  rw [mem_filter] at hC hC'
  exact hdis C hC.1 C' hC'.1 z hC.2 hC'.2

lemma step_of_disjoint (σ : State)
    (hdis : ∀ C ∈ σ.LEFT, ∀ C' ∈ σ.LEFT, ∀ z, z ∈ C → z ∈ C' → C = C')
    (y : Literal) (hy : σ.inLIT y) (C : Clause) (hC : C ∈ σ.LEFT) (hyC : y ∈ C) :
    StepWith σ y (stepState σ y) := by
  refine ⟨fun hh => hh C hC y hyC hy, hy, fun z _ => ?_, rfl⟩
  have h1 := count_le_one σ hdis z
  have h2 : 1 ≤ σ.count y := by
    unfold State.count State.YT
    exact card_pos.2 ⟨C, mem_filter.2 ⟨hC, hyC⟩⟩
  omega

theorem exampleK3_spec :
    Shared.InMS 3 exampleK3 ∧ Shared.opt exampleK3 = 4 ∧
      (∃ X, Choosable exampleK3 X ∧ X.card = 3) ∧ (∀ X, Choosable exampleK3 X → 3 ≤ X.card) := by
  have hcard : exampleK3.card = 4 := by decide
  have hdisj : ∀ C ∈ exampleK3, ∀ C' ∈ exampleK3, ∀ z, z ∈ C → z ∈ C' → C = C' := by
    have : ∀ C ∈ exampleK3, ∀ C' ∈ exampleK3, C ≠ C' → Disjoint C C' := by decide
    intro C hC C' hC' z hz hz'
    by_contra hne
    exact Finset.disjoint_left.1 (this C hC C' hC' hne) hz hz'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C hC
    have : ∀ C ∈ exampleK3, 3 ≤ C.card := by decide
    exact this C hC
  · apply le_antisymm (hcard ▸ opt_le_card _)
    rw [← hcard]
    apply card_le_opt
    refine ⟨⟨{l | l.pos = true}, fun l hl hneg => ?_⟩, fun C hC => ?_⟩
    · simp only [Set.mem_setOf_eq, Literal.neg] at hl hneg
      rw [hl] at hneg; exact Bool.noConfusion hneg
    · simp only [exampleK3, mem_insert, mem_singleton] at hC
      rcases hC with rfl | rfl | rfl | rfl
      · exact ⟨x 1, by decide, rfl⟩
      · exact ⟨x 4, by decide, rfl⟩
      · exact ⟨x 6, by decide, rfl⟩
      · exact ⟨x 8, by decide, rfl⟩
  · set σ0 := init exampleK3
    set σ1 := stepState σ0 (xbar 1)
    set σ2 := stepState σ1 (xbar 2)
    set σ3 := stepState σ2 (xbar 3)
    have hsub : ∀ σ : State, Reachable exampleK3 σ → σ.LEFT ⊆ exampleK3 := by
      intro σ hσ
      obtain ⟨_, h2, _⟩ := inv exampleK3 σ hσ
      rw [← h2]; exact subset_union_right
    have hd : ∀ σ : State, Reachable exampleK3 σ →
        ∀ C ∈ σ.LEFT, ∀ C' ∈ σ.LEFT, ∀ z, z ∈ C → z ∈ C' → C = C' :=
      fun σ hσ C hC C' hC' => hdisj C (hsub σ hσ hC) C' (hsub σ hσ hC')
    have r0 : Reachable exampleK3 σ0 := Relation.ReflTransGen.refl
    have r1 : Reachable exampleK3 σ1 := r0.tail ⟨_, step_of_disjoint σ0 (hd σ0 r0) (xbar 1)
      (by unfold State.inLIT; decide) {xbar 1, x 4, x 5} (by decide) (by decide)⟩
    have r2 : Reachable exampleK3 σ2 := r1.tail ⟨_, step_of_disjoint σ1 (hd σ1 r1) (xbar 2)
      (by unfold State.inLIT; decide) {xbar 2, x 6, x 7} (by decide) (by decide)⟩
    have r3 : Reachable exampleK3 σ3 := r2.tail ⟨_, step_of_disjoint σ2 (hd σ2 r2) (xbar 3)
      (by unfold State.inLIT; decide) {xbar 3, x 8, x 9} (by decide) (by decide)⟩
    refine ⟨σ3.SUB, ⟨σ3, r3, ?_, rfl⟩, by decide⟩
    unfold Halts State.inLIT; decide
  · rintro X ⟨σ, hσ, hh, rfl⟩
    obtain ⟨h1, h2, h3⟩ := halt_sub_ge_k_left 3 exampleK3 (by
      intro C hC
      have : ∀ C ∈ exampleK3, 3 ≤ C.card := by decide
      exact this C hC) σ hσ hh
    have := card_union_of_disjoint h2
    rw [h3, hcard] at this
    omega

/-! ### The tight family for general `k` -/

def posL (v : ℕ) : Literal := ⟨v, true⟩
def negL (v : ℕ) : Literal := ⟨v, false⟩
def freshL (k i j : ℕ) : Literal := ⟨k + 1 + Nat.pair i j, true⟩

def C0 (k : ℕ) : Clause := (range k).image posL
def Ci (k i : ℕ) : Clause := insert (negL i) ((range k).image (freshL k i))
def Sk (k : ℕ) : Finset Clause := insert (C0 k) ((range k).image (Ci k))

lemma negL_mem_Ci (k i : ℕ) : negL i ∈ Ci k i := mem_insert_self _ _

lemma negL_not_C0 (k i : ℕ) : negL i ∉ C0 k := by
  simp [C0, posL, negL]

lemma negL_mem_Ci_iff (k i i' : ℕ) : negL i ∈ Ci k i' ↔ i = i' := by
  simp [Ci, negL, freshL]

lemma Ci_inj (k : ℕ) : Function.Injective (Ci k) := by
  intro i i' h
  have := negL_mem_Ci k i
  rw [h, negL_mem_Ci_iff] at this
  exact this

lemma C0_ne_Ci (k i : ℕ) : C0 k ≠ Ci k i := by
  intro h
  have := negL_mem_Ci k i
  rw [← h] at this
  exact negL_not_C0 k i this

/-- Each literal lies in at most one clause of `Sk k`. -/
lemma Sk_uniq (k : ℕ) : ∀ C ∈ Sk k, ∀ C' ∈ Sk k, ∀ z, z ∈ C → z ∈ C' → C = C' := by
  have hC0 : ∀ z ∈ C0 k, z.pos = true ∧ z.var < k := by
    intro z hz; simp only [C0, mem_image, mem_range, posL] at hz
    obtain ⟨v, hv, rfl⟩ := hz; exact ⟨rfl, hv⟩
  have hCi : ∀ i, ∀ z ∈ Ci k i, z = negL i ∨ ∃ j, z = freshL k i j := by
    intro i z hz; simp only [Ci, mem_insert, mem_image] at hz
    rcases hz with rfl | ⟨j, _, rfl⟩
    · left; rfl
    · right; exact ⟨j, rfl⟩
  have hdisj0 : ∀ i z, z ∈ C0 k → z ∈ Ci k i → False := by
    intro i z h0 h1
    obtain ⟨hp, hv⟩ := hC0 z h0
    rcases hCi i z h1 with rfl | ⟨j, rfl⟩
    · simp [negL] at hp
    · simp [freshL] at hv; omega
  have hdisjI : ∀ i i' z, z ∈ Ci k i → z ∈ Ci k i' → i = i' := by
    intro i i' z h h'
    rcases hCi i z h with rfl | ⟨j, rfl⟩
    · exact (negL_mem_Ci_iff k i i').1 h'
    · rcases hCi i' _ h' with h2 | ⟨j', h2⟩
      · simp [freshL, negL] at h2
      · simp only [freshL, Literal.mk.injEq, add_right_inj, and_true] at h2
        exact (Nat.pair_eq_pair.1 h2).1
  intro C hC C' hC' z hz hz'
  simp only [Sk, mem_insert, mem_image, mem_range] at hC hC'
  rcases hC with rfl | ⟨i, _, rfl⟩ <;> rcases hC' with rfl | ⟨i', _, rfl⟩
  · rfl
  · exact (hdisj0 i' z hz hz').elim
  · exact (hdisj0 i z hz' hz).elim
  · rw [hdisjI i i' z hz hz']

lemma Sk_InMS (k : ℕ) : InMS k (Sk k) := by
  intro C hC
  simp only [Sk, mem_insert, mem_image, mem_range] at hC
  rcases hC with rfl | ⟨i, _, rfl⟩
  · rw [C0, card_image_of_injective _ (fun a b h => by simpa [posL] using h), card_range]
  · rw [Ci, card_insert_of_notMem (by simp [negL, freshL]),
      card_image_of_injective _ (fun a b h => by
        simp only [freshL, Literal.mk.injEq, add_right_inj, and_true] at h
        exact (Nat.pair_eq_pair.1 h).2), card_range]
    omega

lemma Sk_card (k : ℕ) : (Sk k).card = k + 1 := by
  rw [Sk, card_insert_of_notMem, card_image_of_injective _ (Ci_inj k), card_range]
  simp only [mem_image, not_exists, not_and]
  intro i _ h; exact C0_ne_Ci k i h.symm

lemma Sk_opt (k : ℕ) (hk : 1 ≤ k) : opt (Sk k) = k + 1 := by
  apply le_antisymm ((opt_le_card _).trans (Sk_card k).le)
  rw [← Sk_card k]
  apply card_le_opt
  refine ⟨⟨{l | l.pos = true}, fun l hl hneg => ?_⟩, fun C hC => ?_⟩
  · simp only [Set.mem_setOf_eq, Literal.neg] at hl hneg
    rw [hl] at hneg; exact Bool.noConfusion hneg
  · simp only [Sk, mem_insert, mem_image, mem_range] at hC
    rcases hC with rfl | ⟨i, _, rfl⟩
    · exact ⟨posL 0, mem_image.2 ⟨0, mem_range.2 (by omega), rfl⟩, rfl⟩
    · exact ⟨freshL k i 0, mem_insert_of_mem (mem_image.2 ⟨0, mem_range.2 (by omega), rfl⟩), rfl⟩

/-- The states of the run choosing `negL 0, negL 1, …`. -/
def runState (k j : ℕ) : State :=
  ⟨(range j).image (Ci k), insert (C0 k) ((Ico j k).image (Ci k)), (range j).image negL, range j⟩

lemma runState_reach (k : ℕ) : ∀ j ≤ k, Reachable (Sk k) (runState k j) := by
  intro j
  induction j with
  | zero =>
    intro _
    have : runState k 0 = init (Sk k) := by
      unfold runState init Sk
      rw [Finset.range_zero, Finset.image_empty, Finset.image_empty, Finset.range_eq_Ico]
    rw [this]; exact Relation.ReflTransGen.refl
  | succ j ih =>
    intro hj
    have hr := ih (by omega)
    obtain ⟨_, h2, _⟩ := inv (Sk k) _ hr
    have hsub : (runState k j).LEFT ⊆ Sk k := by rw [← h2]; exact subset_union_right
    have hd : ∀ C ∈ (runState k j).LEFT, ∀ C' ∈ (runState k j).LEFT, ∀ z, z ∈ C → z ∈ C' → C = C' :=
      fun C hC C' hC' => Sk_uniq k C (hsub hC) C' (hsub hC')
    have hCj : Ci k j ∈ (runState k j).LEFT := by
      simp only [runState, mem_insert, mem_image, mem_Ico]
      right; exact ⟨j, ⟨le_rfl, by omega⟩, rfl⟩
    have hlit : (runState k j).inLIT (negL j) := by simp [State.inLIT, runState, negL]
    have hstep := step_of_disjoint _ hd (negL j) hlit (Ci k j) hCj (negL_mem_Ci k j)
    have hYT : (runState k j).YT (negL j) = {Ci k j} := by
      ext C
      simp only [State.YT, mem_filter, mem_singleton]
      constructor
      · rintro ⟨hC, hn⟩
        exact hd C hC (Ci k j) hCj (negL j) hn (negL_mem_Ci k j)
      · rintro rfl; exact ⟨hCj, negL_mem_Ci k j⟩
    have heq : stepState (runState k j) (negL j) = runState k (j + 1) := by
      unfold stepState
      rw [hYT]
      simp only [runState]
      congr 1
      · rw [Finset.range_add_one, image_insert, union_comm, ← insert_eq]
      · ext C
        simp only [mem_sdiff, mem_insert, mem_image, mem_Ico, mem_singleton]
        constructor
        · rintro ⟨h | ⟨i, hi, rfl⟩, hne⟩
          · left; exact h
          · right; refine ⟨i, ⟨?_, hi.2⟩, rfl⟩
            rcases Nat.lt_or_ge j i with h | h
            · exact h
            · exfalso; apply hne; congr 1; omega
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨Or.inl rfl, C0_ne_Ci k j⟩
          · refine ⟨Or.inr ⟨i, ⟨by omega, hi.2⟩, rfl⟩, fun h => ?_⟩
            have := Ci_inj k h; omega
      · rw [Finset.range_add_one, image_insert]
      · simp [negL, Finset.range_add_one]
    rw [← heq]
    exact hr.tail ⟨_, hstep⟩

theorem greedy_maxsat_ratio (k : ℕ) (hk : 1 ≤ k) :
    (∀ (S : Finset Shared.Clause), Shared.InMS k S → ∀ X : Finset Shared.Clause, Choosable S X →
        k * Shared.opt S ≤ (k + 1) * X.card) ∧
      (∃ (S : Finset Shared.Clause), Shared.InMS k S ∧ ∃ X : Finset Shared.Clause, Choosable S X ∧
        0 < X.card ∧ k * Shared.opt S = (k + 1) * X.card) := by
  refine ⟨fun S hS X ⟨σ, hσ, hh, hX⟩ => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := halt_sub_ge_k_left k S hS σ hσ hh
    have hc := card_union_of_disjoint h2
    rw [h3] at hc
    have hopt := opt_le_card S
    rw [← hX]
    nlinarith
  · refine ⟨Sk k, Sk_InMS k, (runState k k).SUB, ⟨runState k k, runState_reach k k le_rfl, ?_, rfl⟩,
      ?_, ?_⟩
    · intro C hC l hl
      simp only [runState, Ico_self, image_empty, insert_empty_eq, mem_singleton] at hC
      subst hC
      simp only [State.inLIT, runState, not_not, mem_range]
      simp only [C0, mem_image, mem_range, posL] at hl
      obtain ⟨v, hv, rfl⟩ := hl; exact hv
    · simp only [runState]
      rw [card_image_of_injective _ (Ci_inj k), card_range]; omega
    · simp only [runState]
      rw [card_image_of_injective _ (Ci_inj k), card_range, Sk_opt k hk]
      ring

end JohnsonApprox.MaxSatGreedy

open JohnsonApprox JohnsonApprox.MaxSatGreedy

theorem solution (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) (σ : State)
    (hσ : Reachable S σ) (hh : Halts σ) :
    k * σ.LEFT.card ≤ σ.SUB.card ∧ Disjoint σ.SUB σ.LEFT ∧ σ.SUB ∪ σ.LEFT = S := by
  exact halt_sub_ge_k_left k S hS σ hσ hh
