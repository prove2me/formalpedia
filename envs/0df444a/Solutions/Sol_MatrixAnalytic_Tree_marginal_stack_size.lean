-- Prove2me | solution 1 for MatrixAnalytic.Tree.marginal_stack_size
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:27:43.330893+00:00
-- url     : https://prove2.me/submissions/e7d61bbb-b11b-428f-b6b6-44506c59c11d

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal
open MatrixAnalytic.Tree

set_option linter.unusedSectionVars false

namespace S202MS


noncomputable def g72mab_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def g72mab_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then g72mab_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72mab_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * g72mab_W P ω := by
  unfold g72mab_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma g72mab_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72mab_W P (Fin.snoc ω k : Fin (n + 2) → V) = g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold g72mab_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g72mab_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g72mab_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma g72mab_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma g72mab_PS_zero (x y : V) (A : V → Prop) :
    g72mab_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold g72mab_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [g72mab_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma g72mab_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
    ((Fin.cons x ω : Fin (L + 2) → V) 0 = x ∧ (Fin.cons x ω : Fin (L + 2) → V) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.cons x ω : Fin (L + 2) → V) m)) ↔
    ((L = 0 ∨ A (ω 0)) ∧ ω 0 = ω 0 ∧ ω (Fin.last L) = y ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)) := by
  rw [← Fin.succ_last, Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ]
  simp only [ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and, Fin.cons_succ,
    Fin.succ_ne_zero, not_false_eq_true, true_implies, Fin.succ_inj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun m _ hm => h2 m hm⟩
    by_cases hL : L = 0
    · exact Or.inl hL
    · refine Or.inr (h2 0 ?_)
      intro h; apply hL; have := congrArg Fin.val h; simp at this; omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases hm0 : m = 0
    · subst hm0
      rcases h0 with h0 | h0
      · subst h0; exact absurd rfl hm
      · exact h0
    · exact h2 m hm0 hm

lemma g72mab_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72mab_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then g72mab_PS P z L y A else 0) := by
  classical
  unfold g72mab_PS
  rw [g72mab_tsum_cons, tsum_eq_single x]
  · simp_rw [g72mab_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := g72mab_cond_cons x y A ω
      rw [g72mab_W_cons]
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd (hcc.mp h1).2 h3
      · exact absurd (hcc.mp h1).1 h2
      · exact absurd (hcc.mpr ⟨by assumption, by assumption⟩) (by assumption)
      · simp
      · simp
    · intro z hz
      simp [Ne.symm hz]
  · intro k hk
    apply ENNReal.tsum_eq_zero.mpr
    intro ω
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hk (by simpa using h)

lemma g72mab_PS_one (x y : V) (A : V → Prop) :
    g72mab_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [g72mab_PS_cons P, tsum_eq_single y]
  · simp [g72mab_PS_zero]
  · intro z hz; simp [g72mab_PS_zero, hz]

open Classical in
noncomputable def g72mab_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then g72mab_W P ω else 0

open Classical in
noncomputable def g72mab_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then g72mab_W P ω else 0

lemma g72mab_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A (t + 1) + g72mab_EX P x A (t + 1) = g72mab_AV P x A t := by
  classical
  unfold g72mab_AV g72mab_EX
  rw [g72mab_tsum_snoc, g72mab_tsum_snoc, ← ENNReal.tsum_add]
  refine tsum_congr fun ω => ?_
  rw [← ENNReal.tsum_add]
  have hz : ∀ k, (Fin.snoc ω k : Fin (t + 2) → V) 0 = ω 0 := fun k => by
    have : (0 : Fin (t + 2)) = (0 : Fin (t + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  have e1 : ∀ m : Fin (t + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · rintro rfl; rfl
  have hA : ∀ k, (∀ i : Fin (t + 2), i ≠ 0 → A ((Fin.snoc ω k : Fin (t + 2) → V) i)) ↔
      (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have e2 : Fin.last (t + 1) ≠ 0 := by simp [Fin.ext_iff]
    simp only [ne_eq, e1, e2, not_false_eq_true, true_implies]
  have hB : ∀ k, (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
      A ((Fin.snoc ω k : Fin (t + 2) → V) m)) ↔ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff,
      and_true]
    refine forall_congr' fun m => ?_
    have e2 : m.castSucc ≠ Fin.last (t+1) := Fin.castSucc_ne_last m
    simp only [e1, e2, not_false_eq_true, true_implies]
  simp_rw [hz, hA, hB, Fin.snoc_last, g72mab_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
      intro k
      by_cases hk : A k
      · rw [if_pos ⟨hc.1, hc.2, hk⟩, if_neg (by tauto), add_zero]
      · rw [if_neg (by tauto), if_pos ⟨hc.1, hk, hc.2⟩, zero_add]
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, hrow, mul_one]
  · rw [if_neg hc]
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    rw [if_neg (by tauto), if_neg (by tauto), add_zero]

lemma g72mab_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A t + ∑ k ∈ Finset.range t, g72mab_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold g72mab_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [g72mab_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (g72mab_EX P x A (t + 1)), ← add_assoc,
      add_comm (g72mab_EX P x A (t + 1)), g72mab_step P hrow x A t, ih]

end Gen

section Gen3
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
    ((Fin.snoc ω y : Fin (L + 2) → V) 0 = x ∧ (Fin.snoc ω y : Fin (L + 2) → V) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.snoc ω y : Fin (L + 2) → V) m)) ↔
    ((L = 0 ∨ A (ω (Fin.last L))) ∧ (ω 0 = x ∧ ω (Fin.last L) = ω (Fin.last L) ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m))) := by
  have hz : (Fin.snoc ω y : Fin (L + 2) → V) 0 = ω 0 := by
    have : (0 : Fin (L + 2)) = (0 : Fin (L + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  rw [hz, Fin.snoc_last, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff, and_true,
    true_and]
  have e1 : ∀ m : Fin (L + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · rintro rfl; rfl
  have e2 : ∀ m : Fin (L + 1), m.castSucc ≠ Fin.last (L+1) := Fin.castSucc_ne_last
  simp only [e1, e2, not_false_eq_true, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun m hm _ => h2 m hm⟩
    by_cases hL : L = 0
    · exact Or.inl hL
    · refine Or.inr (h2 _ ?_)
      intro h; apply hL; have := congrArg Fin.val h; simp at this; omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases hml : m = Fin.last L
    · subst hml
      rcases h0 with h0 | h0
      · subst h0; exact absurd rfl hm
      · exact h0
    · exact h2 m hm hml

lemma g72mab_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72mab_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then g72mab_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold g72mab_PS
  rw [g72mab_tsum_snoc]
  simp_rw [g72mab_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := g72mab_cond_snoc x y A ω
    rw [g72mab_W_snoc]
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd (hcc.mp h1).2 h3
    · exact absurd (hcc.mp h1).1 h2
    · exact absurd (hcc.mpr ⟨by assumption, by assumption⟩) (by assumption)
    · simp
    · simp
  · intro z hz
    simp [Ne.symm hz]
  · intro k hk
    rw [if_neg]
    rintro ⟨-, h, -⟩
    exact hk (by simpa using h)

end Gen3
section GRK
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma g72mab_EX_eq (x : V) (A : V → Prop) (k : ℕ) :
    g72mab_EX P x A k = ∑' y, if ¬ A y then g72mab_PS P x k y A else 0 := by
  classical
  unfold g72mab_EX g72mab_PS
  simp_rw [g72mab_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last k))]
  · by_cases hA : A (ω (Fin.last k)) <;> simp [hA]
  · intro y hy; simp [Ne.symm hy]
end GRK
section TR
variable {V : Type*} [Countable V] [DecidableEq V]

lemma g72mab_qsum (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    HasSum (fun y => if y = x then 0 else Q x y) (holdRate Q x) := by
  have h := (hQ.2 x).sub (hasSum_ite_eq x (Q x x))
  have e : (fun y => if y = x then 0 else Q x y) = fun y => Q x y - (if y = x then Q x x else 0) := by
    funext y; by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  rw [e, show holdRate Q x = 0 - Q x x by simp [holdRate]]
  exact h

lemma g72mab_qge (Q : V → V → ℝ) (hQ : IsGenerator Q) (x y : V) (hxy : x ≠ y) :
    Q x y ≤ holdRate Q x := by
  have h := le_hasSum (g72mab_qsum Q hQ x) y (fun j hj => by
    split_ifs with h
    · exact le_rfl
    · exact hQ.1 x j (Ne.symm h))
  simpa [Ne.symm hxy] using h

lemma g72mab_jrow (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    ∑' y, ENNReal.ofReal (jumpP Q x y) = 1 := by
  classical
  unfold jumpP
  by_cases hq : holdRate Q x = 0
  · simp only [hq, if_true]
    rw [tsum_eq_single x]
    · simp
    · intro b hb; simp [hb]
  · simp only [hq, if_false]
    have hs := (g72mab_qsum Q hQ x).div_const (holdRate Q x)
    rw [div_self hq] at hs
    have hqpos : 0 < holdRate Q x := by
      have : 0 ≤ holdRate Q x := (g72mab_qsum Q hQ x).nonneg (fun j => by
        split_ifs with h
        · exact le_rfl
        · exact hQ.1 x j (Ne.symm h))
      exact lt_of_le_of_ne this (Ne.symm hq)
    have e : (fun y => (if y = x then 0 else Q x y) / holdRate Q x) =
        fun y => if y = x then 0 else Q x y / holdRate Q x := by
      funext y; split_ifs <;> simp
    rw [e] at hs
    have hnn : ∀ y, 0 ≤ (if y = x then (0 : ℝ) else Q x y / holdRate Q x) := fun y => by
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg (hQ.1 x y (Ne.symm h)) hqpos.le
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs.summable, hs.tsum_eq, ENNReal.ofReal_one]

lemma g72mab_jpos (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    ∀ y, Relation.ReflTransGen (fun u v : V => u ≠ v ∧ 0 < Q u v) x y →
      ∃ L, g72mab_PS (jumpP Q) x L y (fun _ => True) ≠ 0 := by
  classical
  intro y h
  induction h with
  | refl => exact ⟨0, by rw [g72mab_PS_zero]; simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨hne, hpos⟩ := hbc
    have hq : 0 < holdRate Q b := lt_of_lt_of_le hpos (g72mab_qge Q hQ b c hne)
    have hj : 0 < jumpP Q b c := by
      unfold jumpP
      rw [if_neg hq.ne', if_neg (Ne.symm hne)]
      exact div_pos hpos hq
    refine ⟨L + 1, ?_⟩
    rw [g72mab_PS_snoc (jumpP Q) x L c (fun _ => True)]
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (if L = 0 ∨ True then g72mab_PS (jumpP Q) x L b (fun _ => True) else 0) *
          ENNReal.ofReal (jumpP Q b c) := by
          rw [if_pos (Or.inr trivial)]
          exact ENNReal.mul_pos hL (by simp [hj])
      _ ≤ _ := ENNReal.le_tsum b

lemma g72mab_rt (Q : V → V → ℝ) (x : V) (t : ℕ) :
    returnTail Q x t = g72mab_AV (jumpP Q) x (fun z => z ≠ x) t := by
  unfold returnTail g72mab_AV
  refine tsum_congr fun ω => ?_
  split_ifs <;> rfl

end TR

section UNTree
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma un_N_eq (T : TreeData ι) (i j : ι) :
    matN T i j = (∑' t, g72mab_PS (jumpP (gen T)) (some ([], i)) t (some ([], j))
      (fun w => w ≠ none)) * ENNReal.ofReal (holdRate (gen T) (some ([], j)))⁻¹ := by
  unfold matN sojournAvoid expVisitsAvoid g72mab_PS
  congr 1
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases h1 : ω 0 = some ([], i) ∧ ω (Fin.last t) = some ([], j) ∧
      ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ ({none} : Set (TreeState ι))
  · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, fun m hm _ => h1.2.2 m hm⟩]; rfl
  · rw [if_neg h1, if_neg]
    intro h2
    refine h1 ⟨h2.1, h2.2.1, fun m hm => ?_⟩
    by_cases hml : m = Fin.last t
    · rw [hml, h2.2.1]; simp
    · simpa using h2.2.2 m hm hml

end UNTree

section Chain
variable {V : Type*} (P : V → V → ℝ)

lemma ns_sub_iter (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y) :
    ∀ L x y, m x * g72mab_PS P x L y (fun _ => True) ≤ m y := by
  classical
  intro L
  induction L with
  | zero =>
    intro x y
    rw [g72mab_PS_zero]
    split_ifs with h
    · subst h; simp
    · simp
  | succ L ih =>
    intro x y
    rw [g72mab_PS_snoc, ← hm y, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [if_pos (Or.inr trivial), ← mul_assoc]
    gcongr
    exact ih x w

lemma ns_iter (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y)
    (B : V → Prop) [DecidablePred B] (y : V) :
    ∀ t, m y = ∑ L ∈ Finset.range (t + 1),
        ∑' x, (if B x then 0 else m x * g72mab_PS P x (L + 1) y B)
      + ∑' x, (if B x then m x * g72mab_PS P x (t + 1) y B else 0) := by
  intro t
  induction t with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [← ENNReal.tsum_add, ← hm y]
    refine tsum_congr fun x => ?_
    rw [g72mab_PS_one]
    split_ifs <;> simp
  | succ t ih =>
    rw [ih, Finset.sum_range_succ _ (t + 1), add_assoc]
    congr 1
    have hc : ∀ u, m u * g72mab_PS P u (t + 1 + 1) y B = ∑' x, (if B x then
        m u * ENNReal.ofReal (P u x) * g72mab_PS P x (t + 1) y B else 0) := by
      intro u
      rw [g72mab_PS_cons, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun x => ?_
      by_cases hx : B x <;> simp [hx, mul_assoc]
    rw [← ENNReal.tsum_add]
    calc ∑' x, (if B x then m x * g72mab_PS P x (t + 1) y B else 0)
        = ∑' x, (if B x then (∑' u, m u * ENNReal.ofReal (P u x)) *
            g72mab_PS P x (t + 1) y B else 0) := by
          refine tsum_congr fun x => ?_; rw [hm x]
      _ = ∑' x, ∑' u, (if B x then m u * ENNReal.ofReal (P u x) *
            g72mab_PS P x (t + 1) y B else 0) := by
          refine tsum_congr fun x => ?_
          split_ifs
          · rw [ENNReal.tsum_mul_right]
          · simp
      _ = ∑' u, m u * g72mab_PS P u (t + 1 + 1) y B := by
          rw [ENNReal.tsum_comm]; exact tsum_congr fun u => (hc u).symm
      _ = _ := tsum_congr fun u => by split_ifs <;> simp

/-- excursion occupation measure from `k` -/
noncomputable def ns_gam (k y : V) : ℝ≥0∞ :=
  ∑' L, g72mab_PS P k (L + 1) y (fun z => z ≠ k)

lemma ns_gam_kk (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (k : V)
    (hrec : Filter.Tendsto (fun t => g72mab_AV P k (fun z => z ≠ k) t) Filter.atTop (nhds 0)) :
    ns_gam P k k = 1 := by
  classical
  have hEX : ∀ s, g72mab_EX P k (fun z => z ≠ k) (s + 1) = g72mab_PS P k (s + 1) k (fun z => z ≠ k) := by
    intro s
    rw [g72mab_EX_eq, tsum_eq_single k]
    · simp
    · intro b hb; simp [hb]
  have hmass : ∀ t, g72mab_AV P k (fun z => z ≠ k) t +
      ∑ s ∈ Finset.range t, g72mab_PS P k (s + 1) k (fun z => z ≠ k) = 1 := by
    intro t; have := g72mab_mass P hrow k (fun z => z ≠ k) t; simp_rw [hEX] at this; exact this
  apply le_antisymm
  · exact ENNReal.tsum_le_of_sum_range_le fun t => by rw [← hmass t]; exact le_add_self
  · have hlim := hrec.add (tendsto_const_nhds (x := ns_gam P k k))
    rw [zero_add] at hlim
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun t => ?_)
    rw [← hmass t]
    gcongr
    exact ENNReal.sum_le_tsum _

lemma ns_gam_inv (k : V) (hkk : ns_gam P k k = 1) :
    ∀ y, ∑' w, ns_gam P k w * ENNReal.ofReal (P w y) = ns_gam P k y := by
  classical
  intro y
  unfold ns_gam
  rw [tsum_eq_zero_add' ENNReal.summable, g72mab_PS_one]
  have e : ∀ L, g72mab_PS P k (L + 1 + 1) y (fun z => z ≠ k) =
      ∑' w, (if w = k then 0 else g72mab_PS P k (L + 1) w (fun z => z ≠ k) * ENNReal.ofReal (P w y)) := by
    intro L
    rw [g72mab_PS_snoc]
    refine tsum_congr fun w => ?_
    by_cases hw : w = k <;> simp [hw]
  simp_rw [e]
  rw [ENNReal.tsum_comm, ENNReal.tsum_eq_add_tsum_ite k]
  have hk1 : ∑' L, g72mab_PS P k (L + 1) k (fun z => z ≠ k) = 1 := hkk
  rw [hk1, one_mul]
  congr 1
  refine tsum_congr fun w => ?_
  by_cases hw : w = k
  · simp [hw]
  · simp only [hw, if_false]
    rw [ENNReal.tsum_mul_right]

lemma ns_gam_le (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y) (k y : V) :
    m k * ns_gam P k y ≤ m y := by
  classical
  unfold ns_gam
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  have h := ns_iter P m hm (fun z => z ≠ k) y t
  have e : ∀ L, ∑' x, (if x ≠ k then 0 else m x * g72mab_PS P x (L + 1) y (fun z => z ≠ k)) =
      m k * g72mab_PS P k (L + 1) y (fun z => z ≠ k) := by
    intro L
    rw [tsum_eq_single k]
    · simp
    · intro b hb; simp [hb]
  simp_rw [e] at h
  calc _ ≤ ∑ L ∈ Finset.range (t + 1), m k * g72mab_PS P k (L + 1) y (fun z => z ≠ k) :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ t))
    _ ≤ _ := by rw [h]; exact le_self_add

lemma ns_uniq (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y)
    (hfin : ∀ y, m y ≠ ⊤) (k : V) (hkk : ns_gam P k k = 1)
    (hirr : ∀ x, ∃ L, g72mab_PS P x L k (fun _ => True) ≠ 0) :
    ∀ y, m y = m k * ns_gam P k y := by
  classical
  set c := m k with hc
  set μ : V → ℝ≥0∞ := fun y => m y - c * ns_gam P k y with hμ
  have hle := ns_gam_le P m hm k
  have hsplit : ∀ y, m y = μ y + c * ns_gam P k y := fun y => (tsub_add_cancel_of_le (hle y)).symm
  have hcf : ∀ y, c * ns_gam P k y ≠ ⊤ := fun y => ne_top_of_le_ne_top (hfin y) (hle y)
  have hginv := ns_gam_inv P k hkk
  have hμinv : ∀ y, ∑' x, μ x * ENNReal.ofReal (P x y) = μ y := by
    intro y
    have h1 : ∑' x, m x * ENNReal.ofReal (P x y) =
        ∑' x, μ x * ENNReal.ofReal (P x y) + c * ns_gam P k y := by
      rw [← hginv y, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      refine tsum_congr fun x => ?_
      rw [hsplit x, add_mul, mul_assoc]
    rw [hm y, hsplit y] at h1
    exact ((ENNReal.add_left_inj (hcf y)).mp h1).symm
  have hμk : μ k = 0 := by simp [hμ, hc, hkk]
  intro y
  have hy0 : μ y = 0 := by
    obtain ⟨L, hL⟩ := hirr y
    have := ns_sub_iter P μ hμinv L y k
    rw [hμk] at this
    rcases mul_eq_zero.mp (le_antisymm this bot_le) with h | h
    · exact h
    · exact absurd h hL
  rw [hsplit y, hy0, zero_add]

lemma ns_rem (k : V) (B : V → Prop) [DecidablePred B] (hB : ∀ z, B z → z ≠ k) (L : ℕ) :
    ∀ t y, ∑' x, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
        g72mab_PS P x t y B else 0) ≤ g72mab_PS P k (L + 1 + t) y (fun z => z ≠ k) := by
  classical
  intro t
  induction t with
  | zero =>
    intro y
    rw [tsum_eq_single y]
    · rw [g72mab_PS_zero]; split_ifs <;> simp
    · intro b hb; rw [g72mab_PS_zero, if_neg hb]; simp
  | succ t ih =>
    intro y
    rw [show L + 1 + (t + 1) = (L + 1 + t) + 1 by omega, g72mab_PS_snoc P k (L + 1 + t)]
    have e : ∀ x, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
        g72mab_PS P x (t + 1) y B else 0) = ∑' w, (if B x then
          g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
          ((if t = 0 ∨ B w then g72mab_PS P x t w B else 0) * ENNReal.ofReal (P w y)) else 0) := by
      intro x
      split_ifs
      · rw [g72mab_PS_snoc P x t y B, ENNReal.tsum_mul_left]
      · simp
    simp_rw [e]
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum fun w => ?_
    by_cases hw : B w
    · have hk : L + 1 + t = 0 ∨ w ≠ k := Or.inr (hB w hw)
      rw [if_pos hk]
      calc _ = (∑' x, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
            g72mab_PS P x t w B else 0)) * ENNReal.ofReal (P w y) := by
            rw [← ENNReal.tsum_mul_right]
            refine tsum_congr fun x => ?_
            rw [if_pos (Or.inr hw)]
            split_ifs <;> simp [mul_assoc]
        _ ≤ _ := by gcongr; exact ih w
    · by_cases ht : t = 0
      · subst ht
        refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun x => ?_)) bot_le
        by_cases hx : B x
        · rw [if_pos hx, g72mab_PS_zero, if_neg (fun (h : x = w) => hw (h ▸ hx))]; simp
        · rw [if_neg hx]
      · refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun x => ?_)) bot_le
        split_ifs <;> simp_all

theorem ns_main (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (m : V → ℝ≥0∞) (hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y)
    (hfin : ∀ y, m y ≠ ⊤) (k : V) (hk0 : m k ≠ 0)
    (hrec : Filter.Tendsto (fun t => g72mab_AV P k (fun z => z ≠ k) t) Filter.atTop (nhds 0))
    (hirr : ∀ x, ∃ L, g72mab_PS P x L k (fun _ => True) ≠ 0)
    (B : V → Prop) [DecidablePred B] (hB : ∀ z, B z → z ≠ k) (y : V) :
    m y = ∑' L, ∑' x, (if B x then 0 else m x * g72mab_PS P x (L + 1) y B) := by
  have hkk := ns_gam_kk P hrow k hrec
  have hu := ns_uniq P m hm hfin k hkk hirr
  have hgfin : ns_gam P k y ≠ ⊤ := by
    intro h
    have := hfin y
    rw [hu y, h, ENNReal.mul_top hk0] at this
    exact this rfl
  set f : ℕ → ℝ≥0∞ := fun L => g72mab_PS P k (L + 1) y (fun z => z ≠ k) with hf
  have htail := ENNReal.tendsto_sum_nat_add f hgfin
  have hremb : ∀ t, ∑' x, (if B x then m x * g72mab_PS P x (t + 1) y B else 0) ≤
      m k * ∑' L, f (L + (t + 1)) := by
    intro t
    calc _ = m k * ∑' x, (if B x then ns_gam P k x * g72mab_PS P x (t + 1) y B else 0) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun x => ?_
          split_ifs
          · rw [hu x, mul_assoc]
          · simp
      _ ≤ _ := by
          gcongr
          unfold ns_gam
          calc _ = ∑' x, ∑' L, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
                g72mab_PS P x (t + 1) y B else 0) := by
                refine tsum_congr fun x => ?_
                split_ifs
                · rw [ENNReal.tsum_mul_right]
                · simp
            _ = ∑' L, ∑' x, (if B x then g72mab_PS P k (L + 1) x (fun z => z ≠ k) *
                g72mab_PS P x (t + 1) y B else 0) := ENNReal.tsum_comm
            _ ≤ _ := by
                refine ENNReal.tsum_le_tsum fun L => (ns_rem P k B hB L (t + 1) y).trans
                  (le_of_eq ?_)
                simp only [hf]
                congr 1
                omega
  apply le_antisymm
  · have hlim := (tendsto_const_nhds (x := ∑' L, ∑' x, (if B x then 0 else
      m x * g72mab_PS P x (L + 1) y B))).add (ENNReal.Tendsto.const_mul htail (Or.inr (hfin k))
        |>.comp (Filter.tendsto_add_atTop_nat 1))
    rw [mul_zero, add_zero] at hlim
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun t => ?_)
    rw [ns_iter P m hm B y t]
    simp only [Function.comp]
    gcongr
    · exact ENNReal.sum_le_tsum _
    · exact hremb t
  · refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
    calc _ ≤ ∑ L ∈ Finset.range (t + 1), ∑' x, (if B x then 0 else
          m x * g72mab_PS P x (L + 1) y B) :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ t))
      _ ≤ _ := by rw [ns_iter P m hm B y t]; exact le_self_add

end Chain

section Tree
variable {ι : Type*} [Countable ι] [DecidableEq ι]

def ns_In (p : List ι) (w : TreeState ι) : Prop := ∃ l m, w = some (p ++ l, m)

lemma ns_rtsum_ne {α : Type*} (f : α → ℝ) (h : ∑' x, f x ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  have : f = fun _ => 0 := funext hc
  rw [this, tsum_zero]

lemma ns_gen_shift (T : TreeData ι) (p l l' : List ι) (a b : ι) :
    gen T (some (p ++ l, a)) (some (p ++ l', b)) = gen T (some (l, a)) (some (l', b)) := by
  simp [gen, List.append_assoc]

lemma ns_hold_shift (T : TreeData ι) (p l : List ι) (a : ι) :
    holdRate (gen T) (some (p ++ l, a)) = holdRate (gen T) (some (l, a)) := by
  unfold holdRate; rw [ns_gen_shift]

lemma ns_jumpP_shift (T : TreeData ι) (p l l' : List ι) (a b : ι) :
    jumpP (gen T) (some (p ++ l, a)) (some (p ++ l', b)) =
      jumpP (gen T) (some (l, a)) (some (l', b)) := by
  unfold jumpP
  rw [ns_hold_shift, ns_gen_shift]
  simp

lemma ns_iso (T : TreeData ι) (p : List ι) :
    ∀ t (l : List ι) (a : ι) (lb : List ι) (b : ι),
      g72mab_PS (jumpP (gen T)) (some (p ++ l, a)) t (some (p ++ lb, b)) (ns_In p) =
        g72mab_PS (jumpP (gen T)) (some (l, a)) t (some (lb, b)) (fun w => w ≠ none) := by
  classical
  intro t
  induction t with
  | zero =>
    intro l a lb b
    rw [g72mab_PS_zero, g72mab_PS_zero]
    simp
  | succ t ih =>
    intro l a lb b
    rw [g72mab_PS_cons, g72mab_PS_cons]
    have hψ : Function.Injective (fun q : List ι × ι => (some (p ++ q.1, q.2) : TreeState ι)) := by
      intro q r h
      simp only [Option.some.injEq, Prod.mk.injEq, List.append_cancel_left_eq] at h
      exact Prod.ext h.1 h.2
    have hσ : Function.Injective (fun q : List ι × ι => (some q : TreeState ι)) :=
      Option.some_injective _
    rw [← hψ.tsum_eq, ← hσ.tsum_eq]
    · refine tsum_congr fun q => ?_
      rw [ns_jumpP_shift, ih]
      have h1 : ns_In p (some (p ++ q.1, q.2) : TreeState ι) := ⟨q.1, q.2, rfl⟩
      have h2 : (some q : TreeState ι) ≠ none := by simp
      rw [if_pos (Or.inr h1), if_pos (Or.inr h2)]
    · intro w hw
      rw [Function.mem_support] at hw
      rcases w with _ | q
      · exfalso; apply hw
        by_cases ht : t = 0
        · subst ht; simp [g72mab_PS_zero]
        · simp [ht]
      · exact ⟨q, rfl⟩
    · intro w hw
      rw [Function.mem_support] at hw
      have h2 := right_ne_zero_of_mul hw
      by_cases hc : t = 0 ∨ ns_In p w
      · rcases hc with hc | ⟨l', m, rfl⟩
        · subst hc
          rw [if_pos (Or.inl rfl), g72mab_PS_zero] at h2
          by_cases hw' : w = some (p ++ lb, b)
          · exact ⟨(lb, b), hw'.symm⟩
          · rw [if_neg hw'] at h2; exact absurd rfl h2
        · exact ⟨(l', m), rfl⟩
      · rw [if_neg hc] at h2; exact absurd rfl h2

lemma ns_struct (T : TreeData ι) (n : List ι) (j : ι) (x z : TreeState ι)
    (hx : ¬ ns_In (n ++ [j]) x) (hz : ns_In (n ++ [j]) z) (h : gen T x z ≠ 0) :
    (∃ a, x = some (n, a)) ∧ ∃ b, z = some (n ++ [j], b) := by
  obtain ⟨l, b, rfl⟩ := hz
  rcases x with _ | ⟨m, a⟩
  · exfalso; apply h; simp [gen]
  · simp only [gen] at h
    have h1 : ¬ (n ++ [j] ++ l = m) := fun e => hx ⟨l, a, by rw [e]⟩
    have h3 : (∑' j' : ι, (if m = n ++ [j] ++ l ++ [j'] then T.D j' a b else 0)) = 0 := by
      refine (tsum_congr fun j' => if_neg ?_).trans tsum_zero
      intro e; exact hx ⟨l ++ [j'], a, by rw [e]; simp⟩
    rw [if_neg h1, h3, zero_add, add_zero] at h
    obtain ⟨j', hj'⟩ := ns_rtsum_ne _ h
    have e : n ++ [j] ++ l = m ++ [j'] := by
      by_contra hc; exact hj' (if_neg hc)
    rcases List.eq_nil_or_concat l with hl | ⟨l', c, rfl⟩
    · subst hl
      have e2 := congrArg List.dropLast e
      simp only [List.append_nil, List.dropLast_concat] at e2
      subst e2
      exact ⟨⟨a, rfl⟩, ⟨b, by simp⟩⟩
    · exfalso
      have e2 := congrArg List.dropLast e
      simp only [List.concat_eq_append, ← List.append_assoc, List.dropLast_concat] at e2
      exact hx ⟨l', a, by rw [← e2]⟩

lemma ns_gen_A (T : TreeData ι) (n : List ι) (j a b : ι) :
    gen T (some (n, a)) (some (n ++ [j], b)) = T.A j a b := by
  simp only [gen]
  have h1 : ¬ (n ++ [j] = n) := by simp
  rw [if_neg h1, zero_add]
  have h3 : ∑' j' : ι, (if n = n ++ [j] ++ [j'] then T.D j' a b else 0) = 0 :=
    (tsum_congr fun j' => if_neg (by intro e; have := congrArg List.length e; simp at this)).trans
      tsum_zero
  rw [h3, add_zero, tsum_eq_single j]
  · simp
  · intro j' hj'; rw [if_neg]; intro e; simp at e; exact hj' e.symm

lemma ns_qpos (T : TreeData ι) (hT : IsTreeProcess T) (j0 : ι) (x : TreeState ι) :
    0 < holdRate (gen T) x := by
  obtain ⟨y, hy⟩ : ∃ y, y ≠ x := by
    rcases x with _ | q
    · exact ⟨some ([], j0), by simp⟩
    · exact ⟨none, by simp⟩
  rcases Relation.ReflTransGen.cases_head (hT.2 x y) with h | ⟨c, ⟨hne, hpos⟩, -⟩
  · exact absurd h.symm hy
  · exact lt_of_lt_of_le hpos (g72mab_qge (gen T) hT.1 _ c hne)

lemma ns_inv (T : TreeData ι) (hT : IsTreeProcess T) (j0 : ι) (π : TreeState ι → ℝ)
    (hπ : IsStationaryCT (gen T) π) (y : TreeState ι) :
    ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate (gen T) x) *
      ENNReal.ofReal (jumpP (gen T) x y) =
      ENNReal.ofReal (π y) * ENNReal.ofReal (holdRate (gen T) y) := by
  classical
  have hq := ns_qpos T hT j0
  set g : TreeState ι → ℝ := fun x => if x = y then 0 else π x * gen T x y with hg
  have hgs : HasSum g (π y * holdRate (gen T) y) := by
    have h := (hπ.2.2 y).sub (hasSum_ite_eq y (π y * gen T y y))
    have e1 : g = fun x => π x * gen T x y - if x = y then π y * gen T y y else 0 := by
      funext x
      by_cases hx : x = y
      · subst hx; simp [hg]
      · simp [hg, hx]
    rw [e1, show π y * holdRate (gen T) y = 0 - π y * gen T y y by simp [holdRate]]
    exact h
  have hgn : ∀ x, 0 ≤ g x := fun x => by
    simp only [hg]
    split_ifs with hx
    · exact le_rfl
    · exact mul_nonneg (hπ.1 x) (hT.1.1 x y hx)
  have hterm : ∀ x, ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate (gen T) x) *
      ENNReal.ofReal (jumpP (gen T) x y) = ENNReal.ofReal (g x) := by
    intro x
    unfold jumpP
    rw [if_neg (hq x).ne']
    by_cases hx : y = x
    · subst hx; simp [hg]
    · rw [if_neg hx]
      simp only [hg, if_neg (Ne.symm hx)]
      rw [← ENNReal.ofReal_mul (hπ.1 x), ← ENNReal.ofReal_mul (mul_nonneg (hπ.1 x) (hq x).le)]
      congr 1
      have := (hq x).ne'
      field_simp
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hgn hgs.summable, hgs.tsum_eq, ENNReal.ofReal_mul (hπ.1 y)]

end Tree

section Final
variable {ι : Type*} [Countable ι] [DecidableEq ι]

theorem ns_final (T : TreeData ι) (hT : IsTreeProcess T)
    (hpr : IsPositiveRecurrentProcess (gen T))
    (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) (n : List ι) (j i : ι) :
    ENNReal.ofReal (nodeVec π (n ++ [j]) i) =
      vecMulE (vecMulE (fun k => ENNReal.ofReal (nodeVec π n k)) (ennMat (T.A j))) (matN T) i := by
  classical
  set P := jumpP (gen T) with hP
  set ν : TreeState ι → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate (gen T) x) with hν
  set p := n ++ [j] with hp
  have hq := ns_qpos T hT j
  have hrow := g72mab_jrow (gen T) hT.1
  have hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y := ns_inv T hT j π hπ
  have hfin : ∀ y, ν y ≠ ⊤ := fun y =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hirr : ∀ x, ∃ L, g72mab_PS P x L none (fun _ => True) ≠ 0 :=
    fun x => g72mab_jpos (gen T) hT.1 x none (hT.2 x none)
  have hk0 : ν none ≠ 0 := by
    intro h0
    have hall : ∀ x, π x = 0 := by
      intro x
      obtain ⟨L, hL⟩ := hirr x
      have h1 := ns_sub_iter P ν hinv L x none
      rw [h0] at h1
      have h2 : ν x = 0 := by
        rcases mul_eq_zero.mp (le_antisymm h1 bot_le) with h | h
        · exact h
        · exact absurd h hL
      have h3 : ENNReal.ofReal (π x) = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h (by simp [hq x])
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp h3) (hπ.1 x)
    have h1 := hπ.2.1
    have hz : π = fun _ => 0 := funext hall
    rw [hz] at h1
    exact one_ne_zero (h1.unique hasSum_zero)
  have hrec : Filter.Tendsto (fun t => g72mab_AV P none (fun z => z ≠ none) t)
      Filter.atTop (nhds 0) := by
    have h := (hpr none).1
    unfold RecurrentState at h
    simp only [g72mab_rt] at h
    exact h
  have hB : ∀ z, ns_In p z → z ≠ none := by rintro z ⟨l, m, rfl⟩; simp
  set y : TreeState ι := some (p, i) with hy
  have hyB : ns_In p y := ⟨[], i, by simp [hy]⟩
  have hmain := ns_main P hrow ν hinv hfin none hk0 hrec hirr (ns_In p) hB y
  set G : ι → ℝ≥0∞ := fun b =>
    ∑' t, g72mab_PS P (some ([], b)) t (some ([], i)) (fun w => w ≠ none) with hG
  have hGeq : ∀ b, ∑' L, g72mab_PS P (some (p, b)) L y (ns_In p) = G b := by
    intro b
    refine tsum_congr fun L => ?_
    have := ns_iso T p L [] b [] i
    simpa only [List.append_nil] using this
  set F : TreeState ι → TreeState ι → ℝ≥0∞ := fun x z =>
    if ns_In p x then 0 else if ns_In p z then
      ν x * ENNReal.ofReal (P x z) * ∑' L, g72mab_PS P z L y (ns_In p) else 0 with hF
  have hstep1 : ∀ x, ∑' L, (if ns_In p x then 0 else ν x * g72mab_PS P x (L + 1) y (ns_In p)) =
      ∑' z, F x z := by
    intro x
    by_cases hx : ns_In p x
    · simp [hF, hx]
    · simp only [hF, hx, if_false]
      simp_rw [g72mab_PS_cons P x _ y (ns_In p), ← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun z => ?_
      by_cases hz : ns_In p z
      · simp only [hz, or_true, if_true]
        simp_rw [← mul_assoc]
        try rw [ENNReal.tsum_mul_left]
      · simp only [hz, if_false, or_false]
        apply ENNReal.tsum_eq_zero.mpr
        intro L
        split_ifs with hL
        · subst hL
          rw [g72mab_PS_zero, if_neg (fun (h : z = y) => hz (h ▸ hyB))]; simp
        · simp
  have hsupp : ∀ x z, F x z ≠ 0 → ∃ a b, x = some (n, a) ∧ z = some (p, b) := by
    intro x z hF0
    simp only [hF] at hF0
    by_cases hx : ns_In p x
    · rw [if_pos hx] at hF0; exact absurd rfl hF0
    rw [if_neg hx] at hF0
    by_cases hz : ns_In p z
    · rw [if_pos hz] at hF0
      have hP0 : P x z ≠ 0 := by
        intro h0; apply hF0; rw [h0]; simp
      have hxz : z ≠ x := fun h => hx (h ▸ hz)
      have hg : gen T x z ≠ 0 := by
        intro h0; apply hP0
        simp only [hP, jumpP, if_neg (hq x).ne', if_neg hxz, h0, zero_div]
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ns_struct T n j x z hx hz hg
      exact ⟨a, b, ha, hb⟩
    · rw [if_neg hz] at hF0; exact absurd rfl hF0
  have hFval : ∀ a b, F (some (n, a)) (some (p, b)) =
      ENNReal.ofReal (π (some (n, a))) * ENNReal.ofReal (T.A j a b) * G b := by
    intro a b
    have h1 : ¬ ns_In p (some (n, a)) := by
      rintro ⟨l, m, e⟩
      have := congrArg (fun w => match w with | some q => q.1.length | none => 0) e
      simp [hp] at this
      try omega
    have h2 : ns_In p (some (p, b)) := ⟨[], b, by simp⟩
    simp only [hF, if_neg h1, if_pos h2, hGeq]
    congr 1
    have hne : ¬ ((some (n ++ [j], b) : TreeState ι) = some (n, a)) := by
      intro e; simp at e
    simp only [hν, hP, jumpP, if_neg (hq _).ne', hp, ns_gen_A]
    rw [if_neg hne]
    rw [mul_assoc, ← ENNReal.ofReal_mul (hq _).le]
    congr 2
    have := (hq (some (n, a))).ne'
    field_simp
  have hφ : Function.Injective (fun c : ι × ι =>
      ((some (n, c.1) : TreeState ι), (some (p, c.2) : TreeState ι))) := by
    intro c d h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact Prod.ext h.1.2 h.2.2
  have hsum : ν y = ∑' a, ∑' b, ENNReal.ofReal (π (some (n, a))) *
      ENNReal.ofReal (T.A j a b) * G b := by
    rw [hmain, ENNReal.tsum_comm]
    simp_rw [hstep1]
    rw [← ENNReal.tsum_prod (f := F), ← hφ.tsum_eq, ENNReal.tsum_prod']
    · dsimp only
      simp only [hFval]
    · intro w hw
      rw [Function.mem_support] at hw
      obtain ⟨a, b, ha, hb⟩ := hsupp w.1 w.2 hw
      exact ⟨(a, b), by
        show (some (n, a), some (p, b)) = w
        rw [← ha, ← hb]⟩
  -- conclude
  have hqy : holdRate (gen T) y = holdRate (gen T) (some ([], i)) := by
    have := ns_hold_shift T p [] i
    simpa only [List.append_nil] using this
  have hlhs : ENNReal.ofReal (π y) = ν y * ENNReal.ofReal (holdRate (gen T) (some ([], i)))⁻¹ := by
    simp only [hν]
    rw [hqy, mul_assoc, ← ENNReal.ofReal_mul (hq _).le, mul_inv_cancel₀ (hq _).ne',
      ENNReal.ofReal_one, mul_one]
  unfold nodeVec vecMulE ennMat
  simp_rw [un_N_eq]
  show ENNReal.ofReal (π y) = _
  rw [hlhs, hsum]
  set c := ENNReal.ofReal (holdRate (gen T) (some ([], i)))⁻¹ with hc
  change (∑' a, ∑' b, ENNReal.ofReal (π (some (n, a))) * ENNReal.ofReal (T.A j a b) * G b) * c =
    ∑' b, (∑' a, ENNReal.ofReal (π (some (n, a))) * ENNReal.ofReal (T.A j a b)) * (G b * c)
  calc _ = ∑' a, ∑' b, ENNReal.ofReal (π (some (n, a))) * ENNReal.ofReal (T.A j a b) * G b * c :=
        by rw [← ENNReal.tsum_mul_right]; exact tsum_congr fun a => ENNReal.tsum_mul_right.symm
    _ = ∑' b, ∑' a, ENNReal.ofReal (π (some (n, a))) * ENNReal.ofReal (T.A j a b) * G b * c :=
        ENNReal.tsum_comm
    _ = _ := by
        refine tsum_congr fun b => ?_
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun a => ?_
        ring

end Final

section Root
variable {ι : Type*} [Countable ι] [DecidableEq ι]

theorem ms_root (T : TreeData ι) (hT : IsTreeProcess T)
    (hpr : IsPositiveRecurrentProcess (gen T))
    (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) (i : ι) :
    ENNReal.ofReal (π (some ([], i))) = vecMulE (rootVec T π) (matN T) i := by
  classical
  set P := jumpP (gen T) with hP
  set ν : TreeState ι → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate (gen T) x) with hν
  set p := ([] : List ι) with hp
  have hq := ns_qpos T hT i
  have hrow := g72mab_jrow (gen T) hT.1
  have hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y := ns_inv T hT i π hπ
  have hfin : ∀ y, ν y ≠ ⊤ := fun y =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hirr : ∀ x, ∃ L, g72mab_PS P x L none (fun _ => True) ≠ 0 :=
    fun x => g72mab_jpos (gen T) hT.1 x none (hT.2 x none)
  have hk0 : ν none ≠ 0 := by
    intro h0
    have hall : ∀ x, π x = 0 := by
      intro x
      obtain ⟨L, hL⟩ := hirr x
      have h1 := ns_sub_iter P ν hinv L x none
      rw [h0] at h1
      have h2 : ν x = 0 := by
        rcases mul_eq_zero.mp (le_antisymm h1 bot_le) with h | h
        · exact h
        · exact absurd h hL
      have h3 : ENNReal.ofReal (π x) = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h (by simp [hq x])
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp h3) (hπ.1 x)
    have h1 := hπ.2.1
    have hz : π = fun _ => 0 := funext hall
    rw [hz] at h1
    exact one_ne_zero (h1.unique hasSum_zero)
  have hrec : Filter.Tendsto (fun t => g72mab_AV P none (fun z => z ≠ none) t)
      Filter.atTop (nhds 0) := by
    have h := (hpr none).1
    unfold RecurrentState at h
    simp only [g72mab_rt] at h
    exact h
  have hB : ∀ z, ns_In p z → z ≠ none := by rintro z ⟨l, m, rfl⟩; simp
  set y : TreeState ι := some (p, i) with hy
  have hyB : ns_In p y := ⟨[], i, by simp [hy]⟩
  have hmain := ns_main P hrow ν hinv hfin none hk0 hrec hirr (ns_In p) hB y
  set G : ι → ℝ≥0∞ := fun b =>
    ∑' t, g72mab_PS P (some ([], b)) t (some ([], i)) (fun w => w ≠ none) with hG
  have hGeq : ∀ b, ∑' L, g72mab_PS P (some (p, b)) L y (ns_In p) = G b := by
    intro b
    refine tsum_congr fun L => ?_
    have := ns_iso T p L [] b [] i
    simpa only [List.append_nil] using this
  set F : TreeState ι → TreeState ι → ℝ≥0∞ := fun x z =>
    if ns_In p x then 0 else if ns_In p z then
      ν x * ENNReal.ofReal (P x z) * ∑' L, g72mab_PS P z L y (ns_In p) else 0 with hF
  have hstep1 : ∀ x, ∑' L, (if ns_In p x then 0 else ν x * g72mab_PS P x (L + 1) y (ns_In p)) =
      ∑' z, F x z := by
    intro x
    by_cases hx : ns_In p x
    · simp [hF, hx]
    · simp only [hF, hx, if_false]
      simp_rw [g72mab_PS_cons P x _ y (ns_In p), ← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun z => ?_
      by_cases hz : ns_In p z
      · simp only [hz, or_true, if_true]
        simp_rw [← mul_assoc]
        try rw [ENNReal.tsum_mul_left]
      · simp only [hz, if_false, or_false]
        apply ENNReal.tsum_eq_zero.mpr
        intro L
        split_ifs with hL
        · subst hL
          rw [g72mab_PS_zero, if_neg (fun (h : z = y) => hz (h ▸ hyB))]; simp
        · simp
  have hsupp : ∀ x z, F x z ≠ 0 → x = none ∧ ∃ b, z = some (p, b) := by
    intro x z hF0
    simp only [hF] at hF0
    by_cases hx : ns_In p x
    · rw [if_pos hx] at hF0; exact absurd rfl hF0
    rw [if_neg hx] at hF0
    have hxn : x = none := by
      rcases x with _ | ⟨l, m⟩
      · rfl
      · exact absurd ⟨l, m, by simp [hp]⟩ hx
    subst hxn
    by_cases hz : ns_In p z
    · rw [if_pos hz] at hF0
      have hP0 : P none z ≠ 0 := by
        intro h0; apply hF0; rw [h0]; simp
      have hxz : z ≠ none := hB z hz
      have hg : gen T none z ≠ 0 := by
        intro h0; apply hP0
        simp only [hP, jumpP, if_neg (hq none).ne', if_neg hxz, h0, zero_div]
      obtain ⟨l, b, rfl⟩ := hz
      refine ⟨rfl, b, ?_⟩
      by_cases hl : l = []
      · subst hl; simp [hp]
      · exfalso; apply hg; simp [gen, hp, hl]
    · rw [if_neg hz] at hF0; exact absurd rfl hF0
  have hFval : ∀ b, F none (some (p, b)) =
      ENNReal.ofReal (π none) * ENNReal.ofReal (T.a b) * G b := by
    intro b
    have h1 : ¬ ns_In p (none : TreeState ι) := by
      rintro ⟨l, m, e⟩; simp at e
    have h2 : ns_In p (some (p, b)) := ⟨[], b, by simp⟩
    simp only [hF, if_neg h1, if_pos h2, hGeq]
    congr 1
    have hne : ¬ ((some (p, b) : TreeState ι) = none) := by simp
    have hga : gen T none (some (p, b)) = T.a b := by simp [gen, hp]
    simp only [hν, hP, jumpP, if_neg (hq _).ne', hga]
    try rw [if_neg hne]
    rw [mul_assoc, ← ENNReal.ofReal_mul (hq _).le]
    congr 2
    have := (hq (none : TreeState ι)).ne'
    field_simp
  have hφ : Function.Injective (fun b : ι =>
      ((none : TreeState ι), (some (p, b) : TreeState ι))) := by
    intro c d h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact h.2.2
  have hsum : ν y = ∑' b, ENNReal.ofReal (π none) * ENNReal.ofReal (T.a b) * G b := by
    rw [hmain, ENNReal.tsum_comm]
    simp_rw [hstep1]
    rw [← ENNReal.tsum_prod (f := F), ← hφ.tsum_eq]
    · dsimp only
      simp only [hFval]
    · intro w hw
      rw [Function.mem_support] at hw
      obtain ⟨ha, b, hb⟩ := hsupp w.1 w.2 hw
      exact ⟨b, by
        show (none, some (p, b)) = w
        rw [← ha, ← hb]⟩
  have hlhs : ENNReal.ofReal (π y) = ν y * ENNReal.ofReal (holdRate (gen T) (some ([], i)))⁻¹ := by
    simp only [hν, hy, hp]
    rw [mul_assoc, ← ENNReal.ofReal_mul (hq _).le, mul_inv_cancel₀ (hq _).ne',
      ENNReal.ofReal_one, mul_one]
  unfold vecMulE rootVec
  simp_rw [un_N_eq]
  show ENNReal.ofReal (π y) = _
  rw [hlhs, hsum, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun b => ?_
  rw [ENNReal.ofReal_mul (hπ.1 none)]
  ring

end Root

section Marg
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma ms_marg (T : TreeData ι) (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) (n : ℕ) (j : ι) :
    ENNReal.ofReal (stackMarginal π n j) =
      ∑' l : List ι, if l.length + 1 = n then ENNReal.ofReal (π (some (l, j))) else 0 := by
  classical
  have hinj : Function.Injective (fun l : List ι => (some (l, j) : TreeState ι)) := by
    intro a b h; simpa using h
  have hs : Summable (fun l : List ι => π (some (l, j))) :=
    hπ.2.1.summable.comp_injective hinj
  have hs2 : Summable (fun l : List ι => if l.length + 1 = n then π (some (l, j)) else 0) := by
    refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) hs
    · split_ifs
      · exact hπ.1 _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hπ.1 _
  unfold stackMarginal
  rw [ENNReal.ofReal_tsum_of_nonneg (fun l => by split_ifs; exact hπ.1 _; exact le_rfl) hs2]
  refine tsum_congr fun l => ?_
  split_ifs <;> simp

lemma ms_assoc (v : ι → ℝ≥0∞) (A M : ι → ι → ℝ≥0∞) (j : ι) :
    vecMulE v (matMulE A M) j = vecMulE (vecMulE v A) M j := by
  unfold vecMulE matMulE
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => tsum_congr fun i => ?_
  ring

lemma ms_step (T : TreeData ι) (hT : IsTreeProcess T)
    (hpr : IsPositiveRecurrentProcess (gen T))
    (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) (n : ℕ) (hn : 1 ≤ n) (j : ι) :
    ENNReal.ofReal (stackMarginal π (n + 1) j) =
      vecMulE (fun k => ENNReal.ofReal (stackMarginal π n k)) (matR T) j := by
  classical
  set c : List ι → ι → ℝ≥0∞ := fun l a =>
    if l.length + 1 = n then ENNReal.ofReal (π (some (l, a))) else 0 with hc
  have hg : Function.Injective (fun q : List ι × ι => q.1 ++ [q.2]) := by
    intro q r h
    have h1 := congrArg List.dropLast h
    have h2 := congrArg List.getLast? h
    simp only [List.dropLast_concat] at h1
    simp at h2
    exact Prod.ext h1 h2
  have hL : ENNReal.ofReal (stackMarginal π (n + 1) j) =
      ∑' l', ∑' k, if l'.length + 1 = n then ENNReal.ofReal (π (some (l' ++ [k], j))) else 0 := by
    rw [ms_marg (T := T) π hπ, ← ENNReal.tsum_prod, ← hg.tsum_eq]
    · refine tsum_congr fun q => ?_
      simp
    · intro l hl
      rw [Function.mem_support] at hl
      have hlen : l.length + 1 = n + 1 := by
        by_contra h; exact hl (if_neg h)
      have hne : l ≠ [] := by
        intro h; subst h; simp at hlen; omega
      exact ⟨(l.dropLast, l.getLast hne), List.dropLast_append_getLast hne⟩
  have hterm : ∀ l' k, (if l'.length + 1 = n then ENNReal.ofReal (π (some (l' ++ [k], j))) else 0)
      = ∑' b, ∑' a, c l' a * ENNReal.ofReal (T.A k a b) * matN T b j := by
    intro l' k
    have := ns_final T hT hpr π hπ l' k j
    unfold nodeVec vecMulE ennMat at this
    simp only [hc]
    split_ifs
    · rw [this]
      refine tsum_congr fun b => ?_
      rw [← ENNReal.tsum_mul_right]
    · simp
  rw [hL]
  simp_rw [hterm]
  unfold vecMulE matR matRi matMulE ennMat
  simp_rw [ms_marg (T := T) π hπ n]
  change _ = ∑' a, (∑' l', c l' a) * _
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun l' => ?_
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

end Marg

end S202MS

open MatrixAnalytic.Tree in
open scoped ENNReal in
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (hpr : IsPositiveRecurrentProcess (gen T))
    (π : TreeState ι → ℝ) (hπ : IsStationaryCT (gen T) π) :
    (∀ j : ι, ENNReal.ofReal (stackMarginal π 1 j) = vecMulE (rootVec T π) (matN T) j) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ j : ι,
        ENNReal.ofReal (stackMarginal π n j) =
          vecMulE (fun k => ENNReal.ofReal (stackMarginal π 1 k)) (matPowE (matR T) (n - 1)) j := by
  classical
  constructor
  · intro j
    rw [S202MS.ms_marg (T := T) π hπ, tsum_eq_single []]
    · simpa using S202MS.ms_root T hT hpr π hπ j
    · intro l hl
      rw [if_neg]
      intro h; apply hl; simpa using h
  · intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro j
      show _ = ∑' i, _ * (if i = j then 1 else 0)
      rw [tsum_eq_single j]
      · simp
      · intro b hb; simp [hb]
    | succ n hn ih =>
      intro j
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [show m + 1 + 1 - 1 = m + 1 by omega]
      show _ = vecMulE _ (matMulE _ _) j
      rw [S202MS.ms_assoc, S202MS.ms_step T hT hpr π hπ (m + 1) hn j]
      congr 1
      funext k
      rw [ih k]
      rfl
