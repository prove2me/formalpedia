-- Prove2me | solution 1 for MatrixAnalytic.ProductForm.ct_matrix_geometric
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:47:24.815751+00:00
-- url     : https://prove2.me/submissions/e5745367-cf22-4baf-954b-84199dcb8a63

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_MatrixAnalytic_ProductForm_QBD

open scoped ENNReal
open MatrixAnalytic.ProductForm

set_option linter.unusedSectionVars false

namespace S202CG

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

lemma cg_qpos (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (x : V) : 0 < holdRate Q x := by
  unfold holdRate; linarith [hQ.2.1 x]

lemma cg_qsum (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (x : V) :
    HasSum (fun y => if y = x then 0 else Q x y) (holdRate Q x) := by
  have h := (hQ.2.2 x).sub (hasSum_ite_eq x (Q x x))
  have e : (fun y => if y = x then 0 else Q x y) = fun y => Q x y - (if y = x then Q x x else 0) := by
    funext y; by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  rw [e, show holdRate Q x = 0 - Q x x by simp [holdRate]]
  exact h

lemma cg_jnn (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (x y : V) : 0 ≤ jumpP Q x y := by
  unfold jumpP
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (hQ.1 x y (Ne.symm h)) (cg_qpos Q hQ x).le

lemma cg_jrow (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (x : V) :
    ∑' y, ENNReal.ofReal (jumpP Q x y) = 1 := by
  have hq := cg_qpos Q hQ x
  have hs := (cg_qsum Q hQ x).div_const (holdRate Q x)
  rw [div_self hq.ne'] at hs
  have e : (fun y => (if y = x then 0 else Q x y) / holdRate Q x) = jumpP Q x := by
    funext y; unfold jumpP; split_ifs <;> simp
  rw [e] at hs
  rw [← ENNReal.ofReal_tsum_of_nonneg (cg_jnn Q hQ x) hs.summable, hs.tsum_eq, ENNReal.ofReal_one]

lemma cg_PQ (Q : V → V → ℝ) (x z : V) (h : jumpP Q x z ≠ 0) : Q x z ≠ 0 := by
  unfold jumpP at h
  split_ifs at h
  · exact absurd rfl h
  · intro h0; rw [h0, zero_div] at h; exact h rfl

lemma cg_W_eq (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) {t : ℕ} (ω : Fin (t + 1) → V) :
    g72mab_W P ω = ENNReal.ofReal (pathWeightC P ω) := by
  unfold g72mab_W pathWeightC
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hP _ _)]

lemma cg_rt (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (x : V) (t : ℕ) :
    g72mab_AV (jumpP Q) x (fun z => z ≠ x) t = ENNReal.ofReal (returnTailC (jumpP Q) x t) := by
  classical
  have hP := cg_jnn Q hQ
  set f : (Fin (t + 1) → V) → ℝ := fun ω => if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 →
    ω i ∉ ({x} : Set V) then pathWeightC (jumpP Q) ω else 0 with hf
  have hfn : ∀ ω, 0 ≤ f ω := fun ω => by
    simp only [hf]
    split_ifs
    · exact Finset.prod_nonneg fun i _ => hP _ _
    · exact le_rfl
  have hAV : g72mab_AV (jumpP Q) x (fun z => z ≠ x) t = ∑' ω, ENNReal.ofReal (f ω) := by
    unfold g72mab_AV
    refine tsum_congr fun ω => ?_
    simp only [hf, Set.mem_singleton_iff]
    split_ifs <;> simp [cg_W_eq _ hP]
  have hle : g72mab_AV (jumpP Q) x (fun z => z ≠ x) t ≠ ⊤ := by
    have := g72mab_mass (jumpP Q) (cg_jrow Q hQ) x (fun z => z ≠ x) t
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (this ▸ le_self_add)
  rw [hAV] at hle ⊢
  have hs : Summable f := by
    have := ENNReal.summable_toReal hle
    simpa [ENNReal.toReal_ofReal (hfn _)] using this
  unfold returnTailC setAvoidTailC
  convert (ENNReal.ofReal_tsum_of_nonneg hfn hs).symm using 4
  rename_i ω
  simp only [hf]
  split_ifs <;> rfl

lemma cg_irr_aux (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (x : V) :
    ∀ t y, g72mab_PS P x t y (fun _ => True) = 0 → stepPow P t x y = 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro y h
    rw [g72mab_PS_zero] at h
    simp only [stepPow]
    by_cases hxy : x = y
    · subst hxy; simp at h
    · rw [if_neg (Ne.symm hxy)]
  | succ t ih =>
    intro y h
    rw [g72mab_PS_snoc] at h
    have h0 := ENNReal.tsum_eq_zero.mp h
    simp only [stepPow]
    have : ∀ z, stepPow P t x z * P z y = 0 := by
      intro z
      have hz := h0 z
      rw [if_pos (Or.inr trivial)] at hz
      rcases mul_eq_zero.mp hz with h1 | h1
      · rw [ih z h1, zero_mul]
      · rw [le_antisymm (ENNReal.ofReal_eq_zero.mp h1) (hP z y), mul_zero]
    simp [this]

lemma cg_irr (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (h : IrreducibleCT Q) (x y : V) :
    ∃ L, g72mab_PS (jumpP Q) x L y (fun _ => True) ≠ 0 := by
  obtain ⟨t, ht⟩ := h x y
  exact ⟨t, fun h0 => by rw [cg_irr_aux _ (cg_jnn Q hQ) x t y h0] at ht; exact lt_irrefl _ ht⟩

lemma cg_inv (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (π : V → ℝ)
    (hπ : IsStationaryCT Q π) (y : V) :
    ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate Q x) *
      ENNReal.ofReal (jumpP Q x y) =
      ENNReal.ofReal (π y) * ENNReal.ofReal (holdRate Q y) := by
  classical
  have hq := cg_qpos Q hQ
  set g : V → ℝ := fun x => if x = y then 0 else π x * Q x y with hg
  have hgs : HasSum g (π y * holdRate Q y) := by
    have h := (hπ.2.2 y).sub (hasSum_ite_eq y (π y * Q y y))
    have e1 : g = fun x => π x * Q x y - if x = y then π y * Q y y else 0 := by
      funext x
      by_cases hx : x = y
      · subst hx; simp [hg]
      · simp [hg, hx]
    rw [e1, show π y * holdRate Q y = 0 - π y * Q y y by simp [holdRate]]
    exact h
  have hgn : ∀ x, 0 ≤ g x := fun x => by
    simp only [hg]
    split_ifs with hx
    · exact le_rfl
    · exact mul_nonneg (hπ.1 x) (hQ.1 x y hx)
  have hterm : ∀ x, ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate Q x) *
      ENNReal.ofReal (jumpP Q x y) = ENNReal.ofReal (g x) := by
    intro x
    unfold jumpP
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

lemma cg_soj (Q : V → V → ℝ) (T : Set V) (x y : V) (hy : y ∉ T) :
    sojournAvoid Q T x y = (∑' t, g72mab_PS (jumpP Q) x t y (fun z => z ∉ T)) *
      (ENNReal.ofReal (holdRate Q y))⁻¹ := by
  classical
  unfold sojournAvoid g72mab_PS
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun t => ?_
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun ω => ?_
  by_cases h1 : ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T
  · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, fun m hm _ => h1.2.2 m hm⟩]; rfl
  · rw [if_neg h1, if_neg, zero_mul]
    intro h2
    refine h1 ⟨h2.1, h2.2.1, fun m hm => ?_⟩
    by_cases hml : m = Fin.last t
    · rw [hml, h2.2.1]; exact hy
    · exact h2.2.2 m hm hml

end TR

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

section QBD
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma cg_Q_ne (x z : ℕ × ι) (h : qbdQ B A₀ A₁ A₂ x z ≠ 0) :
    z.1 ≤ x.1 + 1 ∧ x.1 ≤ z.1 + 1 := by
  unfold qbdQ at h
  split_ifs at h <;> first | omega | exact absurd rfl h | contradiction

lemma cg_Q_up (n : ℕ) (a b : ι) : qbdQ B A₀ A₁ A₂ (n, a) (n + 1, b) = A₀ a b := by
  unfold qbdQ
  dsimp only
  split_ifs <;> first | rfl | omega | contradiction

lemma cg_Q_shift (d l l' : ℕ) (a b : ι) (hl : 1 ≤ l) :
    qbdQ B A₀ A₁ A₂ (l + d, a) (l' + d, b) = qbdQ B A₀ A₁ A₂ (l, a) (l', b) := by
  unfold qbdQ
  dsimp only
  split_ifs <;> first | rfl | omega | contradiction

lemma cg_hold_shift (d l : ℕ) (a : ι) (hl : 1 ≤ l) :
    holdRate (qbdQ B A₀ A₁ A₂) (l + d, a) = holdRate (qbdQ B A₀ A₁ A₂) (l, a) := by
  unfold holdRate; rw [cg_Q_shift B A₀ A₁ A₂ d l l a a hl]

lemma cg_P_shift (d l l' : ℕ) (a b : ι) (hl : 1 ≤ l) :
    jumpP (qbdQ B A₀ A₁ A₂) (l + d, a) (l' + d, b) = jumpP (qbdQ B A₀ A₁ A₂) (l, a) (l', b) := by
  unfold jumpP
  rw [cg_hold_shift B A₀ A₁ A₂ d l a hl, cg_Q_shift B A₀ A₁ A₂ d l l' a b hl]
  simp only [Prod.mk.injEq, Nat.add_right_cancel_iff]

lemma cg_skip (d : ℕ) (y : ℕ × ι) : ∀ t (x : ℕ × ι), d < x.1 →
    g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) x t y (fun z => z.1 ≠ d) =
      g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) x t y (fun z => d < z.1) := by
  classical
  intro t
  induction t with
  | zero => intro x _; rw [g72mab_PS_zero, g72mab_PS_zero]
  | succ t ih =>
    intro x hx
    rw [g72mab_PS_cons, g72mab_PS_cons]
    refine tsum_congr fun z => ?_
    by_cases hP : jumpP (qbdQ B A₀ A₁ A₂) x z = 0
    · simp [hP]
    · have hz := (cg_Q_ne B A₀ A₁ A₂ x z (cg_PQ _ x z hP)).2
      by_cases hzd : z.1 = d
      · by_cases ht : t = 0
        · subst ht
          rw [if_pos (Or.inl rfl), if_pos (Or.inl rfl), g72mab_PS_zero, g72mab_PS_zero]
        · have h1 : ¬ (t = 0 ∨ z.1 ≠ d) := by tauto
          have h2 : ¬ (t = 0 ∨ d < z.1) := by omega
          rw [if_neg h1, if_neg h2]
      · have hzd' : d < z.1 := by omega
        rw [if_pos (Or.inr hzd), if_pos (Or.inr hzd'), ih z hzd']

lemma cg_iso (d : ℕ) : ∀ t (l : ℕ) (a : ι) (l' : ℕ) (b : ι), 1 ≤ l → 1 ≤ l' →
    g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (l + d, a) t (l' + d, b) (fun z => d < z.1) =
      g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (l, a) t (l', b) (fun z => 0 < z.1) := by
  classical
  intro t
  induction t with
  | zero =>
    intro l a l' b _ _
    rw [g72mab_PS_zero, g72mab_PS_zero]
    simp only [Prod.mk.injEq, Nat.add_right_cancel_iff]
  | succ t ih =>
    intro l a l' b hl hl'
    rw [g72mab_PS_cons, g72mab_PS_cons]
    have hf : Function.Injective (fun w : ℕ × ι => ((w.1 + d, w.2) : ℕ × ι)) := by
      intro w w' h
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
      exact Prod.ext h.1 h.2
    rw [← hf.tsum_eq]
    · refine tsum_congr fun w => ?_
      obtain ⟨m, c⟩ := w
      dsimp only
      rw [cg_P_shift B A₀ A₁ A₂ d l m a c hl]
      have key : (if t = 0 ∨ d < m + d then g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (m + d, c) t
            (l' + d, b) (fun z => d < z.1) else 0)
          = (if t = 0 ∨ 0 < m then g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (m, c) t (l', b)
            (fun z => 0 < z.1) else 0) := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          rcases Nat.eq_zero_or_pos t with ht | ht
          · subst ht
            rw [if_pos (Or.inl rfl), if_pos (Or.inl rfl), g72mab_PS_zero, g72mab_PS_zero,
              if_neg, if_neg]
            · intro h; simp only [Prod.mk.injEq] at h; omega
            · intro h; simp only [Prod.mk.injEq] at h; omega
          · rw [if_neg (by omega), if_neg (by omega)]
        · rw [if_pos (Or.inr (by omega)), if_pos (Or.inr hm), ih m c l' b hm hl']
      exact congrArg (fun u => ENNReal.ofReal (jumpP (qbdQ B A₀ A₁ A₂) (l, a) (m, c)) * u) key
    · intro z hz
      rw [Function.mem_support] at hz
      have hP : jumpP (qbdQ B A₀ A₁ A₂) (l + d, a) z ≠ 0 := by
        intro h0; apply hz; rw [h0]; simp
      have h2 := (cg_Q_ne B A₀ A₁ A₂ _ z (cg_PQ _ _ z hP)).2
      dsimp only at h2
      exact ⟨(z.1 - d, z.2), Prod.ext (by dsimp only; omega) rfl⟩

lemma cg_far (n : ℕ) (y : ℕ × ι) (hy : n < y.1) (x : ℕ × ι) (hx : x.1 < n) (L : ℕ) :
    g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) x (L + 1) y (fun z => n < z.1) = 0 := by
  classical
  rw [g72mab_PS_cons]
  refine ENNReal.tsum_eq_zero.mpr fun z => ?_
  by_cases hz : n < z.1
  · have : jumpP (qbdQ B A₀ A₁ A₂) x z = 0 := by
      by_contra hP
      have := (cg_Q_ne B A₀ A₁ A₂ x z (cg_PQ _ x z hP)).1
      omega
    simp [this]
  · rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL
      rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg (fun h => hz (by rw [h]; exact hy)), mul_zero]
    · have : ¬ (L = 0 ∨ n < z.1) := by omega
      rw [if_neg this, mul_zero]

/-- entries into levels `> n` from `(n, a)` -/
lemma cg_entry (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂)) (n : ℕ) (a j : ι) :
    ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (n, a)) *
      ∑' L, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (n, a) (L + 1) (n + 1, j) (fun z => n < z.1) =
    ∑' b, ENNReal.ofReal (A₀ a b) *
      ∑' L, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (n + 1, b) L (n + 1, j) (fun z => n < z.1) := by
  classical
  set Q := qbdQ B A₀ A₁ A₂ with hQd
  set P := jumpP Q with hPd
  set y : ℕ × ι := (n + 1, j) with hy
  set G : ℕ × ι → ℝ≥0∞ := fun z => ∑' L, g72mab_PS P z L y (fun z => n < z.1) with hG
  have h1 : ∑' L, g72mab_PS P (n, a) (L + 1) y (fun z => n < z.1) =
      ∑' z, ENNReal.ofReal (P (n, a) z) * (if n < z.1 then G z else 0) := by
    simp_rw [g72mab_PS_cons P (n, a) _ y (fun z => n < z.1)]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    by_cases hz : n < z.1
    · rw [if_pos hz, hG, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun L => ?_
      rw [if_pos (Or.inr hz)]
    · rw [if_neg hz, mul_zero]
      refine ENNReal.tsum_eq_zero.mpr fun L => ?_
      rcases Nat.eq_zero_or_pos L with hL | hL
      · subst hL
        rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg (fun h => hz (by rw [h, hy]; exact Nat.lt_succ_self n)), mul_zero]
      · have : ¬ (L = 0 ∨ n < z.1) := by omega
        rw [if_neg this, mul_zero]
  have hf : Function.Injective (fun b : ι => ((n + 1, b) : ℕ × ι)) := by
    intro b b' h; simpa using h
  rw [h1, ← hf.tsum_eq, ← ENNReal.tsum_mul_left]
  · refine tsum_congr fun b => ?_
    dsimp only
    rw [if_pos (Nat.lt_succ_self n), ← mul_assoc, ← ENNReal.ofReal_mul (cg_qpos Q hQ _).le]
    congr 2
    have hne : ((n + 1, b) : ℕ × ι) ≠ (n, a) := by simp
    simp only [hPd, jumpP, if_neg hne, hQd, cg_Q_up]
    have := (cg_qpos Q hQ (n, a)).ne'
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ this
  · intro z hz
    rw [Function.mem_support] at hz
    have hzn : n < z.1 := by
      by_contra hc; apply hz; rw [if_neg hc, mul_zero]
    have hP : P (n, a) z ≠ 0 := by
      intro h0; apply hz; rw [h0]; simp
    have h2 := (cg_Q_ne B A₀ A₁ A₂ _ z (cg_PQ _ _ z hP)).1
    dsimp only at h2
    exact ⟨z.2, Prod.ext (by dsimp only; omega) rfl⟩

lemma cg_rateS (n : ℕ) (a j : ι) :
    rateR (qbdQ B A₀ A₁ A₂) n a j = ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (n, a)) *
      (∑' L, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (n, a) (L + 1) (n + 1, j) (fun z => n < z.1)) *
      (ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (n + 1, j)))⁻¹ := by
  classical
  unfold rateR
  rw [cg_soj _ _ _ _ (by simp [levelsUpTo])]
  have e : (fun z : ℕ × ι => z ∉ levelsUpTo n) = fun z => n < z.1 := by
    funext z; simp [levelsUpTo, not_le]
  rw [e, tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero, if_neg (by simp), zero_add, mul_assoc]

lemma cg_Nform (n : ℕ) (b j : ι) :
    matNct (qbdQ B A₀ A₁ A₂) (n + 1) b j =
      (∑' t, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (n + 1, b) t (n + 1, j) (fun z => n < z.1)) *
      (ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (n + 1, j)))⁻¹ := by
  classical
  unfold matNct
  rw [Nat.add_sub_cancel, cg_soj _ _ _ _ (by simp [level])]
  have e : (fun z : ℕ × ι => z ∉ level n) = fun z => z.1 ≠ n := by
    funext z; simp [level]
  rw [e]
  congr 1
  exact tsum_congr fun t => cg_skip B A₀ A₁ A₂ n _ t _ (Nat.lt_succ_self n)

lemma cg_Nhom (m : ℕ) (b j : ι) :
    matNct (qbdQ B A₀ A₁ A₂) (m + 1) b j =
      (∑' t, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (1, b) t (1, j) (fun z => 0 < z.1)) *
      (ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (1, j)))⁻¹ := by
  rw [cg_Nform]
  have h1 := cg_hold_shift B A₀ A₁ A₂ m 1 j le_rfl
  rw [Nat.add_comm 1 m] at h1
  rw [h1]
  congr 1
  refine tsum_congr fun t => ?_
  have h2 := cg_iso B A₀ A₁ A₂ m t 1 b 1 j le_rfl le_rfl
  rw [Nat.add_comm 1 m] at h2
  exact h2

lemma cg_rate (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂)) (n : ℕ) (a j : ι) :
    rateR (qbdQ B A₀ A₁ A₂) n a j =
      ∑' b, ENNReal.ofReal (A₀ a b) * matNct (qbdQ B A₀ A₁ A₂) 1 b j := by
  rw [cg_rateS, cg_entry B A₀ A₁ A₂ hQ, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun b => ?_
  rw [mul_assoc]
  congr 1
  rw [← cg_Nform B A₀ A₁ A₂ n b j, cg_Nhom]
  exact (cg_Nhom B A₀ A₁ A₂ 0 b j).symm

end QBD

section Final
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma cg_assoc (v : ι → ℝ≥0∞) (M M' : ι → ι → ℝ≥0∞) :
    vecMulE (vecMulE v M) M' = vecMulE v (matMulE M M') := by
  funext j
  unfold vecMulE matMulE
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => tsum_congr fun i => ?_
  ring

lemma cg_one (v : ι → ℝ≥0∞) : vecMulE v matOneE = v := by
  funext j
  unfold vecMulE matOneE
  rw [tsum_eq_single j]
  · simp
  · intro b hb; simp [hb]

theorem cg_main (B A₀ A₁ A₂ : ι → ι → ℝ) (π : ℕ × ι → ℝ)
    (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂))
    (hirr : IrreducibleCT (qbdQ B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrentCT (qbdQ B A₀ A₁ A₂) x)
    (hπ : IsStationaryCT (qbdQ B A₀ A₁ A₂) π) :
    ∃ R N : ι → ι → ℝ, (∀ i j, 0 ≤ R i j) ∧ (∀ i j, 0 ≤ N i j) ∧
      (∀ n : ℕ, rateR (qbdQ B A₀ A₁ A₂) n = ennMat R) ∧
      (∀ n : ℕ, 1 ≤ n → matNct (qbdQ B A₀ A₁ A₂) n = ennMat N) ∧
      matMulE (ennMat A₀) (ennMat N) = ennMat R ∧
      (∀ n : ℕ, ∀ j : ι, ENNReal.ofReal (π (n, j)) =
        vecMulE (fun i => ENNReal.ofReal (π (0, i))) (matPowE (ennMat R) n) j) := by
  classical
  set ν : ℕ × ι → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) x) with hν
  have hq := cg_qpos (qbdQ B A₀ A₁ A₂) hQ
  have hrow := cg_jrow (qbdQ B A₀ A₁ A₂) hQ
  have hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (jumpP (qbdQ B A₀ A₁ A₂) x y) = ν y :=
    cg_inv (qbdQ B A₀ A₁ A₂) hQ π hπ
  have hfin : ∀ y, ν y ≠ ⊤ := fun y =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hirr' : ∀ x y, ∃ L, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) x L y (fun _ => True) ≠ 0 :=
    cg_irr (qbdQ B A₀ A₁ A₂) hQ hirr
  obtain ⟨x0⟩ : Nonempty (ℕ × ι) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact one_ne_zero (hπ.2.1.unique hasSum_empty)
  set k : ℕ × ι := (0, x0.2) with hk
  have hk0 : ν k ≠ 0 := by
    intro h0
    have hall : ∀ x, π x = 0 := by
      intro x
      obtain ⟨L, hL⟩ := hirr' x k
      have h1 := ns_sub_iter (jumpP (qbdQ B A₀ A₁ A₂)) ν hinv L x k
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
  have hrec : Filter.Tendsto (fun t => g72mab_AV (jumpP (qbdQ B A₀ A₁ A₂)) k (fun z => z ≠ k) t)
      Filter.atTop (nhds 0) := by
    have h := (hpos k).1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr fun t => ?_
    exact (cg_rt (qbdQ B A₀ A₁ A₂) hQ k t).symm
  have hkk := ns_gam_kk (jumpP (qbdQ B A₀ A₁ A₂)) hrow k hrec
  have hu := ns_uniq (jumpP (qbdQ B A₀ A₁ A₂)) ν hinv hfin k hkk (fun x => hirr' x k)
  have hνpos : ∀ x, ν x ≠ 0 := by
    intro x h0
    obtain ⟨L, hL⟩ := hirr' k x
    have h1 := ns_sub_iter (jumpP (qbdQ B A₀ A₁ A₂)) ν hinv L k x
    rw [h0] at h1
    exact (mul_ne_zero hk0 hL) (le_antisymm h1 bot_le)
  have hπpos : ∀ x, ENNReal.ofReal (π x) ≠ 0 := fun x h => hνpos x (by simp [hν, h])
  -- the matrix-geometric step
  have hstep : ∀ n j, ENNReal.ofReal (π (n + 1, j)) =
      ∑' a, ENNReal.ofReal (π (n, a)) * rateR (qbdQ B A₀ A₁ A₂) n a j := by
    intro n j
    have hB : ∀ z : ℕ × ι, n < z.1 → z ≠ k := by
      intro z hz h; rw [h] at hz; simp [hk] at hz
    have hmain := ns_main (jumpP (qbdQ B A₀ A₁ A₂)) hrow ν hinv hfin k hk0 hrec
      (fun x => hirr' x k) (fun z => n < z.1) hB (n + 1, j)
    set S : ℕ × ι → ℝ≥0∞ := fun x =>
      ∑' L, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) x (L + 1) (n + 1, j) (fun z => n < z.1) with hS
    have h1 : ν (n + 1, j) = ∑' x, (if n < x.1 then 0 else ν x * S x) := by
      rw [hmain, ENNReal.tsum_comm]
      refine tsum_congr fun x => ?_
      split_ifs
      · simp
      · rw [hS, ENNReal.tsum_mul_left]
    have hf : Function.Injective (fun a : ι => ((n, a) : ℕ × ι)) := fun a b h => by simpa using h
    have h2 : ν (n + 1, j) = ∑' a, ν (n, a) * S (n, a) := by
      rw [h1, ← hf.tsum_eq]
      · refine tsum_congr fun a => ?_
        dsimp only
        rw [if_neg (lt_irrefl n)]
      · intro x hx
        rw [Function.mem_support] at hx
        have hxn : ¬ n < x.1 := by intro h; apply hx; rw [if_pos h]
        have hxn' : ¬ x.1 < n := by
          intro h; apply hx
          rw [if_neg hxn, hS]
          simp only [cg_far B A₀ A₁ A₂ n (n + 1, j) (Nat.lt_succ_self n) x h, tsum_zero, mul_zero]
        exact ⟨x.2, Prod.ext (by dsimp only; omega) rfl⟩
    have hlhs : ENNReal.ofReal (π (n + 1, j)) =
        ν (n + 1, j) * (ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (n + 1, j)))⁻¹ := by
      simp only [hν]
      rw [mul_assoc, ENNReal.mul_inv_cancel (by simp [hq (n + 1, j)]) ENNReal.ofReal_ne_top, mul_one]
    rw [hlhs, h2, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [cg_rateS]
    simp only [hν, hS]
    ring
  -- finiteness of N
  have hNfin : ∀ b j, matNct (qbdQ B A₀ A₁ A₂) 1 b j ≠ ⊤ := by
    intro b j
    rw [show (1 : ℕ) = 0 + 1 from rfl, cg_Nhom B A₀ A₁ A₂ 0 b j]
    refine ENNReal.mul_ne_top ?_ (ENNReal.inv_ne_top.mpr (by simp [hq (1, j)]))
    have hB : ∀ z : ℕ × ι, 0 < z.1 → z ≠ k := fun z hz h => by rw [h] at hz; simp [hk] at hz
    have hγx : ns_gam (jumpP (qbdQ B A₀ A₁ A₂)) k (1, b) ≠ 0 := by
      intro h; apply hνpos (1, b); rw [hu (1, b), h, mul_zero]
    obtain ⟨L, hL⟩ : ∃ L, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) k (L + 1) (1, b) (fun z => z ≠ k) ≠ 0 := by
      by_contra hc; push Not at hc; apply hγx; unfold ns_gam; simp [hc]
    have hγy : ns_gam (jumpP (qbdQ B A₀ A₁ A₂)) k (1, j) ≠ ⊤ := by
      intro h; apply hfin (1, j); rw [hu (1, j), h, ENNReal.mul_top hk0]
    have hle : g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) k (L + 1) (1, b) (fun z => z ≠ k) *
        ∑' t, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (1, b) t (1, j) (fun z => 0 < z.1) ≤
        ns_gam (jumpP (qbdQ B A₀ A₁ A₂)) k (1, j) := by
      rw [← ENNReal.tsum_mul_left]
      calc _ ≤ ∑' t, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) k ((L + t) + 1) (1, j) (fun z => z ≠ k) := by
            refine ENNReal.tsum_le_tsum fun t => ?_
            have h3 := ns_rem (jumpP (qbdQ B A₀ A₁ A₂)) k (fun z => 0 < z.1) hB L t (1, j)
            have h4 := (ENNReal.le_tsum ((1, b) : ℕ × ι)).trans h3
            beta_reduce at h4
            rw [if_pos (show 0 < ((1, b) : ℕ × ι).1 from Nat.one_pos)] at h4
            rwa [show L + 1 + t = L + t + 1 by omega] at h4
        _ ≤ ns_gam (jumpP (qbdQ B A₀ A₁ A₂)) k (1, j) :=
            ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective L)
              (fun L' => g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) k (L' + 1) (1, j) (fun z => z ≠ k))
    intro htop
    rw [htop, ENNReal.mul_top hL] at hle
    exact hγy (top_le_iff.mp hle)
  have hRfin : ∀ a j, rateR (qbdQ B A₀ A₁ A₂) 0 a j ≠ ⊤ := by
    intro a j htop
    have h1 := hstep 0 j
    have h2 : ENNReal.ofReal (π (0, a)) * rateR (qbdQ B A₀ A₁ A₂) 0 a j ≤
        ENNReal.ofReal (π (0 + 1, j)) := by
      rw [h1]
      exact ENNReal.le_tsum (f := fun a' => ENNReal.ofReal (π (0, a')) *
        rateR (qbdQ B A₀ A₁ A₂) 0 a' j) a
    rw [htop, ENNReal.mul_top (hπpos _)] at h2
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h2)
  have hrate : ∀ n, rateR (qbdQ B A₀ A₁ A₂) n =
      matMulE (ennMat A₀) (matNct (qbdQ B A₀ A₁ A₂) 1) := by
    intro n; funext a j; rw [cg_rate B A₀ A₁ A₂ hQ]; rfl
  obtain ⟨N, hN0, hN⟩ : ∃ N : ι → ι → ℝ, (∀ i j, 0 ≤ N i j) ∧
      ennMat N = matNct (qbdQ B A₀ A₁ A₂) 1 :=
    ⟨fun b j => (matNct (qbdQ B A₀ A₁ A₂) 1 b j).toReal, fun _ _ => ENNReal.toReal_nonneg,
      by funext b j; exact ENNReal.ofReal_toReal (hNfin b j)⟩
  obtain ⟨R, hR0, hR⟩ : ∃ R : ι → ι → ℝ, (∀ i j, 0 ≤ R i j) ∧
      ennMat R = rateR (qbdQ B A₀ A₁ A₂) 0 :=
    ⟨fun a j => (rateR (qbdQ B A₀ A₁ A₂) 0 a j).toReal, fun _ _ => ENNReal.toReal_nonneg,
      by funext a j; exact ENNReal.ofReal_toReal (hRfin a j)⟩
  have hpow : ∀ n, (fun j => ENNReal.ofReal (π (n, j))) =
      vecMulE (fun i => ENNReal.ofReal (π (0, i))) (matPowE (ennMat R) n) := by
    intro n
    induction n with
    | zero => rw [matPowE, cg_one]
    | succ n ih =>
      rw [matPowE, ← cg_assoc, ← ih, hR, hrate 0, ← hrate n]
      funext j
      rw [hstep n j]
      rfl
  refine ⟨R, N, hR0, hN0, ?_, ?_, ?_, ?_⟩
  · intro n; rw [hR, hrate, hrate]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hN]
    funext b j
    rw [cg_Nhom B A₀ A₁ A₂ m b j]
    exact (cg_Nhom B A₀ A₁ A₂ 0 b j).symm
  · rw [hN, hR, hrate]
  · intro n j
    exact congrFun (hpow n) j

end Final

end S202CG

open MatrixAnalytic.ProductForm in
open scoped ENNReal in
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ) (π : ℕ × ι → ℝ)
    (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂))
    (hirr : IrreducibleCT (qbdQ B A₀ A₁ A₂))
    (hreg : RegularCT (qbdQ B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrentCT (qbdQ B A₀ A₁ A₂) x)
    (hπ : IsStationaryCT (qbdQ B A₀ A₁ A₂) π) :
    ∃ R N : ι → ι → ℝ, (∀ i j, 0 ≤ R i j) ∧ (∀ i j, 0 ≤ N i j) ∧
      (∀ n : ℕ, rateR (qbdQ B A₀ A₁ A₂) n = ennMat R) ∧
      (∀ n : ℕ, 1 ≤ n → matNct (qbdQ B A₀ A₁ A₂) n = ennMat N) ∧
      matMulE (ennMat A₀) (ennMat N) = ennMat R ∧
      (∀ n : ℕ, ∀ j : ι, ENNReal.ofReal (π (n, j)) =
        vecMulE (fun i => ENNReal.ofReal (π (0, i))) (matPowE (ennMat R) n) j) :=
  S202CG.cg_main B A₀ A₁ A₂ π hQ hirr hpos hπ
