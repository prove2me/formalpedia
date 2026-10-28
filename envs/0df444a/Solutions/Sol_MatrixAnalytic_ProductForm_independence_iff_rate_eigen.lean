-- Prove2me | solution 1 for MatrixAnalytic.ProductForm.independence_iff_rate_eigen
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:20:17.963976+00:00
-- url     : https://prove2.me/submissions/90fa59df-5b33-46bd-b88e-3dd631578360

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

namespace S202IR
open S202CG

section G
variable {V : Type*} (P : V → V → ℝ)

lemma ps_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) :
    ∀ s, ∑' y, g72mab_PS P x s y (fun _ => True) = 1 := by
  classical
  intro s
  induction s with
  | zero =>
    rw [tsum_eq_single x]
    · simp [g72mab_PS_zero]
    · intro b hb; simp [g72mab_PS_zero, Ne.symm hb]
  | succ s ih =>
    simp_rw [g72mab_PS_snoc P x s _ (fun _ => True)]
    rw [ENNReal.tsum_comm]
    simp only [or_true, if_true, ENNReal.tsum_mul_left, hrow, mul_one]
    exact ih

lemma ps_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (s : ℕ) (y : V) :
    g72mab_PS P x s y (fun _ => True) ≤ 1 := by
  rw [← ps_mass P hrow x s]; exact ENNReal.le_tsum y

open Classical in
/-- last-exit decomposition at the last visit to `C` before the final step -/
lemma ps_last (A C : V → Prop) (hCA : ∀ z, C z → A z) (x : V) :
    ∀ s y, g72mab_PS P x (s + 1) y A =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, ∑' c, (if C c then g72mab_PS P x p.1 c A *
          g72mab_PS P c (p.2 + 1) y (fun z => A z ∧ ¬ C z) else 0)
      + (if C x then 0 else g72mab_PS P x (s + 1) y (fun z => A z ∧ ¬ C z)) := by
  classical
  intro s
  induction s with
  | zero =>
    intro y
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, zero_add, g72mab_PS_zero,
      g72mab_PS_one]
    rw [tsum_eq_single x]
    · by_cases hx : C x <;> simp [hx]
    · intro b hb; simp [Ne.symm hb]
  | succ s ih =>
    intro y
    set B : V → Prop := fun z => A z ∧ ¬ C z with hB
    set D : V → ℝ≥0∞ := fun w => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, ∑' c, (if C c then
      g72mab_PS P x p.1 c A * g72mab_PS P c (p.2 + 1) w B else 0) with hD
    set E : V → ℝ≥0∞ := fun w => if C x then 0 else g72mab_PS P x (s + 1) w B with hE
    have h1 : g72mab_PS P x (s + 1 + 1) y A =
        ∑' w, (if C w then g72mab_PS P x (s + 1) w A * ENNReal.ofReal (P w y) else 0) +
        ∑' w, (if B w then D w * ENNReal.ofReal (P w y) else 0) +
        ∑' w, (if B w then E w * ENNReal.ofReal (P w y) else 0) := by
      rw [g72mab_PS_snoc, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
      refine tsum_congr fun w => ?_
      by_cases hC : C w
      · have hBw : ¬ B w := fun h => h.2 hC
        simp [hC, hBw, hCA w hC]
      · by_cases hA : A w
        · have hBw : B w := ⟨hA, hC⟩
          simp only [hC, hBw, hA, or_true, if_true, if_false, zero_add]
          rw [ih w, add_mul]
        · have hBw : ¬ B w := fun h => hA h.1
          simp [hC, hBw, hA]
    rw [h1, Finset.Nat.sum_antidiagonal_succ']
    congr 1
    · congr 1
      · refine tsum_congr fun c => ?_
        split_ifs <;> simp [g72mab_PS_one]
      · simp only [hD]
        simp_rw [Finset.sum_mul, ENNReal.tsum_mul_right.symm]
        have e : ∀ w, (if B w then ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, ∑' c, (if C c then
            g72mab_PS P x p.1 c A * g72mab_PS P c (p.2 + 1) w B else 0) * ENNReal.ofReal (P w y)
            else 0) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, ∑' c, (if C c then
            g72mab_PS P x p.1 c A *
            ((if B w then g72mab_PS P c (p.2 + 1) w B else 0) * ENNReal.ofReal (P w y)) else 0) := by
          intro w
          by_cases hBw : B w
          · simp only [hBw, if_true]
            refine Finset.sum_congr rfl fun p _ => tsum_congr fun c => ?_
            split_ifs <;> simp [mul_assoc]
          · simp [hBw]
        simp_rw [e]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun c => ?_
        split_ifs with hc
        · rw [ENNReal.tsum_mul_left, g72mab_PS_snoc P c (p.2 + 1) y B]
          congr 1
          refine tsum_congr fun w => ?_
          simp
        · simp
    · simp only [hE]
      by_cases hx : C x
      · simp [hx]
      · simp only [hx, if_false]
        rw [g72mab_PS_snoc P x (s + 1) y B]
        refine tsum_congr fun w => ?_
        simp

end G

end S202IR

namespace S202IR
open S202CG

lemma ecauchy (a b : ℕ → ℝ≥0∞) :
    (∑' r, a r) * (∑' u, b u) =
      ∑' s, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, a p.1 * b p.2 := by
  have h1 : (∑' r, a r) * (∑' u, b u) = ∑' p : ℕ × ℕ, a p.1 * b p.2 := by
    rw [show (∑' p : ℕ × ℕ, a p.1 * b p.2) = ∑' r, ∑' u, a r * b u from
      ENNReal.tsum_prod (f := fun r u => a r * b u),
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun r => ?_
    rw [ENNReal.tsum_mul_left]
  rw [h1, ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq,
    ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  exact Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal n) (fun p => a p.1 * b p.2)

lemma trunc_cauchy (a b : ℕ → ℝ≥0∞) (t : ℕ) :
    ∑ s ∈ Finset.range t, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, a p.1 * b p.2 ≤
      (∑ r ∈ Finset.range t, a r) * (∑ u ∈ Finset.range t, b u) := by
  set a' : ℕ → ℝ≥0∞ := fun r => if r < t then a r else 0 with ha'
  set b' : ℕ → ℝ≥0∞ := fun r => if r < t then b r else 0 with hb'
  have hA : ∑' r, a' r = ∑ r ∈ Finset.range t, a r := by
    rw [tsum_eq_sum (s := Finset.range t)]
    · exact Finset.sum_congr rfl fun r hr => by simp [ha', Finset.mem_range.mp hr]
    · intro r hr; simp [ha', Finset.mem_range.not.mp hr]
  have hB : ∑' r, b' r = ∑ r ∈ Finset.range t, b r := by
    rw [tsum_eq_sum (s := Finset.range t)]
    · exact Finset.sum_congr rfl fun r hr => by simp [hb', Finset.mem_range.mp hr]
    · intro r hr; simp [hb', Finset.mem_range.not.mp hr]
  rw [← hA, ← hB, ecauchy]
  calc _ = ∑ s ∈ Finset.range t, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, a' p.1 * b' p.2 := by
        refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun p hp => ?_
        have h1 := Finset.mem_range.mp hs
        have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        have h3 : p.1 < t := by omega
        have h4 : p.2 < t := by omega
        simp [ha', hb', h3, h4]
    _ ≤ _ := ENNReal.sum_le_tsum _

section G2
variable {V : Type*} (P : V → V → ℝ)

lemma ps_ret (x : V) (s : ℕ) (y : V) :
    g72mab_PS P x (s + 1) y (fun _ => True) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s,
        g72mab_PS P x p.1 x (fun _ => True) * g72mab_PS P x (p.2 + 1) y (fun z => z ≠ x) := by
  classical
  rw [ps_last P (fun _ => True) (fun z => z = x) (fun _ _ => trivial) x s y]
  have e : (fun z : V => True ∧ ¬ z = x) = fun z => z ≠ x := by funext z; simp
  rw [e, if_pos rfl, add_zero]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [tsum_eq_single x]
  · simp
  · intro c hc; simp [hc]

lemma ps_green (x : V) (s : ℕ) (y : V) :
    g72mab_PS P x s y (fun _ => True) ≤
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s,
        g72mab_PS P x p.1 x (fun _ => True) * g72mab_PS P x p.2 y (fun z => z ≠ x) := by
  classical
  cases s with
  | zero => simp [g72mab_PS_zero]
  | succ s =>
    rw [ps_ret, Finset.Nat.sum_antidiagonal_succ']
    exact le_add_self

lemma g_bound (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (a : ℝ≥0∞)
    (ha : ∀ t, a ≤ g72mab_AV P x (fun z => z ≠ x) t) (t : ℕ) :
    (∑ s ∈ Finset.range t, g72mab_PS P x s x (fun _ => True)) * a ≤ 1 := by
  classical
  have hEX : ∀ s, g72mab_EX P x (fun z => z ≠ x) (s + 1) =
      g72mab_PS P x (s + 1) x (fun z => z ≠ x) := by
    intro s
    rw [g72mab_EX_eq, tsum_eq_single x]
    · simp
    · intro b hb; simp [hb]
  have hmass : ∀ t, g72mab_AV P x (fun z => z ≠ x) t +
      ∑ s ∈ Finset.range t, g72mab_PS P x (s + 1) x (fun z => z ≠ x) = 1 := by
    intro t; have := g72mab_mass P hrow x (fun z => z ≠ x) t; simp_rw [hEX] at this; exact this
  set G : ℕ → ℝ≥0∞ := fun t => ∑ s ∈ Finset.range t, g72mab_PS P x s x (fun _ => True) with hG
  set F : ℕ → ℝ≥0∞ := fun t => ∑ s ∈ Finset.range t, g72mab_PS P x (s + 1) x (fun z => z ≠ x)
    with hF
  have hGfin : ∀ t, G t ≠ ⊤ := by
    intro t
    refine ne_top_of_le_ne_top (b := ∑ s ∈ Finset.range t, (1 : ℝ≥0∞)) (by simp) ?_
    exact Finset.sum_le_sum fun s _ => ps_le_one P hrow x s x
  have hGmono : ∀ t, G t ≤ G (t + 1) := fun t => by
    simp only [hG]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ t))
  have hFle : ∀ t, F t ≤ 1 := fun t => by rw [← hmass t]; exact le_add_self
  have hrec : G (t + 1) ≤ 1 + G (t + 1) * F t := by
    show ∑ s ∈ Finset.range (t + 1), g72mab_PS P x s x (fun _ => True) ≤ 1 + G (t + 1) * F t
    rw [Finset.sum_range_succ', g72mab_PS_zero, if_pos rfl, add_comm]
    gcongr 1 + ?_
    simp_rw [ps_ret P x]
    refine (trunc_cauchy (fun r => g72mab_PS P x r x (fun _ => True))
      (fun u => g72mab_PS P x (u + 1) x (fun z => z ≠ x)) t).trans ?_
    gcongr
    exact hGmono t
  have hGF : G (t + 1) * F t ≠ ⊤ :=
    ENNReal.mul_ne_top (hGfin _) (ne_top_of_le_ne_top ENNReal.one_ne_top (hFle t))
  have h2 : G (t + 1) * g72mab_AV P x (fun z => z ≠ x) t + G (t + 1) * F t ≤
      1 + G (t + 1) * F t := by
    rw [← mul_add, hmass t, mul_one]; exact hrec
  have h3 := ENNReal.le_of_add_le_add_right hGF h2
  calc G t * a ≤ G (t + 1) * g72mab_AV P x (fun z => z ≠ x) t := by
        gcongr
        · exact hGmono t
        · exact ha t
    _ ≤ 1 := h3

lemma green_bound (x : V) (t : ℕ) (y : V) :
    ∑ s ∈ Finset.range t, g72mab_PS P x s y (fun _ => True) ≤
      (∑ s ∈ Finset.range t, g72mab_PS P x s x (fun _ => True)) *
        ∑' u, g72mab_PS P x u y (fun z => z ≠ x) := by
  calc _ ≤ ∑ s ∈ Finset.range t, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s,
        g72mab_PS P x p.1 x (fun _ => True) * g72mab_PS P x p.2 y (fun z => z ≠ x) :=
        Finset.sum_le_sum fun s _ => ps_green P x s y
    _ ≤ _ := trunc_cauchy (fun r => g72mab_PS P x r x (fun _ => True))
        (fun u => g72mab_PS P x u y (fun z => z ≠ x)) t
    _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum _

open Classical in
lemma group_last (x : V) (t : ℕ) (h : V → ℝ≥0∞) :
    ∑' ω : Fin (t + 1) → V, (if ω 0 = x then g72mab_W P ω * h (ω (Fin.last t)) else 0) =
      ∑' y, g72mab_PS P x t y (fun _ => True) * h y := by
  classical
  unfold g72mab_PS
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last t))]
  · by_cases h0 : ω 0 = x <;> simp [h0]
  · intro y hy; simp [Ne.symm hy]

open Classical in
lemma marg (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (h : V → ℝ≥0∞) :
    ∀ t k (hk : k ≤ t), ∑' ω : Fin (t + 1) → V,
      (if ω 0 = x then g72mab_W P ω * h (ω ⟨k, Nat.lt_succ_of_le hk⟩) else 0) =
      ∑' y, g72mab_PS P x k y (fun _ => True) * h y := by
  classical
  intro t
  induction t with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    exact group_last P x 0 h
  | succ t ih =>
    intro k hk
    by_cases hkt : k = t + 1
    · subst hkt
      exact group_last P x (t + 1) h
    · have hk' : k ≤ t := by omega
      rw [← ih k hk', g72mab_tsum_snoc]
      refine tsum_congr fun ω => ?_
      have hz : ∀ z, (Fin.snoc ω z : Fin (t + 2) → V) 0 = ω 0 := by
        intro z
        have : (0 : Fin (t + 2)) = (0 : Fin (t + 1)).castSucc := rfl
        rw [this, Fin.snoc_castSucc]
      have hkk : ∀ z, (Fin.snoc ω z : Fin (t + 2) → V) ⟨k, Nat.lt_succ_of_le hk⟩ =
          ω ⟨k, Nat.lt_succ_of_le hk'⟩ := by
        intro z
        have : (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (t + 2)) =
          (⟨k, Nat.lt_succ_of_le hk'⟩ : Fin (t + 1)).castSucc := rfl
        rw [this, Fin.snoc_castSucc]
      simp_rw [hz, hkk, g72mab_W_snoc]
      by_cases h0 : ω 0 = x
      · simp only [h0, if_true]
        simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left]
        congr 1
        simp_rw [mul_comm _ (h _)]
        rw [ENNReal.tsum_mul_left, hrow, mul_one]
      · simp [h0]

end G2

end S202IR

namespace S202IR
open S202CG

section CT
variable {V : Type*} [Countable V] [DecidableEq V]

lemma pi_tsum (π : V → ℝ) (hπ0 : ∀ x, 0 ≤ π x) (hπ1 : HasSum π 1) :
    ∑' x, ENNReal.ofReal (π x) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hπ0 hπ1.summable, hπ1.tsum_eq, ENNReal.ofReal_one]

lemma hr_mul (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (y : V) :
    (ENNReal.ofReal (holdRate Q y))⁻¹ * ENNReal.ofReal (holdRate Q y) = 1 :=
  ENNReal.inv_mul_cancel (by simp [cg_qpos Q hQ y]) ENNReal.ofReal_ne_top

lemma nu_pos (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (hirr : IrreducibleCT Q) (π : V → ℝ)
    (hπ : IsStationaryCT Q π) (x : V) :
    ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate Q x) ≠ 0 := by
  classical
  have hq := cg_qpos Q hQ
  set ν : V → ℝ≥0∞ := fun x => ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate Q x) with hν
  have hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (jumpP Q x y) = ν y := cg_inv Q hQ π hπ
  obtain ⟨k, hk⟩ : ∃ k, π k ≠ 0 := by
    by_contra h
    push Not at h
    have hz : π = fun _ => 0 := funext h
    have h1 := hπ.2.1
    rw [hz] at h1
    exact one_ne_zero (h1.unique hasSum_zero)
  have hk0 : ν k ≠ 0 := by
    simp only [hν, ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero, not_or, not_le]
    exact ⟨lt_of_le_of_ne (hπ.1 k) (Ne.symm hk), hq k⟩
  obtain ⟨L, hL⟩ := cg_irr Q hQ hirr k x
  have h1 := ns_sub_iter (jumpP Q) ν hinv L k x
  intro h0
  change ν x = 0 at h0
  rw [h0] at h1
  exact (mul_ne_zero hk0 hL) (le_antisymm h1 bot_le)

open Classical in
lemma exp_le (Q : V → V → ℝ) (x : V) :
    expReturnTimeCT Q x ≤ ∑' y, (ENNReal.ofReal (holdRate Q y))⁻¹ *
      ∑' t, g72mab_PS (jumpP Q) x t y (fun z => z ≠ x) := by
  unfold expReturnTimeCT
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun t => ?_
  unfold g72mab_PS
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h
  · refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (ω (Fin.last t)))
    rw [if_pos ⟨h.1, rfl, fun m hm _ => h.2 m hm⟩, mul_comm]
    rfl
  · exact bot_le

lemma soj_K (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (π : V → ℝ) (hπ : IsStationaryCT Q π)
    (x : V) :
    ∑' y, (ENNReal.ofReal (holdRate Q y))⁻¹ * ∑' t, g72mab_PS (jumpP Q) x t y (fun z => z ≠ x) ≤
      (ENNReal.ofReal (holdRate Q x))⁻¹ +
        (ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate Q x))⁻¹ := by
  classical
  set ν : V → ℝ≥0∞ := fun x => ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate Q x) with hν
  have hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (jumpP Q x y) = ν y := cg_inv Q hQ π hπ
  by_cases hνx : ν x = 0
  · change _ ≤ _ + (ν x)⁻¹
    rw [hνx, ENNReal.inv_zero, add_top]; exact le_top
  have hνt : ν x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have e1 : ∀ y, ∑' t, g72mab_PS (jumpP Q) x t y (fun z => z ≠ x) =
      g72mab_PS (jumpP Q) x 0 y (fun z => z ≠ x) + ns_gam (jumpP Q) x y := by
    intro y; rw [tsum_eq_zero_add' ENNReal.summable]; rfl
  simp_rw [e1, mul_add]
  rw [ENNReal.tsum_add]
  gcongr
  · rw [tsum_eq_single x]
    · simp [g72mab_PS_zero]
    · intro b hb; simp [g72mab_PS_zero, Ne.symm hb]
  · calc _ ≤ ∑' y, ENNReal.ofReal (π y) * (ν x)⁻¹ := by
          refine ENNReal.tsum_le_tsum fun y => ?_
          have h1 : ns_gam (jumpP Q) x y ≤ ν y / ν x :=
            (ENNReal.le_div_iff_mul_le (Or.inl hνx) (Or.inl hνt)).mpr
              (by rw [mul_comm]; exact ns_gam_le (jumpP Q) ν hinv x y)
          calc _ ≤ (ENNReal.ofReal (holdRate Q y))⁻¹ * (ν y / ν x) := by gcongr
            _ = _ := by
              rw [div_eq_mul_inv, ← mul_assoc]
              congr 1
              simp only [hν]
              rw [mul_comm (ENNReal.ofReal (π y)), ← mul_assoc, hr_mul Q hQ, one_mul]
      _ = _ := by rw [ENNReal.tsum_mul_right, pi_tsum π hπ.1 hπ.2.1, one_mul]

lemma reg_contra (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (hreg : RegularCT Q) (x : V)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hb : ∀ t, ∑ s ∈ Finset.range t, ∑' y, g72mab_PS (jumpP Q) x s y (fun _ => True) *
      (ENNReal.ofReal (holdRate Q y))⁻¹ ≤ C) : False := by
  classical
  have hq := cg_qpos Q hQ
  have hrow := cg_jrow Q hQ
  set c := C.toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  set M : ℝ := 2 * c + 2 with hM
  have hM0 : 0 < M := by rw [hM]; linarith
  have h := hreg x M
  set A : ℕ → ℝ≥0∞ := fun t => ∑' ω : Fin (t + 1) → V,
      if ω 0 = x ∧ ∑ k : Fin t, (holdRate Q (ω k.castSucc))⁻¹ ≤ M
      then pathWeightE (jumpP Q) ω else 0 with hA
  have key : ∀ t, (1 / 2 : ℝ) ≤ (A t).toReal := by
    intro t
    set Bv : ℝ≥0∞ := ∑' ω : Fin (t + 1) → V,
      if ω 0 = x ∧ ¬ ∑ k : Fin t, (holdRate Q (ω k.castSucc))⁻¹ ≤ M
      then g72mab_W (jumpP Q) ω else 0 with hBv
    have hmass : A t + Bv = 1 := by
      have h1 := marg (jumpP Q) hrow x (fun _ => 1) t 0 (Nat.zero_le t)
      simp only [mul_one] at h1
      rw [ps_mass (jumpP Q) hrow x 0] at h1
      rw [← h1, hA, hBv, ← ENNReal.tsum_add]
      refine tsum_congr fun ω => ?_
      by_cases h0 : ω 0 = x
      · by_cases hS : ∑ k : Fin t, (holdRate Q (ω k.castSucc))⁻¹ ≤ M
        · simp only [h0, hS, true_and, not_true_eq_false, if_true, if_false, add_zero]
          rfl
        · simp only [h0, hS, true_and, not_false_eq_true, if_true, if_false, zero_add]
      · simp [h0]
    have hE : ∑' ω : Fin (t + 1) → V, (if ω 0 = x then g72mab_W (jumpP Q) ω *
        ∑ k : Fin t, (ENNReal.ofReal (holdRate Q (ω k.castSucc)))⁻¹ else 0) ≤ C := by
      have e : ∀ ω : Fin (t + 1) → V, (if ω 0 = x then g72mab_W (jumpP Q) ω *
          ∑ k : Fin t, (ENNReal.ofReal (holdRate Q (ω k.castSucc)))⁻¹ else 0) =
          ∑ k : Fin t, (if ω 0 = x then g72mab_W (jumpP Q) ω *
            (ENNReal.ofReal (holdRate Q (ω k.castSucc)))⁻¹ else 0) := by
        intro ω; split_ifs <;> simp [Finset.mul_sum]
      simp_rw [e]
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      have e2 : ∀ k : Fin t, ∑' ω : Fin (t + 1) → V, (if ω 0 = x then g72mab_W (jumpP Q) ω *
            (ENNReal.ofReal (holdRate Q (ω k.castSucc)))⁻¹ else 0) =
          ∑' y, g72mab_PS (jumpP Q) x k y (fun _ => True) *
            (ENNReal.ofReal (holdRate Q y))⁻¹ := fun k => by
        convert marg (jumpP Q) hrow x (fun y => (ENNReal.ofReal (holdRate Q y))⁻¹) t k k.isLt.le
          using 3
        split_ifs <;> rfl
      simp_rw [e2]
      rw [Fin.sum_univ_eq_sum_range (fun s => ∑' y, g72mab_PS (jumpP Q) x s y (fun _ => True) *
        (ENNReal.ofReal (holdRate Q y))⁻¹) t]
      exact hb t
    have hBM : ENNReal.ofReal M * Bv ≤ C := by
      refine le_trans ?_ hE
      rw [hBv, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun ω => ?_
      split_ifs with h1 h2
      · have hS : ∑ k : Fin t, (ENNReal.ofReal (holdRate Q (ω k.castSucc)))⁻¹ =
            ENNReal.ofReal (∑ k : Fin t, (holdRate Q (ω k.castSucc))⁻¹) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => (inv_pos.mpr (hq _)).le)]
          exact Finset.sum_congr rfl fun k _ => (ENNReal.ofReal_inv_of_pos (hq _)).symm
        rw [hS, mul_comm]
        gcongr
        exact le_of_lt (not_le.mp h1.2)
      · exact absurd h1.1 h2
      · simp
      · simp
    have hBv1 : Bv ≤ 1 := by rw [← hmass]; exact le_add_self
    have hBt : Bv ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hBv1
    have hAt : A t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hmass]; exact le_self_add)
    have h1 : M * Bv.toReal ≤ c := by
      have := ENNReal.toReal_mono hC hBM
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0.le] at this
    have h2 : (A t).toReal + Bv.toReal = 1 := by
      rw [← ENNReal.toReal_add hAt hBt, hmass, ENNReal.toReal_one]
    have h3 : Bv.toReal < 1 / 2 := by
      by_contra hcon
      push Not at hcon
      have : M * (1 / 2) ≤ M * Bv.toReal := mul_le_mul_of_nonneg_left hcon hM0.le
      rw [hM] at this
      linarith
    linarith
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h2
  have h3 := h2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨t, ht⟩ := h3.exists
  have := key t
  simp only [Function.comp_apply] at ht
  change (A t).toReal < 1 / 2 at ht
  linarith

end CT

end S202IR

namespace S202IR
open S202CG

section CT2
variable {V : Type*} [Countable V] [DecidableEq V]

lemma rec_main (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (hirr : IrreducibleCT Q)
    (hreg : RegularCT Q) (π : V → ℝ) (hπ : IsStationaryCT Q π) (x : V) :
    Filter.Tendsto (fun t => g72mab_AV (jumpP Q) x (fun z => z ≠ x) t) Filter.atTop (nhds 0) := by
  classical
  have hrow := cg_jrow Q hQ
  have hanti : Antitone (fun t => g72mab_AV (jumpP Q) x (fun z => z ≠ x) t) := by
    refine antitone_nat_of_succ_le fun t => ?_
    rw [← g72mab_step (jumpP Q) hrow x (fun z => z ≠ x) t]
    exact le_self_add
  have hlim := tendsto_atTop_iInf hanti
  set a := ⨅ t, g72mab_AV (jumpP Q) x (fun z => z ≠ x) t with ha
  by_cases ha0 : a = 0
  · rwa [ha0] at hlim
  exfalso
  have hax : ∀ t, a ≤ g72mab_AV (jumpP Q) x (fun z => z ≠ x) t := fun t => iInf_le _ t
  set K := (ENNReal.ofReal (holdRate Q x))⁻¹ +
    (ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate Q x))⁻¹ with hK
  have hKt : K ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.inv_ne_top.mpr (by simp [cg_qpos Q hQ x])
    · exact ENNReal.inv_ne_top.mpr (nu_pos Q hQ hirr π hπ x)
  refine reg_contra Q hQ hreg x (a⁻¹ * K) (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ha0) hKt)
    fun t => ?_
  set G := ∑ s ∈ Finset.range t, g72mab_PS (jumpP Q) x s x (fun _ => True) with hG
  have hGa : G ≤ a⁻¹ := ENNReal.le_inv_iff_mul_le.mpr (g_bound (jumpP Q) hrow x a hax t)
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  calc _ ≤ ∑' y, G * ((ENNReal.ofReal (holdRate Q y))⁻¹ *
        ∑' u, g72mab_PS (jumpP Q) x u y (fun z => z ≠ x)) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        rw [← Finset.sum_mul]
        calc _ ≤ G * (∑' u, g72mab_PS (jumpP Q) x u y (fun z => z ≠ x)) *
              (ENNReal.ofReal (holdRate Q y))⁻¹ := by
              gcongr; exact green_bound (jumpP Q) x t y
          _ = _ := by ring
    _ = G * ∑' y, ((ENNReal.ofReal (holdRate Q y))⁻¹ *
        ∑' u, g72mab_PS (jumpP Q) x u y (fun z => z ≠ x)) := ENNReal.tsum_mul_left
    _ ≤ a⁻¹ * K := by
        gcongr
        exact soj_K Q hQ π hπ x

lemma pr_of_stat (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (hirr : IrreducibleCT Q)
    (hreg : RegularCT Q) (π : V → ℝ) (hπ : IsStationaryCT Q π) (x : V) :
    PositiveRecurrentCT Q x := by
  classical
  refine ⟨?_, ?_⟩
  · have h := rec_main Q hQ hirr hreg π hπ x
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp_apply]
    rw [cg_rt Q hQ x t, ENNReal.toReal_ofReal]
    unfold returnTailC setAvoidTailC
    refine tsum_nonneg fun ω => ?_
    split_ifs
    · exact Finset.prod_nonneg fun i _ => cg_jnn Q hQ _ _
    · exact le_rfl
  · refine ne_top_of_le_ne_top ?_ ((exp_le Q x).trans (soj_K Q hQ π hπ x))
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.inv_ne_top.mpr (by simp [cg_qpos Q hQ x])
    · exact ENNReal.inv_ne_top.mpr (nu_pos Q hQ hirr π hπ x)

lemma stat_uniq (Q : V → V → ℝ) (hQ : IsGeneratorC Q) (hirr : IrreducibleCT Q) (k : V)
    (hpos : PositiveRecurrentCT Q k) (π₁ π₂ : V → ℝ)
    (h₁ : IsStationaryCT Q π₁) (h₂ : IsStationaryCT Q π₂) (y : V) : π₁ y = π₂ y := by
  classical
  have hq := cg_qpos Q hQ
  have hrow := cg_jrow Q hQ
  have hrec : Filter.Tendsto (fun t => g72mab_AV (jumpP Q) k (fun z => z ≠ k) t)
      Filter.atTop (nhds 0) := by
    have h := hpos.1
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr fun t => ?_
    exact (cg_rt Q hQ k t).symm
  have hkk := ns_gam_kk (jumpP Q) hrow k hrec
  have hirr' : ∀ x, ∃ L, g72mab_PS (jumpP Q) x L k (fun _ => True) ≠ 0 :=
    fun x => cg_irr Q hQ hirr x k
  set g : V → ℝ≥0∞ := fun y => ns_gam (jumpP Q) k y * (ENNReal.ofReal (holdRate Q y))⁻¹ with hg
  have hform : ∀ π : V → ℝ, IsStationaryCT Q π → ∀ y, ENNReal.ofReal (π y) =
      (ENNReal.ofReal (π k) * ENNReal.ofReal (holdRate Q k)) * g y := by
    intro π hπ y
    have hu := ns_uniq (jumpP Q) (fun x => ENNReal.ofReal (π x) * ENNReal.ofReal (holdRate Q x))
      (cg_inv Q hQ π hπ) (fun y => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      k hkk hirr' y
    beta_reduce at hu
    rw [hg, ← mul_assoc, ← hu, mul_assoc, mul_comm (ENNReal.ofReal (holdRate Q y)),
      hr_mul Q hQ, mul_one]
  have hsum : ∀ π : V → ℝ, IsStationaryCT Q π →
      (ENNReal.ofReal (π k) * ENNReal.ofReal (holdRate Q k)) * ∑' y, g y = 1 := by
    intro π hπ
    rw [← ENNReal.tsum_mul_left, ← pi_tsum π hπ.1 hπ.2.1]
    exact tsum_congr fun y => (hform π hπ y).symm
  set S := ∑' y, g y
  have hS0 : S ≠ 0 := by
    intro h0; have := hsum π₁ h₁; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hSt : S ≠ ⊤ := by
    intro ht; have := hsum π₁ h₁; rw [ht] at this
    by_cases hc : ENNReal.ofReal (π₁ k) * ENNReal.ofReal (holdRate Q k) = 0
    · rw [hc, zero_mul] at this; exact zero_ne_one this
    · rw [ENNReal.mul_top hc] at this; exact ENNReal.top_ne_one this
  have hc : ENNReal.ofReal (π₁ k) * ENNReal.ofReal (holdRate Q k) =
      ENNReal.ofReal (π₂ k) * ENNReal.ofReal (holdRate Q k) := by
    have e1 := hsum π₁ h₁
    have e2 := hsum π₂ h₂
    rw [← ENNReal.mul_div_cancel_right hS0 hSt (a := ENNReal.ofReal (π₁ k) * _), e1,
      ← ENNReal.mul_div_cancel_right hS0 hSt (a := ENNReal.ofReal (π₂ k) * _), e2]
  have := hform π₁ h₁ y
  rw [hc, ← hform π₂ h₂ y] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (h₁.1 y) (h₂.1 y)).mp this

end CT2

end S202IR

namespace S202IR
open S202CG

section G5
variable {V : Type*} (P : V → V → ℝ)

lemma bal (x : V) (A : V → Prop) [DecidablePred A] (y : V) :
    ∑' L, g72mab_PS P x (L + 1) y A = ENNReal.ofReal (P x y) +
      ∑' w, (if A w then (∑' L, g72mab_PS P x (L + 1) w A) * ENNReal.ofReal (P w y) else 0) := by
  rw [tsum_eq_zero_add' ENNReal.summable, zero_add, g72mab_PS_one]
  congr 1
  simp_rw [g72mab_PS_snoc P x (_ + 1) y A]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun w => ?_
  by_cases hw : A w
  · simp only [hw, or_true, if_true, ENNReal.tsum_mul_right]
  · simp [hw]

end G5

lemma ennsum3 {ι : Type*} (f0 f1 f2 : ι → ℝ) (h0 : ∀ i, 0 ≤ f0 i) (h1 : ∀ i, 0 ≤ f1 i)
    (h2 : ∀ i, 0 ≤ f2 i) (c : ℝ) (hc : 0 ≤ c)
    (h : ∑' i, ENNReal.ofReal (f0 i) + ∑' i, ENNReal.ofReal (f1 i) + ∑' i, ENNReal.ofReal (f2 i) =
      ENNReal.ofReal c) :
    HasSum f0 (∑' i, f0 i) ∧ HasSum f1 (∑' i, f1 i) ∧ HasSum f2 (∑' i, f2 i) ∧
      ∑' i, f0 i + ∑' i, f1 i + ∑' i, f2 i = c := by
  have ht : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← h] at ht
  have t0 : ∑' i, ENNReal.ofReal (f0 i) ≠ ⊤ := fun e => ht (by rw [e]; simp)
  have t1 : ∑' i, ENNReal.ofReal (f1 i) ≠ ⊤ := fun e => ht (by rw [e]; simp)
  have t2 : ∑' i, ENNReal.ofReal (f2 i) ≠ ⊤ := fun e => ht (by rw [e]; simp)
  have sm : ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → ∑' i, ENNReal.ofReal (f i) ≠ ⊤ → Summable f := by
    intro f hf ht
    have := ENNReal.summable_toReal ht
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  have s0 := sm f0 h0 t0
  have s1 := sm f1 h1 t1
  have s2 := sm f2 h2 t2
  refine ⟨s0.hasSum, s1.hasSum, s2.hasSum, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg h0 s0, ← ENNReal.ofReal_tsum_of_nonneg h1 s1,
    ← ENNReal.ofReal_tsum_of_nonneg h2 s2, ← ENNReal.ofReal_add (tsum_nonneg h0) (tsum_nonneg h1),
    ← ENNReal.ofReal_add (add_nonneg (tsum_nonneg h0) (tsum_nonneg h1)) (tsum_nonneg h2)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (add_nonneg (add_nonneg (tsum_nonneg h0) (tsum_nonneg h1))
    (tsum_nonneg h2)) hc).mp h

section Q
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma qz (m n : ℕ) (a b : ι) (h1 : n ≠ m) (h2 : n ≠ m + 1) (h3 : n + 1 ≠ m) :
    qbdQ B A₀ A₁ A₂ (m, a) (n, b) = 0 := by
  unfold qbdQ; dsimp only; split_ifs <;> first | rfl | omega

lemma q11 (n : ℕ) (a b : ι) : qbdQ B A₀ A₁ A₂ (n + 1, a) (n + 1, b) = A₁ a b := by
  simp [qbdQ]

lemma q21 (n : ℕ) (a b : ι) : qbdQ B A₀ A₁ A₂ (n + 2, a) (n + 1, b) = A₂ a b := by
  simp [qbdQ]

lemma q00 (a b : ι) : qbdQ B A₀ A₁ A₂ (0, a) (0, b) = B a b := by
  unfold qbdQ; dsimp only; split_ifs <;> first | rfl | omega

lemma q10 (a b : ι) : qbdQ B A₀ A₁ A₂ (1, a) (0, b) = A₂ a b := by
  simp [qbdQ]

lemma pq (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂)) (x y : ℕ × ι) (hxy : y ≠ x) :
    ENNReal.ofReal (jumpP (qbdQ B A₀ A₁ A₂) x y) =
      (ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) x))⁻¹ * ENNReal.ofReal (qbdQ B A₀ A₁ A₂ x y) := by
  have hq := cg_qpos _ hQ x
  unfold jumpP
  rw [if_neg hxy, ← ENNReal.ofReal_inv_of_pos hq, ← ENNReal.ofReal_mul (inv_nonneg.mpr hq.le),
    div_eq_inv_mul]

lemma lvl2 (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂)) (i k : ι) :
    ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (0, i)) *
      (∑' L, g72mab_PS (jumpP (qbdQ B A₀ A₁ A₂)) (0, i) (L + 1) (2, k) (fun z => 0 < z.1)) *
      (ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (2, k)))⁻¹ =
    ∑' l, rateR (qbdQ B A₀ A₁ A₂) 0 i l * rateR (qbdQ B A₀ A₁ A₂) 1 l k := by
  classical
  set Q := qbdQ B A₀ A₁ A₂ with hQd
  set P := jumpP Q with hPd
  have hrem : ∀ s, g72mab_PS P (0, i) (s + 1) (2, k) (fun z => 1 < z.1) = 0 := by
    intro s
    rw [g72mab_PS_cons]
    refine ENNReal.tsum_eq_zero.mpr fun z => ?_
    by_cases hP : P (0, i) z = 0
    · simp [hP]
    · have h1 := (cg_Q_ne B A₀ A₁ A₂ _ z (cg_PQ _ _ z hP)).1
      simp only at h1
      by_cases hs : s = 0
      · subst hs
        have hz : z ≠ (2, k) := fun h => by rw [h] at h1; simp at h1
        simp [g72mab_PS_zero, hz]
      · have : ¬ (s = 0 ∨ 1 < z.1) := by omega
        simp [this]
  have e : (fun z : ℕ × ι => 0 < z.1 ∧ ¬ z.1 = 1) = fun z => 1 < z.1 := by
    funext z; apply propext; omega
  have hdec : ∀ s, g72mab_PS P (0, i) (s + 1) (2, k) (fun z => 0 < z.1) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, ∑' c : ℕ × ι, (if c.1 = 1 then
        g72mab_PS P (0, i) p.1 c (fun z => 0 < z.1) *
        g72mab_PS P c (p.2 + 1) (2, k) (fun z => 1 < z.1) else 0) := by
    intro s
    rw [ps_last P (fun z => 0 < z.1) (fun z => z.1 = 1) (fun z hz => by rw [hz]; exact Nat.one_pos)
      (0, i) s (2, k), e, if_neg (by simp), hrem, add_zero]
    exact Finset.sum_congr rfl fun p _ => tsum_congr fun c => by split_ifs <;> rfl
  have hE : ∑' L, g72mab_PS P (0, i) (L + 1) (2, k) (fun z => 0 < z.1) =
      ∑' l, (∑' L, g72mab_PS P (0, i) (L + 1) (1, l) (fun z => 0 < z.1)) *
        (∑' L, g72mab_PS P (1, l) (L + 1) (2, k) (fun z => 1 < z.1)) := by
    simp_rw [hdec]
    calc _ = ∑' s, ∑' c : ℕ × ι, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, (if c.1 = 1 then
          g72mab_PS P (0, i) p.1 c (fun z => 0 < z.1) *
          g72mab_PS P c (p.2 + 1) (2, k) (fun z => 1 < z.1) else 0) :=
          tsum_congr fun s => (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
      _ = ∑' c : ℕ × ι, ∑' s, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal s, (if c.1 = 1 then
          g72mab_PS P (0, i) p.1 c (fun z => 0 < z.1) *
          g72mab_PS P c (p.2 + 1) (2, k) (fun z => 1 < z.1) else 0) := ENNReal.tsum_comm
      _ = ∑' c : ℕ × ι, (if c.1 = 1 then
          (∑' L, g72mab_PS P (0, i) (L + 1) c (fun z => 0 < z.1)) *
          (∑' L, g72mab_PS P c (L + 1) (2, k) (fun z => 1 < z.1)) else 0) := by
          refine tsum_congr fun c => ?_
          split_ifs with hc
          · have h0 : ∑' L, g72mab_PS P (0, i) L c (fun z => 0 < z.1) =
                ∑' L, g72mab_PS P (0, i) (L + 1) c (fun z => 0 < z.1) := by
              rw [tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero, if_neg, zero_add]
              intro h; rw [← h] at hc; simp at hc
            rw [← h0, ecauchy]
          · simp
      _ = _ := by
          have hinj : Function.Injective (fun l : ι => ((1, l) : ℕ × ι)) := fun a b h => by
            simpa using h
          rw [← hinj.tsum_eq]
          · refine tsum_congr fun l => ?_
            simp
          · intro c hc
            rw [Function.mem_support] at hc
            have h1 : c.1 = 1 := by by_contra h; exact hc (by simp [h])
            exact ⟨c.2, Prod.ext h1.symm rfl⟩
  rw [hE, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun l => ?_
  rw [cg_rateS B A₀ A₁ A₂ 0 i l, cg_rateS B A₀ A₁ A₂ 1 l k]
  simp only [zero_add, Nat.reduceAdd]
  have h1 := hr_mul Q hQ (1, l)
  calc _ = ENNReal.ofReal (holdRate Q (0, i)) *
        (∑' L, g72mab_PS P (0, i) (L + 1) (1, l) fun z => 0 < z.1) *
        (∑' L, g72mab_PS P (1, l) (L + 1) (2, k) fun z => 1 < z.1) *
        (ENNReal.ofReal (holdRate Q (2, k)))⁻¹ *
        ((ENNReal.ofReal (holdRate Q (1, l)))⁻¹ * ENNReal.ofReal (holdRate Q (1, l))) := by
        rw [h1]; ring
    _ = _ := by ring

end Q

end S202IR

namespace S202IR
open S202CG

section Q2
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma rowid (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂)) (i j : ι) :
    rateR (qbdQ B A₀ A₁ A₂) 0 i j * ENNReal.ofReal (holdRate (qbdQ B A₀ A₁ A₂) (1, j)) =
      ENNReal.ofReal (A₀ i j) +
      ∑' l, (if l = j then 0 else rateR (qbdQ B A₀ A₁ A₂) 0 i l * ENNReal.ofReal (A₁ l j)) +
      ∑' k, (∑' l, rateR (qbdQ B A₀ A₁ A₂) 0 i l * rateR (qbdQ B A₀ A₁ A₂) 1 l k) *
        ENNReal.ofReal (A₂ k j) := by
  classical
  set Q := qbdQ B A₀ A₁ A₂ with hQd
  set P := jumpP Q with hPd
  have hq := cg_qpos Q hQ
  set E : ℕ × ι → ℝ≥0∞ := fun w => ∑' L, g72mab_PS P (0, i) (L + 1) w (fun z => 0 < z.1) with hE
  have hR : ∀ l, rateR Q 0 i l = ENNReal.ofReal (holdRate Q (0, i)) * E (1, l) *
      (ENNReal.ofReal (holdRate Q (1, l)))⁻¹ := by
    intro l; rw [cg_rateS B A₀ A₁ A₂ 0 i l]
  have hq0 : ENNReal.ofReal (holdRate Q (0, i)) * (ENNReal.ofReal (holdRate Q (0, i)))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp [hq (0, i)]) ENNReal.ofReal_ne_top
  have hL : rateR Q 0 i j * ENNReal.ofReal (holdRate Q (1, j)) =
      ENNReal.ofReal (holdRate Q (0, i)) * E (1, j) := by
    rw [hR, mul_assoc, hr_mul Q hQ, mul_one]
  rw [hL]
  have hb := bal P (0, i) (fun z => 0 < z.1) (1, j)
  change E (1, j) = _ + ∑' w, (if 0 < w.1 then E w * _ else 0) at hb
  rw [hb, mul_add, ← ENNReal.tsum_mul_left, add_assoc]
  congr 1
  · rw [pq B A₀ A₁ A₂ hQ _ _ (by simp), ← mul_assoc, hq0, one_mul]
    exact congrArg ENNReal.ofReal (cg_Q_up B A₀ A₁ A₂ 0 i j)
  set G : ℕ × ι → ℝ≥0∞ := fun w => ENNReal.ofReal (holdRate Q (0, i)) *
    (if 0 < w.1 then E w * ENNReal.ofReal (P w (1, j)) else 0) with hG
  rw [show ∑' w, G w = ∑' n, ∑' l, G (n, l) from ENNReal.tsum_prod (f := fun n l => G (n, l))]
  rw [tsum_eq_sum (s := {1, 2})]
  · rw [Finset.sum_pair (by norm_num)]
    congr 1
    · refine tsum_congr fun l => ?_
      simp only [hG]
      rw [if_pos Nat.one_pos]
      by_cases hl : l = j
      · subst hl
        simp [hPd, jumpP]
      · rw [if_neg hl, hR l, pq B A₀ A₁ A₂ hQ _ _ (by simp [Ne.symm hl])]
        have := q11 B A₀ A₁ A₂ 0 l j
        simp only [zero_add] at this
        rw [this]
        ring
    · refine tsum_congr fun k => ?_
      simp only [hG]
      rw [if_pos (by norm_num), pq B A₀ A₁ A₂ hQ _ _ (by simp), ← lvl2 B A₀ A₁ A₂ hQ i k]
      have := q21 B A₀ A₁ A₂ 0 k j
      simp only [zero_add] at this
      rw [this]
      ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    refine ENNReal.tsum_eq_zero.mpr fun l => ?_
    simp only [hG]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · rw [if_pos h0, pq B A₀ A₁ A₂ hQ _ _ (by simp; omega), qz B A₀ A₁ A₂ n 1 l j (by omega)
        (by omega) (by omega)]
      simp

end Q2

end S202IR

namespace S202IR
open S202CG

section Q3
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma ident (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂)) (θ : ι → ℝ) (η : ℝ) (hθ : ∀ i, 0 ≤ θ i)
    (hη : 0 < η)
    (hR : ∀ j, ∑' i, ENNReal.ofReal (θ i) * rateR (qbdQ B A₀ A₁ A₂) 0 i j =
      ENNReal.ofReal (η * θ j)) (j : ι) :
    ∃ s0 s1 s2 : ℝ, HasSum (fun i => θ i * A₀ i j) s0 ∧ HasSum (fun i => θ i * A₁ i j) s1 ∧
      HasSum (fun i => θ i * A₂ i j) s2 ∧ s0 + η * s1 + η ^ 2 * s2 = 0 := by
  classical
  set Q := qbdQ B A₀ A₁ A₂ with hQd
  have hq := cg_qpos Q hQ
  have hA0 : ∀ i, 0 ≤ A₀ i j := fun i => by
    have := hQ.1 (0, i) (1, j) (by simp); rwa [show Q (0, i) (1, j) = A₀ i j from
      cg_Q_up B A₀ A₁ A₂ 0 i j] at this
  have hA1 : ∀ l, l ≠ j → 0 ≤ A₁ l j := fun l hl => by
    have := hQ.1 (1, l) (1, j) (by simp [hl])
    have e : Q (1, l) (1, j) = A₁ l j := by simpa using q11 B A₀ A₁ A₂ 0 l j
    rwa [e] at this
  have hA2 : ∀ k, 0 ≤ A₂ k j := fun k => by
    have := hQ.1 (2, k) (1, j) (by simp)
    have e : Q (2, k) (1, j) = A₂ k j := by simpa using q21 B A₀ A₁ A₂ 0 k j
    rwa [e] at this
  have hq1 : holdRate Q (1, j) = - A₁ j j := by
    unfold holdRate
    have e : Q (1, j) (1, j) = A₁ j j := by simpa using q11 B A₀ A₁ A₂ 0 j j
    rw [e]
  have hR1 : rateR Q 1 = rateR Q 0 := by
    funext a b; rw [cg_rate B A₀ A₁ A₂ hQ, cg_rate B A₀ A₁ A₂ hQ]
  set f0 : ι → ℝ := fun i => θ i * A₀ i j with hf0
  set f1 : ι → ℝ := fun l => if l = j then 0 else η * θ l * A₁ l j with hf1
  set f2 : ι → ℝ := fun k => η * (η * θ k) * A₂ k j with hf2
  have h0 : ∀ i, 0 ≤ f0 i := fun i => mul_nonneg (hθ i) (hA0 i)
  have h1 : ∀ i, 0 ≤ f1 i := fun l => by
    simp only [hf1]; split_ifs with hl
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg hη.le (hθ l)) (hA1 l hl)
  have h2 : ∀ i, 0 ≤ f2 i := fun k =>
    mul_nonneg (mul_nonneg hη.le (mul_nonneg hη.le (hθ k))) (hA2 k)
  have hsum : ∑' i, ENNReal.ofReal (f0 i) + ∑' i, ENNReal.ofReal (f1 i) +
      ∑' i, ENNReal.ofReal (f2 i) = ENNReal.ofReal (η * θ j * holdRate Q (1, j)) := by
    have hrow := fun i => rowid B A₀ A₁ A₂ hQ i j
    simp only [← hQd] at hrow
    have hL : ∑' i, ENNReal.ofReal (θ i) * (rateR Q 0 i j * ENNReal.ofReal (holdRate Q (1, j))) =
        ENNReal.ofReal (η * θ j * holdRate Q (1, j)) := by
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right, hR j, ← ENNReal.ofReal_mul (mul_nonneg hη.le (hθ j))]
    rw [← hL]
    simp_rw [hrow, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_add]
    congr 1
    congr 1
    · refine tsum_congr fun i => ?_
      rw [hf0, ENNReal.ofReal_mul (hθ i)]
    · simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun l => ?_
      by_cases hl : l = j
      · simp [hf1, hl]
      · simp only [hf1, hl, if_false]
        simp_rw [← mul_assoc]
        rw [ENNReal.tsum_mul_right, hR l, ← ENNReal.ofReal_mul (mul_nonneg hη.le (hθ l))]
    · simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun k => ?_
      have e1 : ∀ i, ENNReal.ofReal (θ i) * ((∑' l, rateR Q 0 i l * rateR Q 1 l k) *
          ENNReal.ofReal (A₂ k j)) = (∑' l, ENNReal.ofReal (θ i) * rateR Q 0 i l * rateR Q 0 l k) *
          ENNReal.ofReal (A₂ k j) := by
        intro i
        rw [hR1, ← mul_assoc, ← ENNReal.tsum_mul_left]
        simp_rw [mul_assoc]
      simp_rw [e1]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_right, hR]
      simp_rw [ENNReal.ofReal_mul hη.le, mul_assoc]
      rw [ENNReal.tsum_mul_left, hR k, hf2, ENNReal.ofReal_mul (mul_nonneg hη.le (mul_nonneg hη.le (hθ k))),
        ENNReal.ofReal_mul hη.le]
  have hc : 0 ≤ η * θ j * holdRate Q (1, j) := mul_nonneg (mul_nonneg hη.le (hθ j)) (hq _).le
  obtain ⟨g0, g1, g2, gs⟩ := ennsum3 f0 f1 f2 h0 h1 h2 _ hc hsum
  refine ⟨∑' i, f0 i, ((∑' i, f1 i) + η * θ j * A₁ j j) / η, (∑' i, f2 i) / η ^ 2, g0, ?_, ?_, ?_⟩
  · have := (g1.add (hasSum_ite_eq j (η * θ j * A₁ j j))).div_const η
    have e : (fun l => θ l * A₁ l j) =
        fun l => (f1 l + (if l = j then η * θ j * A₁ j j else 0)) / η := by
      funext l
      by_cases hl : l = j
      · subst hl; simp [hf1]; field_simp
      · simp [hf1, hl]; field_simp
    rw [e]; exact this
  · have := g2.div_const (η ^ 2)
    have e : (fun k => θ k * A₂ k j) = fun k => f2 k / η ^ 2 := by
      funext k
      simp only [hf2]
      field_simp
    rw [e]; exact this
  · rw [hq1] at gs
    field_simp
    linarith

end Q3

end S202IR

namespace S202IR
open S202CG

lemma hs_congr {α : Type*} {f g : α → ℝ} {a b : ℝ} (h : HasSum f a) (hfg : ∀ x, f x = g x)
    (hab : a = b) : HasSum g b := by
  have e : g = f := funext fun x => (hfg x).symm
  rw [e, ← hab]; exact h

lemma lev_hasSum {ι : Type*} (f : ℕ × ι → ℝ) (S : Finset ℕ) (s : ℕ → ℝ)
    (hz : ∀ n ∉ S, ∀ k, f (n, k) = 0) (hs : ∀ n ∈ S, HasSum (fun k => f (n, k)) (s n)) :
    HasSum f (∑ n ∈ S, s n) := by
  classical
  have e : f = fun x => ∑ n ∈ S, (if x.1 = n then f x else 0) := by
    funext x
    by_cases hx : x.1 ∈ S
    · rw [Finset.sum_eq_single x.1]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd hx h
    · rw [Finset.sum_eq_zero]
      · have := hz x.1 hx x.2; simpa using this
      · intro n hn
        have : x.1 ≠ n := fun h => hx (h ▸ hn)
        simp [this]
  rw [e]
  refine hasSum_sum fun n hn => ?_
  have hinj : Function.Injective (fun k : ι => ((n, k) : ℕ × ι)) := fun a b h => by simpa using h
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro x hx
    have : x.1 ≠ n := by
      intro h; apply hx; exact ⟨x.2, Prod.ext h.symm rfl⟩
    simp [this]
  · exact hs_congr (hs n hn) (fun k => by simp) rfl

section Fin
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma cand_stat (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂)) (θ : ι → ℝ) (η : ℝ)
    (hθ : ∀ i, 0 < θ i) (hθ1 : HasSum θ 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hR : ∀ j, ∑' i, ENNReal.ofReal (θ i) * rateR (qbdQ B A₀ A₁ A₂) 0 i j =
      ENNReal.ofReal (η * θ j))
    (hB : ∀ j, HasSum (fun i => θ i * (B i j + η * A₂ i j)) 0) :
    IsStationaryCT (qbdQ B A₀ A₁ A₂) (fun x => (1 - η) * η ^ x.1 * θ x.2) := by
  classical
  have h1η : 0 < 1 - η := by linarith
  refine ⟨fun x => mul_nonneg (mul_nonneg h1η.le (pow_nonneg hη0.le _)) (hθ _).le, ?_, ?_⟩
  · have hg : HasSum (fun n : ℕ => (1 - η) * η ^ n) 1 := by
      have := (hasSum_geometric_of_lt_one hη0.le hη1).mul_left (1 - η)
      rwa [mul_inv_cancel₀ h1η.ne'] at this
    have := hg.mul hθ1 (Summable.mul_of_nonneg hg.summable hθ1.summable
      (fun n => mul_nonneg h1η.le (pow_nonneg hη0.le _)) (fun i => (hθ i).le))
    rw [mul_one] at this
    exact this
  · rintro ⟨m, j⟩
    obtain ⟨s0, s1, s2, g0, g1, g2, hs⟩ :=
      ident B A₀ A₁ A₂ hQ θ η (fun i => (hθ i).le) hη0 hR j
    rcases m with _ | m
    · have gB : HasSum (fun i => θ i * B i j) (0 - η * s2) :=
        hs_congr ((hB j).sub (g2.mul_left η)) (fun i => by ring) rfl
      have := lev_hasSum (fun x => (1 - η) * η ^ x.1 * θ x.2 * qbdQ B A₀ A₁ A₂ x (0, j)) {0, 1}
        (fun n => if n = 0 then (1 - η) * (0 - η * s2) else (1 - η) * η * s2) ?_ ?_
      · rw [Finset.sum_pair (by norm_num)] at this
        simp only [if_true, one_ne_zero, if_false] at this
        exact hs_congr this (fun x => rfl) (by ring)
      · intro n hn k
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        rw [qz B A₀ A₁ A₂ n 0 k j (by omega) (by omega) (by omega), mul_zero]
      · intro n hn
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with h | h <;> rw [h]
        · simp only [if_true]
          exact hs_congr (gB.mul_left (1 - η)) (fun k => by rw [q00]; ring) rfl
        · simp only [one_ne_zero, if_false]
          exact hs_congr (g2.mul_left ((1 - η) * η)) (fun k => by rw [q10]; ring) (by ring)
    · have hmem1 : m ∉ ({m + 1, m + 2} : Finset ℕ) := by simp
      have hmem2 : m + 1 ∉ ({m + 2} : Finset ℕ) := by simp
      have := lev_hasSum (fun x => (1 - η) * η ^ x.1 * θ x.2 * qbdQ B A₀ A₁ A₂ x (m + 1, j))
        {m, m + 1, m + 2}
        (fun n => if n = m then (1 - η) * η ^ m * s0 else if n = m + 1 then
          (1 - η) * η ^ (m + 1) * s1 else (1 - η) * η ^ (m + 2) * s2) ?_ ?_
      · rw [Finset.sum_insert hmem1, Finset.sum_insert hmem2, Finset.sum_singleton] at this
        simp only [if_true, show m + 1 ≠ m by omega, show m + 2 ≠ m by omega,
          show m + 2 ≠ m + 1 by omega, if_false] at this
        have h0 : (1 - η) * η ^ m * (s0 + η * s1 + η ^ 2 * s2) = 0 := by rw [hs, mul_zero]
        exact hs_congr this (fun x => rfl) (by rw [← h0]; ring)
      · intro n hn k
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        rw [qz B A₀ A₁ A₂ n (m + 1) k j (by omega) (by omega) (by omega), mul_zero]
      · intro n hn
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with h | h | h <;> rw [h]
        · simp only [if_true]
          exact hs_congr (g0.mul_left ((1 - η) * η ^ m)) (fun k => by rw [cg_Q_up]; ring) rfl
        · simp only [show m + 1 ≠ m by omega, if_true, if_false]
          exact hs_congr (g1.mul_left ((1 - η) * η ^ (m + 1))) (fun k => by rw [q11]; ring) rfl
        · simp only [show m + 2 ≠ m by omega, show m + 2 ≠ m + 1 by omega, if_false]
          exact hs_congr (g2.mul_left ((1 - η) * η ^ (m + 2))) (fun k => by rw [q21]; ring) rfl

end Fin

end S202IR

namespace S202IR
open S202CG

section Main
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma fwd (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂))
    (hirr : IrreducibleCT (qbdQ B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrentCT (qbdQ B A₀ A₁ A₂) x)
    (π : ℕ × ι → ℝ) (hπ : IsStationaryCT (qbdQ B A₀ A₁ A₂) π)
    (hind : LevelPhaseIndependent π) :
    ∃ (θ : ι → ℝ) (η : ℝ), (∀ i, 0 < θ i) ∧ HasSum θ 1 ∧ 0 < η ∧ η < 1 ∧
        (∀ j, ∑' i, ENNReal.ofReal (θ i) * rateR (qbdQ B A₀ A₁ A₂) 0 i j =
          ENNReal.ofReal (η * θ j)) ∧
        (∀ j, HasSum (fun i => θ i * (B i j + η * A₂ i j)) 0) := by
  classical
  obtain ⟨α, v, hα0, hα1, hv0, hv1, hπαv⟩ := hind
  obtain ⟨R, N, -, -, hrate, -, -, hpow⟩ := cg_main B A₀ A₁ A₂ π hQ hirr hpos hπ
  have hπpos : ∀ x, 0 < π x := by
    intro x
    have h := nu_pos _ hQ hirr π hπ x
    have h2 : ENNReal.ofReal (π x) ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr h2)
  obtain ⟨j0⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact one_ne_zero (hv1.unique hasSum_empty)
  have hαpos : ∀ n, 0 < α n := by
    intro n
    have := hπpos (n, j0)
    rw [hπαv] at this
    refine lt_of_le_of_ne (hα0 n) fun h => ?_
    rw [← h, zero_mul] at this; exact lt_irrefl _ this
  have hvpos : ∀ i, 0 < v i := by
    intro i
    have := hπpos (0, i)
    rw [hπαv] at this
    refine lt_of_le_of_ne (hv0 i) fun h => ?_
    rw [← h, mul_zero] at this; exact lt_irrefl _ this
  have hstep : ∀ n j, ENNReal.ofReal (π (n + 1, j)) =
      ∑' i, ENNReal.ofReal (π (n, i)) * rateR (qbdQ B A₀ A₁ A₂) 0 i j := by
    intro n j
    rw [hpow (n + 1) j]
    simp only [matPowE]
    rw [← cg_assoc]
    have e : vecMulE (fun i => ENNReal.ofReal (π (0, i))) (matPowE (ennMat R) n) =
        fun i => ENNReal.ofReal (π (n, i)) := funext fun i => (hpow n i).symm
    rw [e, hrate 0]
    rfl
  set η := α 1 / α 0 with hη
  set T : ι → ℝ≥0∞ := fun j => ∑' i, ENNReal.ofReal (v i) * rateR (qbdQ B A₀ A₁ A₂) 0 i j
    with hT
  have hgen : ∀ n j, ENNReal.ofReal (α (n + 1) * v j) = ENNReal.ofReal (α n) * T j := by
    intro n j
    rw [← hπαv, hstep n j, hT, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [hπαv, ENNReal.ofReal_mul (hα0 n), mul_assoc]
  have hTj : ∀ j, T j = ENNReal.ofReal (η * v j) := by
    intro j
    have h1 := hgen 0 j
    have h2 : ENNReal.ofReal (α (0 + 1) * v j) = ENNReal.ofReal (α 0) * ENNReal.ofReal (η * v j) := by
      rw [← ENNReal.ofReal_mul (hα0 0)]
      congr 1
      rw [hη]; field_simp [(hαpos 0).ne']
    rw [h2] at h1
    exact ((ENNReal.mul_right_inj (by simp [hαpos 0]) ENNReal.ofReal_ne_top).mp h1).symm
  have hη0 : 0 < η := div_pos (hαpos 1) (hαpos 0)
  have hαrec : ∀ n, α (n + 1) = α n * η := by
    intro n
    have h1 := hgen n j0
    rw [hTj j0, ← ENNReal.ofReal_mul (hα0 n)] at h1
    have h2 := (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (hα0 _) (hv0 j0))
      (mul_nonneg (hα0 n) (mul_nonneg hη0.le (hv0 j0)))).mp h1
    have h3 : (α (n + 1) - α n * η) * v j0 = 0 := by rw [sub_mul, h2]; ring
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · exact absurd h (hvpos j0).ne'
  have hη1 : η < 1 := by
    by_contra hc
    push Not at hc
    have hge : ∀ n, α 0 ≤ α n := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        rw [hαrec n]
        calc α 0 ≤ α n := ih
          _ = α n * 1 := (mul_one _).symm
          _ ≤ α n * η := mul_le_mul_of_nonneg_left hc (hα0 n)
    have ht := hα1.summable.tendsto_atTop_zero
    have := ht.eventually (gt_mem_nhds (hαpos 0))
    obtain ⟨n, hn⟩ := this.exists
    linarith [hge n]
  refine ⟨v, η, hvpos, hv1, hη0, hη1, hTj, fun j => ?_⟩
  -- level-0 balance
  set f : ℕ × ι → ℝ := fun x => π x * qbdQ B A₀ A₁ A₂ x (0, j) with hf
  have hfs : HasSum f 0 := hπ.2.2 (0, j)
  have hinj : ∀ n, Function.Injective (fun k : ι => ((n, k) : ℕ × ι)) :=
    fun n a b h => by simpa using h
  have hlev : ∀ n, HasSum (fun k => f (n, k)) (∑' k, f (n, k)) :=
    fun n => (hfs.summable.comp_injective (hinj n)).hasSum
  have hall := lev_hasSum f {0, 1} (fun n => ∑' k, f (n, k)) (fun n hn k => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp only [hf]
      rw [qz B A₀ A₁ A₂ n 0 k j (by omega) (by omega) (by omega), mul_zero])
    (fun n _ => hlev n)
  rw [Finset.sum_pair (by norm_num)] at hall
  have h01 := hfs.unique hall
  have hsum := ((hlev 0).add (hlev 1)).div_const (α 0)
  rw [← h01, zero_div] at hsum
  refine hs_congr hsum (fun i => ?_) rfl
  simp only [hf, hπαv, q00, q10]
  rw [show α 1 = α 0 * η by rw [hη]; field_simp [(hαpos 0).ne']]
  have h0 := (hαpos 0).ne'
  field_simp

end Main

end S202IR

open MatrixAnalytic.ProductForm in
open scoped ENNReal in
theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂))
    (hirr : IrreducibleCT (qbdQ B A₀ A₁ A₂))
    (hreg : RegularCT (qbdQ B A₀ A₁ A₂)) :
    (((∀ x : ℕ × ι, PositiveRecurrentCT (qbdQ B A₀ A₁ A₂) x) ∧
        ∃ π : ℕ × ι → ℝ, IsStationaryCT (qbdQ B A₀ A₁ A₂) π ∧ LevelPhaseIndependent π) ↔
      ∃ (θ : ι → ℝ) (η : ℝ), (∀ i, 0 < θ i) ∧ HasSum θ 1 ∧ 0 < η ∧ η < 1 ∧
        (∀ j, ∑' i, ENNReal.ofReal (θ i) * rateR (qbdQ B A₀ A₁ A₂) 0 i j =
          ENNReal.ofReal (η * θ j)) ∧
        (∀ j, HasSum (fun i => θ i * (B i j + η * A₂ i j)) 0)) ∧
    ∀ (θ : ι → ℝ) (η : ℝ), (∀ i, 0 < θ i) → HasSum θ 1 → 0 < η → η < 1 →
      (∀ j, ∑' i, ENNReal.ofReal (θ i) * rateR (qbdQ B A₀ A₁ A₂) 0 i j =
        ENNReal.ofReal (η * θ j)) →
      (∀ j, HasSum (fun i => θ i * (B i j + η * A₂ i j)) 0) →
      ∀ π : ℕ × ι → ℝ, IsStationaryCT (qbdQ B A₀ A₁ A₂) π →
        ∀ n i, π (n, i) = (1 - η) * η ^ n * θ i := by
  refine ⟨⟨fun ⟨hpos, π, hπ, hind⟩ => S202IR.fwd B A₀ A₁ A₂ hQ hirr hpos π hπ hind, ?_⟩, ?_⟩
  · rintro ⟨θ, η, hθ, hθ1, hη0, hη1, hR, hB⟩
    have hst := S202IR.cand_stat B A₀ A₁ A₂ hQ θ η hθ hθ1 hη0 hη1 hR hB
    refine ⟨fun x => S202IR.pr_of_stat _ hQ hirr hreg _ hst x, _, hst,
      fun n => (1 - η) * η ^ n, θ, fun n => mul_nonneg (by linarith) (pow_nonneg hη0.le n),
      ?_, fun i => (hθ i).le, hθ1, fun n i => rfl⟩
    have := (hasSum_geometric_of_lt_one hη0.le hη1).mul_left (1 - η)
    rwa [mul_inv_cancel₀ (by linarith : (1 - η) ≠ 0)] at this
  · intro θ η hθ hθ1 hη0 hη1 hR hB π hπ n i
    have hst := S202IR.cand_stat B A₀ A₁ A₂ hQ θ η hθ hθ1 hη0 hη1 hR hB
    exact S202IR.stat_uniq _ hQ hirr (n, i) (S202IR.pr_of_stat _ hQ hirr hreg _ hst (n, i))
      π _ hπ hst (n, i)
