-- Prove2me | solution 1 for MatrixAnalytic.MatrixGeometric.boundary_distribution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T15:40:34.927691+00:00
-- url     : https://prove2.me/submissions/db22688e-c030-4376-85f5-bf6307f7059d

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Chain
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage

-- ===== Base =====

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric

noncomputable def x5bd_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def x5bd_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then x5bd_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma x5bd_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5bd_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * x5bd_W P ω := by
  unfold x5bd_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma x5bd_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5bd_W P (Fin.snoc ω k : Fin (n + 2) → V) = x5bd_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold x5bd_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma x5bd_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma x5bd_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma x5bd_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma x5bd_PS_zero (x y : V) (A : V → Prop) :
    x5bd_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold x5bd_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [x5bd_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma x5bd_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma x5bd_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5bd_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then x5bd_PS P z L y A else 0) := by
  classical
  unfold x5bd_PS
  rw [x5bd_tsum_cons, tsum_eq_single x]
  · simp_rw [x5bd_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := x5bd_cond_cons x y A ω
      rw [x5bd_W_cons]
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

lemma x5bd_PS_one (x y : V) (A : V → Prop) :
    x5bd_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [x5bd_PS_cons P, tsum_eq_single y]
  · simp [x5bd_PS_zero]
  · intro z hz; simp [x5bd_PS_zero, hz]

open Classical in
noncomputable def x5bd_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then x5bd_W P ω else 0

open Classical in
noncomputable def x5bd_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then x5bd_W P ω else 0

lemma x5bd_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5bd_AV P x A (t + 1) + x5bd_EX P x A (t + 1) = x5bd_AV P x A t := by
  classical
  unfold x5bd_AV x5bd_EX
  rw [x5bd_tsum_snoc, x5bd_tsum_snoc, ← ENNReal.tsum_add]
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
  simp_rw [hz, hA, hB, Fin.snoc_last, x5bd_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        x5bd_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        x5bd_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        x5bd_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
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

lemma x5bd_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5bd_AV P x A t + ∑ k ∈ Finset.range t, x5bd_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold x5bd_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [x5bd_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (x5bd_EX P x A (t + 1)), ← add_assoc,
      add_comm (x5bd_EX P x A (t + 1)), x5bd_step P hrow x A t, ih]

lemma x5bd_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    x5bd_PS P x k y A ≤ x5bd_EX P x A k := by
  classical
  unfold x5bd_PS x5bd_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma x5bd_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, x5bd_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← x5bd_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => x5bd_PS_le_EX P x y A hy (k + 1)).trans le_add_self

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma x5bd_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → x5bd_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5bd_PS P x (s + 1) z (fun z => m + 1 < lev z) * x5bd_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [x5bd_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', x5bd_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then x5bd_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        x5bd_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * x5bd_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [x5bd_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5bd_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        x5bd_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          x5bd_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5bd_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          x5bd_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          x5bd_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          x5bd_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5bd_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [x5bd_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
        by_cases hz : lev z = m + 1
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun w => ?_
          by_cases hw : m + 1 < lev w
          · simp [hw, mul_assoc]
          · simp [hw]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_left]
      by_cases hw : m + 1 < lev w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.mul_sum]
    by_cases hw1 : lev w = m + 1
    · simp [hw1]
    · by_cases hw2 : m + 1 < lev w
      · rw [if_pos (Or.inr (by omega)), ih w (by omega)]
        simp [hw1, hw2]
      · have hw3 : ¬ m < lev w := by omega
        simp [hw1, hw2, hw3]
end Gen

section Gen3
variable {V : Type*} (P : V → V → ℝ)

lemma x5bd_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma x5bd_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5bd_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then x5bd_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold x5bd_PS
  rw [x5bd_tsum_snoc]
  simp_rw [x5bd_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := x5bd_cond_snoc x y A ω
    rw [x5bd_W_snoc]
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

/-- last-visit decomposition -/
lemma x5bd_conv3 (InvT mid A A' : V → Prop) [DecidablePred mid] (x : V) (hx : mid x)
    (hstep : ∀ w y, InvT y → P w y ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ InvT w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ L y, InvT y → x5bd_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5bd_PS P x s z A * x5bd_PS P z (L + 1 - s) y A' else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [x5bd_PS_one]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, x5bd_PS_one]
    rw [tsum_eq_single x]
    · rw [if_pos hx, x5bd_PS_zero, if_pos rfl, one_mul]
    · intro z hz
      rw [x5bd_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ L ih =>
    intro y hy
    rw [Finset.sum_range_succ, x5bd_PS_snoc P x (L + 1)]
    have hlast : ∀ z, (if mid z then x5bd_PS P x (L + 1) z A *
        x5bd_PS P z (L + 1 + 1 - (L + 1)) y A' else 0) =
        if mid z then x5bd_PS P x (L + 1) z A * ENNReal.ofReal (P z y) else 0 := fun z => by
      rw [show L + 1 + 1 - (L + 1) = 1 by omega, x5bd_PS_one]
    simp_rw [hlast]
    have h1 : ∀ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5bd_PS P x s z A * x5bd_PS P z (L + 1 + 1 - s) y A' else 0) =
        ∑' w, (if A' w then ∑' z, (if mid z then
          x5bd_PS P x s z A * x5bd_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
      intro s hs
      have hs' : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have e : ∀ z, (if mid z then
          x5bd_PS P x s z A * x5bd_PS P z (L + 1 + 1 - s) y A' else 0) =
          ∑' w, (if A' w then (if mid z then
          x5bd_PS P x s z A * x5bd_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
        intro z
        rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, x5bd_PS_snoc P z (L + 1 - s)]
        by_cases hz : mid z
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun w => ?_
          have : ¬ (L + 1 - s = 0) := by omega
          by_cases hw : A' w
          · simp [hw, this, mul_assoc]
          · simp [hw, this]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_right]
      by_cases hw : A' w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.sum_mul]
    by_cases hPw : P w y = 0
    · simp [hPw]
    rcases hstep w y hy hPw with ⟨hm, hA, hA'⟩ | ⟨hA', hA, hI, hm⟩ | ⟨hA, hA', hm⟩
    · simp [hm, hA, hA']
    · rw [if_pos (Or.inr hA), ih w hI]
      simp [hm, hA']
    · simp [hA, hA', hm]

lemma x5bd_cauchy0 (a b : ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) = (∑' s, a s) * ∑' u, b u := by
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun s t => a s * b t),
    ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun k => ?_
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal k)
    (fun p : ℕ × ℕ => a p.1 * b p.2), Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun s t => a s * b t)]

end Gen3

section QBDm
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma x5bd_qnz (x w : ℕ × ι) (h : qbdP B A₀ A₁ A₂ x w ≠ 0) : w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 := by
  unfold qbdP at h
  split_ifs at h <;> first | omega | exact absurd rfl h

omit [Countable ι] [DecidableEq ι] in
lemma x5bd_qshiftN (a b : ℕ) (i j : ι) (ha : 1 ≤ a) :
    qbdP B A₀ A₁ A₂ (a + 1, i) (b + 1, j) = qbdP B A₀ A₁ A₂ (a, i) (b, j) := by
  unfold qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

def x5bd_sh {L : ℕ} (ω : Fin (L + 1) → ℕ × ι) : Fin (L + 1) → ℕ × ι :=
  fun s => ((ω s).1 + 1, (ω s).2)

omit [Countable ι] [DecidableEq ι] in
lemma x5bd_sh_inj {L : ℕ} : Function.Injective (x5bd_sh (ι := ι) (L := L)) := by
  intro ω ω' h
  funext s
  have := congrFun h s
  simp only [x5bd_sh, Prod.mk.injEq] at this
  exact Prod.ext (by omega) this.2

lemma x5bd_PS_shiftN (n a b : ℕ) (i j : ι) (ha : 1 ≤ a) (L : ℕ) :
    x5bd_PS (qbdP B A₀ A₁ A₂) (a + 1, i) L (b + 1, j) (fun z => n + 1 < z.1) =
      x5bd_PS (qbdP B A₀ A₁ A₂) (a, i) L (b, j) (fun z => n < z.1) := by
  classical
  unfold x5bd_PS
  rw [← x5bd_sh_inj.tsum_eq]
  · refine tsum_congr fun ω => ?_
    have hc : ((x5bd_sh ω) 0 = (a + 1, i) ∧ (x5bd_sh ω) (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < ((x5bd_sh ω) m).1) ↔
        (ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1) := by
      simp only [x5bd_sh, Prod.ext_iff, add_left_inj, Nat.add_lt_add_iff_right]
    by_cases h : ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1
    · rw [if_pos (hc.mpr h), if_pos h]
      unfold x5bd_W
      refine Finset.prod_congr rfl fun s _ => ?_
      have hl : 1 ≤ (ω s.castSucc).1 := by
        by_cases hs : s.castSucc = 0
        · rw [hs, h.1]; exact ha
        · have := h.2.2 s.castSucc hs (Fin.castSucc_ne_last s); omega
      simp only [x5bd_sh]
      rw [x5bd_qshiftN B A₀ A₁ A₂ _ _ _ _ hl]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
  · intro ω hω
    rw [Function.mem_support] at hω
    have hcond : ω 0 = (a + 1, i) ∧ ω (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < (ω m).1 := by
      by_contra hn; exact hω (if_neg hn)
    refine ⟨fun s => ((ω s).1 - 1, (ω s).2), funext fun s => ?_⟩
    have : 1 ≤ (ω s).1 := by
      by_cases h0 : s = 0
      · rw [h0, hcond.1]; omega
      by_cases hl : s = Fin.last L
      · rw [hl, hcond.2.1]; omega
      have := hcond.2.2 s h0 hl; omega
    simp only [x5bd_sh]
    exact Prod.ext (by simp; omega) rfl

lemma x5bd_eva (n : ℕ) (x y : ℕ × ι) (hy : n < y.1) :
    expVisitsAvoid (qbdP B A₀ A₁ A₂) (levelsUpTo n) x y =
      ∑' t, x5bd_PS (qbdP B A₀ A₁ A₂) x t y (fun z => n < z.1) := by
  classical
  unfold expVisitsAvoid x5bd_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  have hc : (ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ levelsUpTo n) ↔
      (ω 0 = x ∧ ω (Fin.last t) = y ∧
        ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → n < (ω m).1) := by
    simp only [levelsUpTo, Set.mem_setOf_eq, not_le]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun m hm _ => h3 m hm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun m hm => ?_⟩
      by_cases hl : m = Fin.last t
      · rw [hl, h2]; exact hy
      · exact h3 m hm hl
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧
      ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → n < (ω m).1
  · rw [if_pos (hc.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

end QBDm

lemma x5bd_levn {ι : Type*} (n : ℕ) (f : ℕ × ι → ℝ≥0∞) :
    ∑' z : ℕ × ι, (if z.1 = n then f z else 0) = ∑' l, f (n, l) := by
  rw [ENNReal.tsum_prod', tsum_eq_single n]
  · simp
  · intro m hm; simp [hm]

lemma x5bd_swap0 {V : Type*} (mid : V → Prop) [DecidablePred mid] (a : V → ℕ → ℝ≥0∞)
    (b : V → ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) =
      ∑' z, if mid z then (∑' s, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact x5bd_cauchy0 (a z) (b z)
  · simp [hz]

lemma x5bd_mm_assoc {ι : Type*} [Countable ι] (X Y Z : ι → ι → ℝ≥0∞) :
    matMulE (matMulE X Y) Z = matMulE X (matMulE Y Z) := by
  funext i j
  unfold matMulE
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  ring

lemma x5bd_mm_one {ι : Type*} [Countable ι] [DecidableEq ι] (X : ι → ι → ℝ≥0∞) :
    matMulE X matOneE = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single j]
  · simp
  · intro b hb; simp [hb]

lemma x5bd_pow_succ' {ι : Type*} [Countable ι] [DecidableEq ι] (X : ι → ι → ℝ≥0∞) (m : ℕ) :
    matMulE X (matPowE X m) = matPowE X (m + 1) := by
  induction m with
  | zero =>
    show matMulE X matOneE = matMulE matOneE X
    rw [x5bd_mm_one]
    funext i j
    unfold matMulE matOneE
    rw [tsum_eq_single i]
    · simp
    · intro b hb; simp [Ne.symm hb]
  | succ m ih =>
    show matMulE X (matMulE (matPowE X m) X) = matMulE (matPowE X (m + 1)) X
    rw [← x5bd_mm_assoc, ih]

theorem x5bd_nb {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (n : ℕ) :
    (∀ k : ℕ, 1 ≤ k →
      matNblock (qbdP B A₀ A₁ A₂) n (k + 1) =
        matMulE (matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1) (ennMat A₀))
          (matNblock (qbdP B A₀ A₁ A₂) n k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      matNblock (qbdP B A₀ A₁ A₂) n k =
          matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1)
            (matPowE (matMulE (ennMat A₀) (matNblock (qbdP B A₀ A₁ A₂) n 1)) (k - 1)) ∧
        matNblock (qbdP B A₀ A₁ A₂) n k =
          matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1)
            (matPowE (matR (qbdP B A₀ A₁ A₂) n) (k - 1))) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  -- N_{1k} as path sums
  have hN : ∀ k i j, 1 ≤ k → matNblock P n k i j =
      ∑' t, x5bd_PS P (n + 1, i) t (n + k, j) (fun z => n < z.1) := by
    intro k i j hk
    exact x5bd_eva B A₀ A₁ A₂ n _ _ (by simp; omega)
  -- step from level n+1 into the rest
  have hstepN : ∀ (k : ℕ) (l j : ι), 1 ≤ k →
      ∑' u, x5bd_PS P (n + 1, l) (u + 1) (n + k + 1, j) (fun z => n + 1 < z.1) =
        ∑' l', ENNReal.ofReal (A₀ l l') * matNblock P n k l' j := by
    intro k l j hk
    simp_rw [x5bd_PS_cons P (n + 1, l)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_prod', tsum_eq_single (n + 2)]
    · refine tsum_congr fun l' => ?_
      have hP2 : P (n + 1, l) (n + 2, l') = A₀ l l' := by simp [hPd, qbdP]
      rw [hP2, hN k l' j hk]
      congr 1
      refine tsum_congr fun u => ?_
      rw [if_pos (Or.inr (by simp))]
      have := x5bd_PS_shiftN B A₀ A₁ A₂ n (n + 1) (n + k) l' j (by omega) u
      rw [← hPd] at this
      rw [← this]
    · intro m hm
      refine ENNReal.tsum_eq_zero.mpr fun l' => ?_
      by_cases hPz : P (n + 1, l) (m, l') = 0
      · simp [hPz]
      have := x5bd_qnz B A₀ A₁ A₂ _ _ hPz
      simp only at this
      rw [ENNReal.tsum_eq_zero.mpr]
      · simp
      intro u
      rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
        intro h; simp only [Prod.mk.injEq] at h; omega
      · rw [if_neg]
        rintro (hu' | hu')
        · omega
        · simp only at hu'; omega
  have hR : matR P n = matMulE (ennMat A₀) (matNblock P n 1) := by
    funext i j
    unfold matR
    have hev := x5bd_eva B A₀ A₁ A₂ n (n, i) (n + 1, j) (by simp)
    rw [← hPd] at hev
    rw [hev, tsum_eq_zero_add' ENNReal.summable, x5bd_PS_zero,
      if_neg (by simp [Prod.ext_iff]), zero_add]
    simp_rw [x5bd_PS_cons P (n, i)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    unfold matMulE ennMat
    rw [ENNReal.tsum_prod', tsum_eq_single (n + 1)]
    · refine tsum_congr fun l => ?_
      have hP1 : P (n, i) (n + 1, l) = A₀ i l := by
        rw [hPd]; unfold qbdP; dsimp only; split_ifs <;> first | rfl | omega | simp_all
      rw [hP1, hN 1 l j le_rfl]
      congr 1
      refine tsum_congr fun t => ?_
      rw [if_pos (Or.inr (by simp))]
    · intro m hm
      refine ENNReal.tsum_eq_zero.mpr fun l => ?_
      by_cases hPz : P (n, i) (m, l) = 0
      · simp [hPz]
      have := x5bd_qnz B A₀ A₁ A₂ _ _ hPz
      simp only at this
      rw [ENNReal.tsum_eq_zero.mpr]
      · simp
      intro u
      rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
        intro h; simp only [Prod.mk.injEq] at h; omega
      · rw [if_neg]
        rintro (hu' | hu')
        · omega
        · simp only at hu'; omega
  have hstep3 : ∀ w y : ℕ × ι, (fun z : ℕ × ι => n + 2 ≤ z.1) y → P w y ≠ 0 →
      ((fun z : ℕ × ι => z.1 = n + 1) w ∧ (fun z : ℕ × ι => n < z.1) w ∧
        ¬ (fun z : ℕ × ι => n + 1 < z.1) w) ∨
      ((fun z : ℕ × ι => n + 1 < z.1) w ∧ (fun z : ℕ × ι => n < z.1) w ∧
        (fun z : ℕ × ι => n + 2 ≤ z.1) w ∧ ¬ (fun z : ℕ × ι => z.1 = n + 1) w) ∨
      (¬ (fun z : ℕ × ι => n < z.1) w ∧ ¬ (fun z : ℕ × ι => n + 1 < z.1) w ∧
        ¬ (fun z : ℕ × ι => z.1 = n + 1) w) := by
    intro w y hy hw
    have := x5bd_qnz B A₀ A₁ A₂ _ _ hw
    simp only at hy ⊢
    omega
  have h1 : ∀ k, 1 ≤ k → matNblock P n (k + 1) =
      matMulE (matMulE (matNblock P n 1) (ennMat A₀)) (matNblock P n k) := by
    intro k hk
    funext i j
    rw [hN (k + 1) i j (by omega), tsum_eq_zero_add' ENNReal.summable, x5bd_PS_zero,
      if_neg (by simp [Prod.ext_iff]; omega), zero_add]
    have hc := x5bd_conv3 P (fun z : ℕ × ι => n + 2 ≤ z.1) (fun z : ℕ × ι => z.1 = n + 1)
      (fun z : ℕ × ι => n < z.1) (fun z : ℕ × ι => n + 1 < z.1) (n + 1, i) rfl hstep3
    rw [tsum_congr fun t => hc t (n + (k + 1), j) (by simp; omega)]
    have e : ∀ t, ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = n + 1 then
        x5bd_PS P (n + 1, i) s z (fun z => n < z.1) *
          x5bd_PS P z (t + 1 - s) (n + (k + 1), j) (fun z => n + 1 < z.1) else 0) =
        ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = n + 1 then
        x5bd_PS P (n + 1, i) s z (fun z => n < z.1) *
          (fun z u => x5bd_PS P z (u + 1) (n + (k + 1), j) (fun z => n + 1 < z.1)) z (t - s)
          else 0) := by
      intro t
      refine Finset.sum_congr rfl fun s hs => ?_
      have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [show t + 1 - s = t - s + 1 by omega]
    refine (tsum_congr e).trans ((x5bd_swap0 (fun z : ℕ × ι => z.1 = n + 1)
      (fun z s => x5bd_PS P (n + 1, i) s z (fun z => n < z.1))
      (fun z u => x5bd_PS P z (u + 1) (n + (k + 1), j) (fun z => n + 1 < z.1))).trans ?_)
    rw [x5bd_levn]
    have hN1 : ∀ l, (∑' s, x5bd_PS P (n + 1, i) s (n + 1, l) (fun z => n < z.1)) =
        matNblock P n 1 i l := fun l => (hN 1 i l le_rfl).symm
    simp_rw [hN1, show n + (k + 1) = n + k + 1 by ring, hstepN k _ j hk]
    unfold matMulE ennMat
    simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => tsum_congr fun l' => ?_
    ring
  refine ⟨h1, fun k hk => ?_⟩
  have h2 : matNblock P n k =
      matMulE (matNblock P n 1) (matPowE (matMulE (ennMat A₀) (matNblock P n 1)) (k - 1)) := by
    induction k, hk using Nat.le_induction with
    | base => simp only [Nat.sub_self]; exact (x5bd_mm_one _).symm
    | succ k hk ih =>
      rw [h1 k hk, ih, show k + 1 - 1 = (k - 1) + 1 by omega, ← x5bd_pow_succ']
      simp only [x5bd_mm_assoc]
  exact ⟨h2, by rw [h2, hR]⟩


lemma x5bd_hR {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ) (n : ℕ) :
    matR (qbdP B A₀ A₁ A₂) n = matMulE (ennMat A₀) (matNblock (qbdP B A₀ A₁ A₂) n 1) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  funext i j
  unfold matR
  have hev := x5bd_eva B A₀ A₁ A₂ n (n, i) (n + 1, j) (by simp)
  rw [← hPd] at hev
  rw [hev, tsum_eq_zero_add' ENNReal.summable, x5bd_PS_zero,
    if_neg (by simp [Prod.ext_iff]), zero_add]
  simp_rw [x5bd_PS_cons P (n, i)]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  unfold matMulE ennMat
  rw [ENNReal.tsum_prod', tsum_eq_single (n + 1)]
  · refine tsum_congr fun l => ?_
    have hP1 : P (n, i) (n + 1, l) = A₀ i l := by
      rw [hPd]; unfold qbdP; dsimp only; split_ifs <;> first | rfl | omega | simp_all
    rw [hP1, show matNblock P n 1 l j = _ from x5bd_eva B A₀ A₁ A₂ n (n + 1, l) (n + 1, j) (by simp)]
    congr 1
    refine tsum_congr fun t => ?_
    rw [if_pos (Or.inr (by simp))]
  · intro m hm
    refine ENNReal.tsum_eq_zero.mpr fun l => ?_
    by_cases hPz : P (n, i) (m, l) = 0
    · simp [hPz]
    have := x5bd_qnz B A₀ A₁ A₂ _ _ hPz
    simp only at this
    rw [ENNReal.tsum_eq_zero.mpr]
    · simp
    intro u
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu
      rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
      intro h; simp only [Prod.mk.injEq] at h; omega
    · rw [if_neg]
      rintro (hu' | hu')
      · omega
      · simp only at hu'; omega

section GRK
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma x5bd_EX_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5bd_EX P x A k = ∑' y, if ¬ A y then x5bd_PS P x k y A else 0 := by
  classical
  unfold x5bd_EX x5bd_PS
  simp_rw [x5bd_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last k))]
  · by_cases hA : A (ω (Fin.last k)) <;> simp [hA]
  · intro y hy; simp [Ne.symm hy]

open Classical in
lemma x5bd_AV_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5bd_AV P x A (k + 1) = ∑' y, if A y then x5bd_PS P x (k + 1) y A else 0 := by
  classical
  unfold x5bd_AV x5bd_PS
  simp_rw [x5bd_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last (k + 1)))]
  · by_cases hA : A (ω (Fin.last (k + 1)))
    · simp only [hA, if_true, true_and]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun m hm _ => h2 m hm⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun m hm => ?_⟩
        by_cases hl : m = Fin.last (k + 1)
        · rw [hl]; exact hA
        · exact h2 m hm hl
    · simp only [hA, if_false]
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact hA (h2 _ (by simp [Fin.ext_iff]))
  · intro y hy; simp [Ne.symm hy]

lemma x5bd_PS_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x y : V) (L : ℕ) :
    x5bd_PS P x L y A ≤ x5bd_PS P x L y A' := by
  classical
  unfold x5bd_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, fun m h1 h2 => hAA _ (h.2.2 m h1 h2)⟩]
  · rw [if_neg h]; exact bot_le

lemma x5bd_PS_concat (A : V → Prop) (y z : V) (hy : A y) :
    ∀ u x t, x5bd_PS P x u y A * x5bd_PS P y t z A ≤ x5bd_PS P x (u + t) z A := by
  classical
  intro u
  induction u with
  | zero =>
    intro x t
    rw [x5bd_PS_zero, zero_add]
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]; exact bot_le
  | succ u ih =>
    intro x t
    rw [x5bd_PS_cons P x u y A, show u + 1 + t = (u + t) + 1 by omega,
      x5bd_PS_cons P x (u + t) z A, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [mul_assoc]
    gcongr
    by_cases hw : A w
    · rw [if_pos (Or.inr hw), if_pos (Or.inr hw)]; exact ih w t
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg (fun h => hw (by rw [h]; exact hy)), zero_mul]
        exact bot_le
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hw h]), zero_mul]; exact bot_le

lemma x5bd_taboo_extract (x0 y : V) (hy : y ≠ x0) (L : ℕ)
    (h : x5bd_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ u, x5bd_PS P x0 u y (fun z => z ≠ x0) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [x5bd_PS_zero, if_neg (Ne.symm hy)] at h; exact absurd rfl h
  rw [x5bd_conv3 P (fun _ => True) (fun z => z = x0) (fun _ => True) (fun z => z ≠ x0) x0 rfl
    (fun w _ _ _ => by by_cases hw : w = x0 <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if z = x0 then x5bd_PS P x0 s z (fun _ => True) *
      x5bd_PS P z (L + 1 - s) y (fun z => z ≠ x0) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzx : z = x0
  · rw [if_pos hzx] at hz
    subst hzx
    exact ⟨_, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzx] at hz; exact absurd rfl hz

lemma x5bd_ofReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  exact ENNReal.ofReal_tsum_of_nonneg hf hs
end GRK

section SPX
variable {ι : Type*} [Countable ι] [DecidableEq ι]
lemma x5bd_one_mm (X : ι → ι → ℝ≥0∞) : matMulE matOneE X = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single i]
  · simp
  · intro b hb; simp [Ne.symm hb]

end SPX

open Filter Topology in
lemma x5bd_sp {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∀ i j, Tendsto (fun k => (M ^ k) i j) atTop (𝓝 0)) : spectralRadius ℂ M < 1 := by
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  have hle : ∀ A : Matrix ι ι ℂ, ‖A‖₊ ≤ ∑ i, ∑ j, ‖A i j‖₊ := by
    intro A
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖₊) (fun _ _ => bot_le) (Finset.mem_univ i)
  have hn : Tendsto (fun k => ‖M ^ k‖) atTop (𝓝 0) := by
    have hs : Tendsto (fun k => ∑ i, ∑ j, ‖(M ^ k) i j‖) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
        tendsto_finsetSum (Finset.univ : Finset ι) fun j _ => (h i j).norm
      simpa using this
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hs
    have := hle (M ^ k)
    have h2 : (‖M ^ k‖₊ : ℝ) ≤ ((∑ i, ∑ j, ‖(M ^ k) i j‖₊ : NNReal) : ℝ) := by exact_mod_cast this
    simpa using h2
  obtain ⟨n, hn1⟩ : ∃ n, ‖M ^ (n + 1)‖ < 1 := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hn.eventually (gt_mem_nhds zero_lt_one))
    exact ⟨N, hN (N + 1) (by omega)⟩
  have h1 : ‖(1 : Matrix ι ι ℂ)‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Matrix.one_apply_ne' hb]
    · simp
  have hlt : (‖M ^ (n + 1)‖₊ : ENNReal) < 1 := by
    have : ‖M ^ (n + 1)‖₊ < 1 := by exact_mod_cast hn1
    exact_mod_cast this
  calc spectralRadius ℂ M ≤ (‖M ^ (n + 1)‖₊ : ENNReal) ^ (1 / (n + 1) : ℝ) *
        (‖(1 : Matrix ι ι ℂ)‖₊ : ENNReal) ^ (1 / (n + 1) : ℝ) :=
        spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ M n
    _ ≤ (‖M ^ (n + 1)‖₊ : ENNReal) ^ (1 / (n + 1) : ℝ) * 1 := by
        gcongr
        exact ENNReal.rpow_le_one (by exact_mod_cast h1) (by positivity)
    _ < 1 := by
        rw [mul_one]
        exact ENNReal.rpow_lt_one hlt (by positivity)


theorem x5bd_spsol {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) :
    (∀ i j, matR (qbdP B A₀ A₁ A₂) 0 i j ≠ ⊤) ∧
      spectralRadius ℂ
        (Matrix.of fun i j => (((matR (qbdP B A₀ A₁ A₂) 0 i j).toReal : ℝ) : ℂ)) < 1 := by
  classical
  have hnb := x5bd_nb B A₀ A₁ A₂ hP hirr hpos 0
  have hR := x5bd_hR B A₀ A₁ A₂ 0
  have hP0' := hP.1
  have hrow' := hP.2
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP0'
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hrow' z).summable, (hrow' z).tsum_eq,
      ENNReal.ofReal_one]
  have hconv : ∀ (x0 : ℕ × ι) T, ENNReal.ofReal (returnTailC P x0 T) =
      x5bd_AV P x0 (fun z => z ≠ x0) T := by
    intro x0 T
    have hAVle : x5bd_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
      le_self_add.trans_eq (x5bd_mass P hrow x0 _ T)
    unfold returnTailC setAvoidTailC
    rw [x5bd_ofReal_tsum]
    · unfold x5bd_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5bd_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
    · intro ω; split_ifs
      · exact Finset.prod_nonneg fun s _ => hP0 _ _
      · exact le_rfl
    · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
      unfold x5bd_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5bd_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
  have hnn : ∀ x0 t, 0 ≤ returnTailC P x0 t := by
    intro x0 t
    unfold returnTailC setAvoidTailC
    refine tsum_nonneg fun ω => ?_
    split_ifs
    · exact Finset.prod_nonneg fun s _ => hP0 _ _
    · exact le_rfl
  set R := matR P 0 with hRd
  have hpow : ∀ k, matPowE R (k + 1) = matMulE (ennMat A₀) (matNblock P 0 (k + 1)) := by
    intro k
    have e := (hnb.2 (k + 1) (by omega)).2
    rw [show k + 1 - 1 = k by omega] at e
    rw [← x5bd_pow_succ']
    nth_rewrite 1 [hR]
    rw [x5bd_mm_assoc, ← e]
  have hent : ∀ k i j, matPowE R (k + 1) i j ≤
      ∑' t, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) := by
    intro k i j
    rw [hpow]
    unfold matMulE ennMat
    have e2 : ∀ l, matNblock P 0 (k + 1) l j =
        ∑' t, x5bd_PS P (1, l) t (k + 1, j) (fun z => 0 < z.1) := fun l => by
      unfold matNblock
      have := x5bd_eva B A₀ A₁ A₂ 0 (0 + 1, l) (0 + (k + 1), j) (by simp)
      simp only [zero_add] at this ⊢
      rw [← hPd] at this
      exact this
    simp_rw [e2, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum fun t => ?_
    rw [x5bd_PS_cons P (0, i) t]
    have hinj : Function.Injective (fun l : ι => ((1 : ℕ), l)) := fun a b h => (Prod.mk.inj h).2
    refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
    refine ENNReal.tsum_le_tsum fun l => ?_
    have hP1 : P (0, i) (1, l) = A₀ i l := by simp [hPd, qbdP]
    simp only [hP1]
    rw [if_pos (Or.inr (by norm_num))]
  have htot : ∀ i, ∑' k, ∑' j, matPowE R (k + 1) i j ≤
      ∑' t, ENNReal.ofReal (returnTailC P (0, i) (t + 1)) := by
    intro i
    calc _ ≤ ∑' k, ∑' j, ∑' t, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) :=
          ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => hent k i j
      _ = ∑' t, ∑' k, ∑' j, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) := by
          conv_lhs => arg 1; ext k; rw [ENNReal.tsum_comm]
          rw [ENNReal.tsum_comm]
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun t => ?_
          rw [hconv, x5bd_AV_eq]
          have hinj : Function.Injective (fun p : ℕ × ι => (p.1 + 1, p.2)) := by
            intro a b h
            simp only [Prod.mk.injEq] at h
            exact Prod.ext (by omega) h.2
          rw [← ENNReal.tsum_prod]
          refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
          refine ENNReal.tsum_le_tsum fun p => ?_
          have hne : (p.1 + 1, p.2) ≠ ((0 : ℕ), i) := by simp
          rw [if_pos hne]
          exact x5bd_PS_mono P _ _ (fun z hz h => by rw [h] at hz; simp at hz) _ _ _
  have hfinT : ∀ i, ∑' t, ENNReal.ofReal (returnTailC P (0, i) (t + 1)) ≠ ⊤ := by
    intro i
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => hnn _ _)
      ((hpos (0, i)).comp_injective (add_left_injective 1))]
    exact ENNReal.ofReal_ne_top
  have hRk : ∀ k i j, matPowE R (k + 1) i j ≠ ⊤ := fun k i j =>
    ne_top_of_le_ne_top (hfinT i) ((ENNReal.le_tsum j).trans ((ENNReal.le_tsum k).trans (htot i)))
  have hR1 : matPowE R 1 = R := x5bd_one_mm R
  have hRfin : ∀ i j, R i j ≠ ⊤ := by
    intro i j; have := hRk 0 i j; rwa [zero_add, hR1] at this
  have hfk : ∀ k i j, matPowE R k i j ≠ ⊤ := by
    intro k i j
    rcases k with _ | k
    · show matOneE i j ≠ ⊤
      unfold matOneE; split_ifs <;> simp
    · exact hRk k i j
  refine ⟨hRfin, ?_⟩
  apply x5bd_sp
  have hMpow : ∀ k i j, ((Matrix.of fun i j => (((R i j).toReal : ℝ) : ℂ)) ^ k) i j =
      (((matPowE R k i j).toReal : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero =>
      intro i j
      show (1 : Matrix ι ι ℂ) i j = (((matOneE i j : ℝ≥0∞).toReal : ℝ) : ℂ)
      unfold matOneE
      rw [Matrix.one_apply]
      split_ifs <;> simp
    | succ k ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih]
      show _ = (((matMulE (matPowE R k) R i j).toReal : ℝ) : ℂ)
      unfold matMulE
      rw [tsum_fintype, ENNReal.toReal_sum (fun l _ => ENNReal.mul_ne_top (hfk k i l) (hRfin l j))]
      push_cast
      simp [ENNReal.toReal_mul]
  intro i j
  simp_rw [hMpow]
  have h2 : Filter.Tendsto (fun k => matPowE R (k + 1) i j) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top (ne_top_of_le_ne_top (hfinT i)
      ((ENNReal.tsum_le_tsum fun k => ENNReal.le_tsum j).trans (htot i)))
  have h3 := (Filter.tendsto_add_atTop_iff_nat (f := fun k => matPowE R k i j) 1).mp h2
  have h4 := (Complex.continuous_ofReal.tendsto _).comp
    ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3)
  simpa [Function.comp_def] using h4

-- ===== Ugr =====

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric


section UGRgen
variable {V : Type*} (P : V → V → ℝ)

lemma x5bd_PS_congr (I A A' : V → Prop) (y : V)
    (hstep : ∀ w z, I w → P w z ≠ 0 → (A z ↔ A' z) ∧ (A z → I z)) :
    ∀ L x, I x → x5bd_PS P x L y A = x5bd_PS P x L y A' := by
  classical
  intro L
  induction L with
  | zero => intro x _; rw [x5bd_PS_zero, x5bd_PS_zero]
  | succ L ih =>
    intro x hx
    rw [x5bd_PS_cons P x L y A, x5bd_PS_cons P x L y A']
    refine tsum_congr fun z => ?_
    by_cases hP0 : P x z = 0
    · simp [hP0]
    obtain ⟨hiff, hI⟩ := hstep x z hx hP0
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp only [true_or, if_true, x5bd_PS_zero]
    · by_cases hz : A z
      · rw [if_pos (Or.inr hz), if_pos (Or.inr (hiff.mp hz)), ih z (hI hz)]
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hz h]),
          if_neg (by rintro (h | h) <;> [omega; exact hz (hiff.mpr h)])]

lemma x5bd_partial (a b : ℕ → ℝ≥0∞) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) ≤
      (∑ s ∈ Finset.range T, a s) * ∑' u, b u := by
  classical
  set a' : ℕ → ℝ≥0∞ := fun s => if s < T then a s else 0 with ha'
  have e1 : ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) =
      ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a' s * b (t - s) := by
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun s hs => ?_
    have : s < T := by
      have := Finset.mem_range.mp ht; have := Finset.mem_range.mp hs; omega
    simp [ha', this]
  have e2 : ∑' s, a' s = ∑ s ∈ Finset.range T, a s := by
    rw [tsum_eq_sum (s := Finset.range T)]
    · exact Finset.sum_congr rfl fun s hs => by simp [ha', Finset.mem_range.mp hs]
    · intro s hs; simp [ha', Finset.mem_range.not.mp hs]
  rw [e1, ← e2, ← x5bd_cauchy0]
  exact ENNReal.sum_le_tsum _

lemma x5bd_swapT {W : Type*} (mid : W → Prop) [DecidablePred mid] (a : W → ℕ → ℝ≥0∞)
    (b : W → ℕ → ℝ≥0∞) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) ≤
      ∑' z, if mid z then (∑ s ∈ Finset.range T, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact x5bd_partial (a z) (b z) T
  · simp [hz]

lemma x5bd_seriesInv {ι : Type*} [Countable ι] [DecidableEq ι] (U N : ι → ι → ℝ≥0∞)
    (f : ι → ι → ℕ → ℝ≥0∞) (hNf : ∀ i j, N i j = ∑' t, f i j t)
    (hNeq : ∀ i j, N i j = matOneE i j + ∑' l, N i l * U l j)
    (hpart : ∀ T i j, ∑ t ∈ Finset.range (T + 1), f i j t ≤
      matOneE i j + ∑' l, (∑ t ∈ Finset.range T, f i l t) * U l j) :
    N = seriesInvE U := by
  have hS : ∀ i j, seriesInvE U i j = matOneE i j + ∑' l, seriesInvE U i l * U l j := by
    intro i j
    unfold seriesInvE
    rw [tsum_eq_zero_add' ENNReal.summable]
    congr 1
    show ∑' ν, matMulE (matPowE U ν) U i j = _
    unfold matMulE
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right]
  have h1 : ∀ T i j, ∑ t ∈ Finset.range T, f i j t ≤ seriesInvE U i j := by
    intro T
    induction T with
    | zero => intro i j; simp
    | succ T ih =>
      intro i j
      refine (hpart T i j).trans ?_
      rw [hS i j]
      gcongr with l
      exact ih i l
  have h2 : ∀ K i j, ∑ ν ∈ Finset.range K, matPowE U ν i j ≤ N i j := by
    intro K
    induction K with
    | zero => intro i j; simp
    | succ K ih =>
      intro i j
      rw [Finset.sum_range_succ', hNeq i j, add_comm]
      gcongr
      · exact le_of_eq rfl
      · show ∑ ν ∈ Finset.range K, ∑' l, matPowE U ν i l * U l j ≤ _
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine ENNReal.tsum_le_tsum fun l => ?_
        rw [← Finset.sum_mul]
        gcongr
        exact ih i l
  funext i j
  refine le_antisymm ?_ ?_
  · rw [hNf i j, ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun T => h1 T i j
  · unfold seriesInvE
    rw [ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun K => h2 K i j
end UGRgen

section UGRq
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma x5bd_fe (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) (hy : y ∈ T) :
    firstEntrance P T x y = ∑' t, x5bd_PS P x (t + 1) y (fun z => z ∉ T) := by
  classical
  unfold firstEntrance x5bd_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
      ∀ m : Fin (t + 1 + 1), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · rw [if_pos ⟨h.1, h.2.1, hy, h.2.2⟩, if_pos h]; rfl
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg h]
end UGRq

theorem x5bd_ugr {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (n : ℕ) (hn : 1 ≤ n) :
    matR (qbdP B A₀ A₁ A₂) n =
        matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂) n)) ∧
      matG (qbdP B A₀ A₁ A₂) n =
        matMulE (seriesInvE (matU (qbdP B A₀ A₁ A₂) n)) (ennMat A₂) ∧
      matU (qbdP B A₀ A₁ A₂) n = ennMat A₁ + matMulE (ennMat A₀) (matG (qbdP B A₀ A₁ A₂) n) ∧
      matU (qbdP B A₀ A₁ A₂) n = ennMat A₁ + matMulE (matR (qbdP B A₀ A₁ A₂) n) (ennMat A₂) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hsub : m + 1 - 1 = m := by omega
  have hqnz : ∀ x w : ℕ × ι, P x w ≠ 0 → w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 :=
    fun x w h => x5bd_qnz B A₀ A₁ A₂ x w h
  have hU : ∀ i j, matU P (m + 1) i j =
      ∑' t, x5bd_PS P (m + 1, i) (t + 1) (m + 1, j) (fun z => m + 1 < z.1) := by
    intro i j
    show firstEntrance P (level (m + 1) ∪ level (m + 1 - 1)) (m + 1, i) (m + 1, j) = _
    rw [hsub, x5bd_fe P _ _ _ (by simp [level])]
    refine tsum_congr fun t => x5bd_PS_congr P (fun z => m + 1 ≤ z.1) _ _ _ ?_ _ _ le_rfl
    intro w z hw hz
    have := hqnz w z hz
    simp only [level, Set.mem_union, Set.mem_setOf_eq] at hw ⊢
    refine ⟨⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩
  have hG : ∀ i j, matG P (m + 1) i j =
      ∑' t, x5bd_PS P (m + 1, i) (t + 1) (m, j) (fun z => m < z.1) := by
    intro i j
    show firstEntrance P (level (m + 1 - 1)) (m + 1, i) (m + 1 - 1, j) = _
    rw [hsub, x5bd_fe P _ _ _ (by simp [level])]
    refine tsum_congr fun t => x5bd_PS_congr P (fun z => m < z.1) _ _ _ ?_ _ _ (by simp)
    intro w z hw hz
    have := hqnz w z hz
    simp only [level, Set.mem_setOf_eq] at hw ⊢
    refine ⟨⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩
  set N : ι → ι → ℝ≥0∞ := fun i j =>
    ∑' t, x5bd_PS P (m + 1, i) t (m + 1, j) (fun z => m < z.1) with hNd
  have hst : ∀ w y : ℕ × ι, (fun z : ℕ × ι => m ≤ z.1) y → P w y ≠ 0 →
      ((fun z : ℕ × ι => z.1 = m + 1) w ∧ (fun z : ℕ × ι => m < z.1) w ∧
          ¬ (fun z : ℕ × ι => m + 1 < z.1) w) ∨
      ((fun z : ℕ × ι => m + 1 < z.1) w ∧ (fun z : ℕ × ι => m < z.1) w ∧
          (fun z : ℕ × ι => m ≤ z.1) w ∧ ¬ (fun z : ℕ × ι => z.1 = m + 1) w) ∨
      (¬ (fun z : ℕ × ι => m < z.1) w ∧ ¬ (fun z : ℕ × ι => m + 1 < z.1) w ∧
          ¬ (fun z : ℕ × ι => z.1 = m + 1) w) := by
    intro w y _ _
    simp only
    omega
  -- G = N A₂
  have hb : ∀ (l j : ι) (u : ℕ), x5bd_PS P (m + 1, l) (u + 1) (m, j) (fun z => m + 1 < z.1) =
      if u = 0 then ENNReal.ofReal (A₂ l j) else 0 := by
    intro l j u
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; rw [x5bd_PS_one, if_pos rfl]; simp [hPd, qbdP, show m ≠ m + 1 + 1 by omega]
    · rw [if_neg (by omega), x5bd_PS_snoc]
      refine ENNReal.tsum_eq_zero.mpr fun w => ?_
      by_cases hw : m + 1 < w.1
      · have : P w (m, j) = 0 := by
          by_contra h; have := hqnz w (m, j) h; simp at this; omega
        simp [this]
      · rw [if_neg (by omega)]; simp
  have hGN : matG P (m + 1) = matMulE N (ennMat A₂) := by
    funext i j
    rw [hG i j]
    rw [tsum_congr fun t => x5bd_conv3 P (fun z : ℕ × ι => m ≤ z.1) (fun z : ℕ × ι => z.1 = m + 1)
      (fun z : ℕ × ι => m < z.1) (fun z : ℕ × ι => m + 1 < z.1) (m + 1, i) rfl hst t (m, j) le_rfl]
    have e : ∀ t, ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = m + 1 then
        x5bd_PS P (m + 1, i) s z (fun z => m < z.1) *
          x5bd_PS P z (t + 1 - s) (m, j) (fun z => m + 1 < z.1) else 0) =
        ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = m + 1 then
        x5bd_PS P (m + 1, i) s z (fun z => m < z.1) *
          (fun z u => x5bd_PS P z (u + 1) (m, j) (fun z => m + 1 < z.1)) z (t - s) else 0) := by
      intro t
      refine Finset.sum_congr rfl fun s hs => ?_
      have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [show t + 1 - s = t - s + 1 by omega]
    rw [tsum_congr e, x5bd_swap0 (fun z : ℕ × ι => z.1 = m + 1)
      (fun z s => x5bd_PS P (m + 1, i) s z (fun z => m < z.1))
      (fun z u => x5bd_PS P z (u + 1) (m, j) (fun z => m + 1 < z.1)), x5bd_levn]
    unfold matMulE ennMat
    refine tsum_congr fun l => ?_
    simp only [hb]
    rw [tsum_eq_single 0 (fun u hu => if_neg hu), if_pos rfl]
  -- N equation
  have hyz : ∀ i j, x5bd_PS P (m + 1, i) 0 (m + 1, j) (fun z => m < z.1) = matOneE i j := by
    intro i j; rw [x5bd_PS_zero]; simp [matOneE]
  have hconvN : ∀ i j t, x5bd_PS P (m + 1, i) (t + 1) (m + 1, j) (fun z => m < z.1) =
      ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = m + 1 then
        x5bd_PS P (m + 1, i) s z (fun z => m < z.1) *
          (fun z u => x5bd_PS P z (u + 1) (m + 1, j) (fun z => m + 1 < z.1)) z (t - s) else 0) := by
    intro i j t
    rw [x5bd_conv3 P (fun z : ℕ × ι => m ≤ z.1) (fun z : ℕ × ι => z.1 = m + 1)
      (fun z : ℕ × ι => m < z.1) (fun z : ℕ × ι => m + 1 < z.1) (m + 1, i) rfl hst t (m + 1, j)
      (Nat.le_succ m)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show t + 1 - s = t - s + 1 by omega]
  have hNeq : ∀ i j, N i j = matOneE i j + ∑' l, N i l * matU P (m + 1) l j := by
    intro i j
    show ∑' t, x5bd_PS P (m + 1, i) t (m + 1, j) (fun z => m < z.1) = _
    rw [tsum_eq_zero_add' ENNReal.summable, hyz]
    congr 1
    rw [tsum_congr (hconvN i j), x5bd_swap0 (fun z : ℕ × ι => z.1 = m + 1)
      (fun z s => x5bd_PS P (m + 1, i) s z (fun z => m < z.1))
      (fun z u => x5bd_PS P z (u + 1) (m + 1, j) (fun z => m + 1 < z.1)), x5bd_levn]
    refine tsum_congr fun l => ?_
    rw [hU l j]
  have hpart : ∀ T i j, ∑ t ∈ Finset.range (T + 1),
      x5bd_PS P (m + 1, i) t (m + 1, j) (fun z => m < z.1) ≤
      matOneE i j + ∑' l, (∑ t ∈ Finset.range T,
        x5bd_PS P (m + 1, i) t (m + 1, l) (fun z => m < z.1)) * matU P (m + 1) l j := by
    intro T i j
    rw [Finset.sum_range_succ', hyz, add_comm (∑ t ∈ Finset.range T, _)]
    gcongr
    rw [Finset.sum_congr rfl fun t _ => hconvN i j t]
    refine (x5bd_swapT (fun z : ℕ × ι => z.1 = m + 1)
      (fun z s => x5bd_PS P (m + 1, i) s z (fun z => m < z.1))
      (fun z u => x5bd_PS P z (u + 1) (m + 1, j) (fun z => m + 1 < z.1)) T).trans (le_of_eq ?_)
    rw [x5bd_levn]
    refine tsum_congr fun l => ?_
    rw [hU l j]
  have hNS : N = seriesInvE (matU P (m + 1)) :=
    x5bd_seriesInv _ N (fun i j t => x5bd_PS P (m + 1, i) t (m + 1, j) (fun z => m < z.1))
      (fun i j => rfl) hNeq hpart
  -- R = A₀ N
  have hRN : matR P (m + 1) = matMulE (ennMat A₀) N := by
    funext i j
    show expVisitsAvoid P (levelsUpTo (m + 1)) (m + 1, i) (m + 1 + 1, j) = _
    rw [x5bd_eva B A₀ A₁ A₂ (m + 1) _ _ (by simp), tsum_eq_zero_add' ENNReal.summable,
      x5bd_PS_zero, if_neg (by simp), zero_add, ← hPd]
    simp_rw [x5bd_PS_cons P (m + 1, i)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    have key : ∀ z : ℕ × ι, ENNReal.ofReal (P (m + 1, i) z) * ∑' t, (if t = 0 ∨ m + 1 < z.1 then
        x5bd_PS P z t (m + 1 + 1, j) (fun z => m + 1 < z.1) else 0) =
        if z.1 = m + 1 + 1 then ENNReal.ofReal (A₀ i z.2) * N z.2 j else 0 := by
      intro z
      obtain ⟨k, l⟩ := z
      by_cases hz : k = m + 1 + 1
      · subst hz
        rw [if_pos rfl]
        have hP' : P (m + 1, i) (m + 1 + 1, l) = A₀ i l := by simp [hPd, qbdP]
        rw [hP']
        congr 1
        show _ = ∑' t, x5bd_PS P (m + 1, l) t (m + 1, j) (fun z => m < z.1)
        refine tsum_congr fun t => ?_
        rw [if_pos (Or.inr (by simp))]
        exact x5bd_PS_shiftN B A₀ A₁ A₂ m (m + 1) (m + 1) l j (by omega) t
      · rw [if_neg hz]
        by_cases hle : k ≤ m + 1
        · rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
          intro t
          rcases Nat.eq_zero_or_pos t with ht | ht
          · subst ht
            rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
            intro h; simp only [Prod.mk.injEq] at h; omega
          · rw [if_neg (by simp only; omega)]
        · have : P (m + 1, i) (k, l) = 0 := by
            by_contra h; have := hqnz _ _ h; simp only at this; omega
          simp [this]
    rw [tsum_congr key, x5bd_levn]
    rfl
  -- U = A₁ + A₀ G
  have hUAG : matU P (m + 1) = ennMat A₁ + matMulE (ennMat A₀) (matG P (m + 1)) := by
    funext i j
    rw [hU i j]
    simp_rw [x5bd_PS_cons P (m + 1, i)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    have key : ∀ z : ℕ × ι, ENNReal.ofReal (P (m + 1, i) z) * ∑' t, (if t = 0 ∨ m + 1 < z.1 then
        x5bd_PS P z t (m + 1, j) (fun z => m + 1 < z.1) else 0) =
        (if z.1 = m + 1 then ENNReal.ofReal (A₁ i z.2) * (if z.2 = j then 1 else 0) else 0) +
        (if z.1 = m + 1 + 1 then ENNReal.ofReal (A₀ i z.2) * matG P (m + 1) z.2 j else 0) := by
      intro z
      obtain ⟨k, l⟩ := z
      simp only
      by_cases h1 : k = m + 1
      · subst h1
        have c1 : ¬ (m + 1 = m + 1 + 1) := by omega
        have hP' : P (m + 1, i) (m + 1, l) = A₁ i l := by simp [hPd, qbdP]
        simp only [c1, eq_self_iff_true, if_true, if_false, add_zero, lt_irrefl, or_false, hP']
        rw [tsum_eq_single 0 (fun t ht => if_neg ht), if_pos rfl, x5bd_PS_zero]
        simp
      by_cases h2 : k = m + 1 + 1
      · subst h2
        have c1 : ¬ (m + 1 + 1 = m + 1) := by omega
        have hP' : P (m + 1, i) (m + 1 + 1, l) = A₀ i l := by simp [hPd, qbdP]
        simp only [c1, eq_self_iff_true, if_true, if_false, zero_add, hP']
        rw [hG l j]
        congr 1
        rw [tsum_eq_zero_add' ENNReal.summable, if_pos (Or.inl rfl), x5bd_PS_zero,
          if_neg (by simp), zero_add]
        refine tsum_congr fun t => ?_
        rw [if_pos (Or.inr (by omega))]
        exact x5bd_PS_shiftN B A₀ A₁ A₂ m (m + 1) m l j (by omega) (t + 1)
      · rw [if_neg h1, if_neg h2, add_zero]
        by_cases hle : k ≤ m
        · rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
          intro t
          rcases Nat.eq_zero_or_pos t with ht | ht
          · subst ht
            rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
            intro h; simp only [Prod.mk.injEq] at h; omega
          · rw [if_neg (by omega)]
        · have : P (m + 1, i) (k, l) = 0 := by
            by_contra h; have := hqnz _ _ h; simp only at this; omega
          simp [this]
    rw [tsum_congr key, ENNReal.tsum_add, x5bd_levn, x5bd_levn]
    simp only [Pi.add_apply, ennMat, matMulE]
    congr 1
    simp
  refine ⟨?_, ?_, hUAG, ?_⟩
  · rw [hRN, hNS]
  · rw [hGN, hNS]
  · rw [hUAG, hGN, hRN, x5bd_mm_assoc]

section MMalg
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma x5bd_mm_add_left (X Y Z : ι → ι → ℝ≥0∞) :
    matMulE (X + Y) Z = matMulE X Z + matMulE Y Z := by
  funext i j
  simp only [matMulE, Pi.add_apply, add_mul, ENNReal.tsum_add]

lemma x5bd_mm_add_right (X Y Z : ι → ι → ℝ≥0∞) :
    matMulE X (Y + Z) = matMulE X Y + matMulE X Z := by
  funext i j
  simp only [matMulE, Pi.add_apply, mul_add, ENNReal.tsum_add]


lemma x5bd_S_right (U : ι → ι → ℝ≥0∞) :
    seriesInvE U = matOneE + matMulE (seriesInvE U) U := by
  funext i j
  unfold seriesInvE
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Pi.add_apply]
  congr 1
  show ∑' ν, matMulE (matPowE U ν) U i j = _
  unfold matMulE
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right]

lemma x5bd_S_left (U : ι → ι → ℝ≥0∞) :
    seriesInvE U = matOneE + matMulE U (seriesInvE U) := by
  funext i j
  unfold seriesInvE
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Pi.add_apply]
  congr 1
  simp_rw [← x5bd_pow_succ']
  unfold matMulE
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
end MMalg

theorem x5bd_quad {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (n : ℕ) (hn : 1 ≤ n) :
    matU (qbdP B A₀ A₁ A₂) n =
        ennMat A₁ + matMulE (matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂) n)))
          (ennMat A₂) ∧
      matG (qbdP B A₀ A₁ A₂) n =
        ennMat A₂ + matMulE (ennMat A₁) (matG (qbdP B A₀ A₁ A₂) n) +
          matMulE (ennMat A₀)
            (matMulE (matG (qbdP B A₀ A₁ A₂) n) (matG (qbdP B A₀ A₁ A₂) n)) ∧
      matR (qbdP B A₀ A₁ A₂) n =
        ennMat A₀ + matMulE (matR (qbdP B A₀ A₁ A₂) n) (ennMat A₁) +
          matMulE (matMulE (matR (qbdP B A₀ A₁ A₂) n) (matR (qbdP B A₀ A₁ A₂) n))
            (ennMat A₂) := by
  obtain ⟨hR, hG, hU1, hU2⟩ := x5bd_ugr B A₀ A₁ A₂ hP hirr hpos n hn
  set U := matU (qbdP B A₀ A₁ A₂) n
  set S := seriesInvE U
  set G := matG (qbdP B A₀ A₁ A₂) n
  set R := matR (qbdP B A₀ A₁ A₂) n
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [hU1, hG]
    rw [x5bd_mm_assoc]
  · have h1 : G = ennMat A₂ + matMulE U G := by
      conv_lhs => rw [hG, show S = seriesInvE U from rfl, x5bd_S_left]
      rw [x5bd_mm_add_left, x5bd_one_mm, x5bd_mm_assoc, ← hG]
    conv_lhs => rw [h1]
    rw [hU1, x5bd_mm_add_left, x5bd_mm_assoc, add_assoc]
  · have h1 : R = ennMat A₀ + matMulE R U := by
      conv_lhs => rw [hR, show S = seriesInvE U from rfl, x5bd_S_right]
      rw [x5bd_mm_add_right, x5bd_mm_one, ← x5bd_mm_assoc, ← hR]
    conv_lhs => rw [h1]
    rw [hU2, x5bd_mm_add_right, ← x5bd_mm_assoc, add_assoc]

-- ===== Gen =====

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric
open Filter Topology

section BDGen
variable {V : Type*} (P : V → V → ℝ)

lemma x5bd_AV_zero (x : V) (A : V → Prop) : x5bd_AV P x A 0 = 1 := by
  classical
  unfold x5bd_AV
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  rw [tsum_eq_single x]
  · simp [x5bd_W]
  · intro b hb; simp [hb]

lemma x5bd_AV_anti (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5bd_AV P x A (t + 1) ≤ x5bd_AV P x A t := by
  rw [← x5bd_step P hrow x A t]; exact le_self_add

lemma x5bd_PS_le_AV (x y : V) (A : V → Prop) (hy : A y) (t : ℕ) :
    x5bd_PS P x t y A ≤ x5bd_AV P x A t := by
  classical
  unfold x5bd_PS x5bd_AV
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → A (ω m)
  · rw [if_pos h, if_pos]
    refine ⟨h.1, fun i hi => ?_⟩
    by_cases hl : i = Fin.last t
    · rw [hl, h.2.1]; exact hy
    · exact h.2.2 i hi hl
  · rw [if_neg h]; exact bot_le

lemma x5bd_AV_concat (A : V → Prop) (x z : V) (hz : A z) (u t : ℕ) :
    x5bd_PS P x u z A * x5bd_AV P z A t ≤ x5bd_AV P x A (u + t) := by
  classical
  rcases t with _ | s
  · rw [x5bd_AV_zero, mul_one, add_zero]; exact x5bd_PS_le_AV P x z A hz u
  · rw [x5bd_AV_eq P z A s, show u + (s + 1) = (u + s) + 1 by omega, x5bd_AV_eq P x A (u + s),
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    split_ifs with hy
    · have := x5bd_PS_concat P A z y hz u x (s + 1)
      rwa [show u + (s + 1) = u + s + 1 by omega] at this
    · simp

lemma x5bd_stepPow_nonneg [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y; simp only [stepPow]
    exact tsum_nonneg fun z => mul_nonneg (ih x z) (hP0 z y)

lemma x5bd_stepPow_PS [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 < stepPow P t x y → x5bd_PS P x t y (fun _ => True) ≠ 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro x y h
    simp only [stepPow] at h
    rw [x5bd_PS_zero]
    split_ifs at h with hyx
    · rw [if_pos hyx.symm]; exact one_ne_zero
    · exact absurd h (lt_irrefl 0)
  | succ t ih =>
    intro x y h
    simp only [stepPow] at h
    obtain ⟨z, hz⟩ : ∃ z, 0 < stepPow P t x z * P z y := by
      by_contra hc
      push_neg at hc
      have : ∀ z, stepPow P t x z * P z y = 0 := fun z =>
        le_antisymm (hc z) (mul_nonneg (x5bd_stepPow_nonneg P hP0 t x z) (hP0 z y))
      simp [this] at h
    have ha := x5bd_stepPow_nonneg P hP0 t x z
    have h1 : 0 < stepPow P t x z :=
      lt_of_le_of_ne ha (fun h0 => by rw [← h0, zero_mul] at hz; exact lt_irrefl 0 hz)
    have h2 : 0 < P z y :=
      lt_of_le_of_ne (hP0 z y) (fun h0 => by rw [← h0, mul_zero] at hz; exact lt_irrefl 0 hz)
    rw [x5bd_PS_snoc P x t y (fun _ => True)]
    intro h0
    have := (ENNReal.tsum_eq_zero.mp h0) z
    rw [if_pos (Or.inr trivial)] at this
    rcases mul_eq_zero.mp this with h3 | h3
    · exact ih x z h1 h3
    · exact absurd h3 (by simpa using h2)

lemma x5bd_AV_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5bd_AV P x A t ≤ 1 :=
  le_self_add.trans_eq (x5bd_mass P hrow x A t)

lemma x5bd_recur (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V)
    (hret : Tendsto (fun t => x5bd_AV P x0 (fun z => z ≠ x0) t) atTop (𝓝 0))
    (hreach : ∀ z, z ≠ x0 → ∃ u, x5bd_PS P x0 u z (fun z => z ≠ x0) ≠ 0) :
    ∀ z, Tendsto (fun t => x5bd_AV P z (fun w => w ≠ x0) t) atTop (𝓝 0) := by
  intro z
  by_cases hz : z = x0
  · subst hz; exact hret
  obtain ⟨u, hu⟩ := hreach z hz
  set c := x5bd_PS P x0 u z (fun z => z ≠ x0) with hc
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((x5bd_PS_le_AV P x0 z _ hz u).trans (x5bd_AV_le_one P hrow x0 _ u))
  have hb : ∀ t, x5bd_AV P z (fun w => w ≠ x0) t ≤ c⁻¹ * x5bd_AV P x0 (fun w => w ≠ x0) (t + u) := by
    intro t
    have h1 := x5bd_AV_concat P (fun w => w ≠ x0) x0 z hz u t
    rw [add_comm u t] at h1
    calc x5bd_AV P z (fun w => w ≠ x0) t = c⁻¹ * (c * x5bd_AV P z (fun w => w ≠ x0) t) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hu hctop, one_mul]
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun t => c⁻¹ * x5bd_AV P x0 (fun w => w ≠ x0) (t + u)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ((Filter.tendsto_add_atTop_iff_nat u).mpr hret)
      (Or.inr (ENNReal.inv_ne_top.mpr hu))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => bot_le) hb

/-- The taboo identity: an invariant measure of finite mass is determined on `A` by its values
off `A`, provided the chain leaves `A` almost surely from every state of `A`. -/
theorem x5bd_taboo (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (ν : V → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (A : V → Prop) [DecidablePred A]
    (hAV : ∀ z, A z → Tendsto (fun t => x5bd_AV P z A t) atTop (𝓝 0)) :
    ∀ y, A y → ν y = ∑' x, if A x then 0 else ν x * ∑' t, x5bd_PS P x (t + 1) y A := by
  classical
  intro y hy
  set a : ℕ → ℝ≥0∞ := fun t => ∑' x, if A x then 0 else ν x * x5bd_PS P x (t + 1) y A with ha
  set r : ℕ → ℝ≥0∞ := fun t => ∑' z, if A z then ν z * x5bd_PS P z t y A else 0 with hr
  have hcons : ∀ t x, x5bd_PS P x (t + 1) y A =
      ∑' z, if A z then ENNReal.ofReal (P x z) * x5bd_PS P z t y A else 0 := by
    intro t x
    rw [x5bd_PS_cons P x t y A]
    refine tsum_congr fun z => ?_
    by_cases hAz : A z
    · rw [if_pos (Or.inr hAz), if_pos hAz]
    · rw [if_neg hAz]
      by_cases ht : t = 0
      · subst ht
        rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg (fun (h : z = y) => hAz (h ▸ hy)), mul_zero]
      · rw [if_neg (by tauto), mul_zero]
  have hstep : ∀ t, r t = a t + r (t + 1) := by
    intro t
    have e1 : r t = ∑' x, ν x * x5bd_PS P x (t + 1) y A := by
      simp only [hr, hcons]
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun z => ?_
      by_cases hAz : A z
      · simp only [if_pos hAz]
        rw [← hinv z, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun x => ?_
        ring
      · simp [hAz]
    rw [e1, ha, hr, ← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    by_cases hAx : A x <;> simp [hAx]
  have hr0 : r 0 = ν y := by
    simp only [hr]
    rw [tsum_eq_single y]
    · rw [if_pos hy, x5bd_PS_zero, if_pos rfl, mul_one]
    · intro z hz; rw [x5bd_PS_zero, if_neg hz]; simp
  have hsum : ∀ t, ν y = ∑ s ∈ Finset.range t, a s + r t := by
    intro t
    induction t with
    | zero => simp [hr0]
    | succ t ih => rw [ih, hstep t, Finset.sum_range_succ, add_assoc]
  -- the remainder tends to zero (dominated convergence for the counting measure)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    letI : MeasurableSpace V := ⊤
    have hdc := MeasureTheory.tendsto_lintegral_of_dominated_convergence (μ := MeasureTheory.Measure.count)
      (F := fun t z => if A z then ν z * x5bd_AV P z A t else 0) (f := fun _ => 0) ν
      (fun t => measurable_from_top)
      (fun t => Filter.Eventually.of_forall fun z => by
        by_cases hAz : A z
        · simp only [if_pos hAz]
          calc ν z * x5bd_AV P z A t ≤ ν z * 1 := by gcongr; exact x5bd_AV_le_one P hrow z A t
            _ = ν z := mul_one _
        · simp [hAz])
      (by rw [MeasureTheory.lintegral_count' measurable_from_top]; exact hfin)
      (Filter.Eventually.of_forall fun z => by
        by_cases hAz : A z
        · simp only [if_pos hAz]
          have hνz : ν z ≠ ⊤ := ne_top_of_le_ne_top hfin (ENNReal.le_tsum z)
          simpa using ENNReal.Tendsto.const_mul (hAV z hAz) (Or.inr hνz)
        · simp [hAz])
    rw [MeasureTheory.lintegral_zero] at hdc
    simp_rw [MeasureTheory.lintegral_count' measurable_from_top] at hdc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdc (fun t => bot_le) ?_
    intro t
    simp only [hr]
    refine ENNReal.tsum_le_tsum fun z => ?_
    by_cases hAz : A z
    · simp only [if_pos hAz]; gcongr; exact x5bd_PS_le_AV P z y A hy t
    · simp [hAz]
  have hlim : Tendsto (fun t => ∑ s ∈ Finset.range t, a s + r t) atTop (𝓝 (∑' s, a s + 0)) :=
    (ENNReal.tendsto_nat_tsum a).add hrlim
  have hconst : Tendsto (fun t => ∑ s ∈ Finset.range t, a s + r t) atTop (𝓝 (ν y)) := by
    simp_rw [← hsum]; exact tendsto_const_nhds
  rw [tendsto_nhds_unique hconst hlim, add_zero, ha]
  dsimp only
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  by_cases hAx : A x
  · simp [hAx]
  · simp only [if_neg hAx]; rw [ENNReal.tsum_mul_left]

end BDGen

-- ===== Q =====

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric
open Filter Topology

section BDGen2
variable {V : Type*} (P : V → V → ℝ)

lemma x5bd_AV_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x : V) (t : ℕ) :
    x5bd_AV P x A t ≤ x5bd_AV P x A' t := by
  classical
  unfold x5bd_AV
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos h, if_pos ⟨h.1, fun i hi => hAA _ (h.2 i hi)⟩]
  · rw [if_neg h]; exact bot_le

end BDGen2

section BDQ
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

omit [Countable ι] [DecidableEq ι] in
lemma x5bd_qshift2 (c d : ℕ) (i j : ι) (hd : 1 ≤ d) :
    qbdP B A₀ A₁ A₂ (c + 1, i) (d + 1, j) = qbdP B A₀ A₁ A₂ (c, i) (d, j) := by
  unfold qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

omit [Countable ι] [DecidableEq ι] in
lemma x5bd_qto (l k : ℕ) (i j : ι) :
    qbdP B A₀ A₁ A₂ (l, i) (k + 1, j) =
      if l = k then A₀ i j else if l = k + 1 then A₁ i j else if l = k + 2 then A₂ i j else 0 := by
  unfold qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

omit [Countable ι] [DecidableEq ι] in
lemma x5bd_qto0 (l : ℕ) (i j : ι) :
    qbdP B A₀ A₁ A₂ (l, i) (0, j) = if l = 0 then B i j else if l = 1 then A₂ i j else 0 := by
  unfold qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

lemma x5bd_PS_shift2 (n a b : ℕ) (i j : ι) (hb : 1 ≤ b) (L : ℕ) :
    x5bd_PS (qbdP B A₀ A₁ A₂) (a + 1, i) L (b + 1, j) (fun z => n + 1 < z.1) =
      x5bd_PS (qbdP B A₀ A₁ A₂) (a, i) L (b, j) (fun z => n < z.1) := by
  classical
  unfold x5bd_PS
  rw [← x5bd_sh_inj.tsum_eq]
  · refine tsum_congr fun ω => ?_
    have hc : ((x5bd_sh ω) 0 = (a + 1, i) ∧ (x5bd_sh ω) (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < ((x5bd_sh ω) m).1) ↔
        (ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1) := by
      simp only [x5bd_sh, Prod.ext_iff, add_left_inj, Nat.add_lt_add_iff_right]
    by_cases h : ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1
    · rw [if_pos (hc.mpr h), if_pos h]
      unfold x5bd_W
      refine Finset.prod_congr rfl fun s _ => ?_
      have hl : 1 ≤ (ω s.succ).1 := by
        by_cases hs : s.succ = Fin.last L
        · rw [hs, h.2.1]; exact hb
        · have := h.2.2 s.succ (Fin.succ_ne_zero s) hs; omega
      simp only [x5bd_sh]
      rw [x5bd_qshift2 B A₀ A₁ A₂ _ _ _ _ hl]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
  · intro ω hω
    rw [Function.mem_support] at hω
    have hcond : ω 0 = (a + 1, i) ∧ ω (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < (ω m).1 := by
      by_contra hn; exact hω (if_neg hn)
    refine ⟨fun s => ((ω s).1 - 1, (ω s).2), funext fun s => ?_⟩
    have : 1 ≤ (ω s).1 := by
      by_cases h0 : s = 0
      · rw [h0, hcond.1]; omega
      by_cases hl : s = Fin.last L
      · rw [hl, hcond.2.1]; omega
      have := hcond.2.2 s h0 hl; omega
    simp only [x5bd_sh]
    exact Prod.ext (by simp; omega) rfl

lemma x5bd_Rshift (n : ℕ) : matR (qbdP B A₀ A₁ A₂) (n + 1) = matR (qbdP B A₀ A₁ A₂) n := by
  funext i j
  unfold matR
  rw [x5bd_eva B A₀ A₁ A₂ (n + 1) _ _ (by simp), x5bd_eva B A₀ A₁ A₂ n _ _ (by simp)]
  refine tsum_congr fun t => ?_
  exact x5bd_PS_shift2 B A₀ A₁ A₂ n n (n + 1) i j (by omega) t

lemma x5bd_R_eq (k : ℕ) : matR (qbdP B A₀ A₁ A₂) k = matR (qbdP B A₀ A₁ A₂) 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [x5bd_Rshift, ih]

lemma x5bd_bal0 (ν : ℕ × ι → ℝ≥0∞) (j : ι) :
    ∑' x, ν x * ENNReal.ofReal (qbdP B A₀ A₁ A₂ x (0, j)) =
      ∑' i, ν (0, i) * ENNReal.ofReal (B i j) + ∑' i, ν (1, i) * ENNReal.ofReal (A₂ i j) := by
  rw [ENNReal.tsum_prod']
  have : ∀ l, ∑' i, ν (l, i) * ENNReal.ofReal (qbdP B A₀ A₁ A₂ (l, i) (0, j)) =
      (if l = 0 then ∑' i, ν (0, i) * ENNReal.ofReal (B i j) else 0) +
      (if l = 1 then ∑' i, ν (1, i) * ENNReal.ofReal (A₂ i j) else 0) := by
    intro l
    simp only [x5bd_qto0]
    by_cases h0 : l = 0
    · subst h0; simp
    by_cases h1 : l = 1
    · subst h1; simp
    · simp [h0, h1]
  simp_rw [this]
  rw [ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq]

lemma x5bd_balk (ν : ℕ × ι → ℝ≥0∞) (k : ℕ) (j : ι) :
    ∑' x, ν x * ENNReal.ofReal (qbdP B A₀ A₁ A₂ x (k + 1, j)) =
      ∑' i, ν (k, i) * ENNReal.ofReal (A₀ i j) + ∑' i, ν (k + 1, i) * ENNReal.ofReal (A₁ i j) +
        ∑' i, ν (k + 2, i) * ENNReal.ofReal (A₂ i j) := by
  rw [ENNReal.tsum_prod']
  have : ∀ l, ∑' i, ν (l, i) * ENNReal.ofReal (qbdP B A₀ A₁ A₂ (l, i) (k + 1, j)) =
      (if l = k then ∑' i, ν (k, i) * ENNReal.ofReal (A₀ i j) else 0) +
      (if l = k + 1 then ∑' i, ν (k + 1, i) * ENNReal.ofReal (A₁ i j) else 0) +
      (if l = k + 2 then ∑' i, ν (k + 2, i) * ENNReal.ofReal (A₂ i j) else 0) := by
    intro l
    simp only [x5bd_qto]
    by_cases h0 : l = k
    · subst h0; simp
    by_cases h1 : l = k + 1
    · subst h1; simp
    by_cases h2 : l = k + 2
    · subst h2; simp
    · simp [h0, h1, h2]
  simp_rw [this]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq, tsum_ite_eq]

lemma x5bd_PS_low (k : ℕ) (x : ℕ × ι) (hx : x.1 < k) (j : ι) (t : ℕ) :
    x5bd_PS (qbdP B A₀ A₁ A₂) x (t + 1) (k + 1, j) (fun z => k < z.1) = 0 := by
  classical
  rw [x5bd_PS_cons]
  refine ENNReal.tsum_eq_zero.mpr fun z => ?_
  by_cases hPz : qbdP B A₀ A₁ A₂ x z = 0
  · simp [hPz]
  have := x5bd_qnz B A₀ A₁ A₂ _ _ hPz
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rw [if_pos (Or.inl rfl), x5bd_PS_zero, if_neg]
    · simp
    · intro h; subst h; simp at this; omega
  · rw [if_neg]
    · simp
    · rintro (h | h) <;> omega

end BDQ

-- ===== M1 =====

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric
open Filter Topology

section BDM1
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma x5bd_rowE (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) :
    ∀ z, ∑' y, ENNReal.ofReal (qbdP B A₀ A₁ A₂ z y) = 1 := by
  intro z
  rw [← ENNReal.ofReal_tsum_of_nonneg (hP.1 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
    ENNReal.ofReal_one]

lemma x5bd_AVlim (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) :
    ∀ x0 z, Tendsto (fun t => x5bd_AV (qbdP B A₀ A₁ A₂) z (fun w => w ≠ x0) t) atTop (𝓝 0) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow := x5bd_rowE B A₀ A₁ A₂ hP
  rw [← hPd] at hrow
  have hconv : ∀ (x0 : ℕ × ι) T, ENNReal.ofReal (returnTailC P x0 T) =
      x5bd_AV P x0 (fun z => z ≠ x0) T := by
    intro x0 T
    have hAVle : x5bd_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
      le_self_add.trans_eq (x5bd_mass P hrow x0 _ T)
    unfold returnTailC setAvoidTailC
    rw [x5bd_ofReal_tsum]
    · unfold x5bd_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5bd_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
    · intro ω; split_ifs
      · exact Finset.prod_nonneg fun s _ => hP0 _ _
      · exact le_rfl
    · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
      unfold x5bd_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5bd_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
  intro x0
  apply x5bd_recur P hrow x0
  · have h1 : Tendsto (fun t => returnTailC P x0 t) atTop (𝓝 0) := (hpos x0).tendsto_atTop_zero
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simp only [ENNReal.ofReal_zero] at h2
    refine h2.congr fun t => ?_
    simp [Function.comp_def, hconv]
  · intro z hz
    obtain ⟨t, ht⟩ := hirr x0 z
    exact x5bd_taboo_extract P x0 z hz t (x5bd_stepPow_PS P hP0 t x0 z ht)

lemma x5bd_tabooQ (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (ν : ℕ × ι → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (qbdP B A₀ A₁ A₂ x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (A : ℕ × ι → Prop) [DecidablePred A] (x0 : ℕ × ι) (hx0 : ¬ A x0) :
    ∀ y, A y → ν y = ∑' x, if A x then 0 else
      ν x * ∑' t, x5bd_PS (qbdP B A₀ A₁ A₂) x (t + 1) y A := by
  refine x5bd_taboo _ (x5bd_rowE B A₀ A₁ A₂ hP) ν hinv hfin A fun z _ => ?_
  have h := x5bd_AVlim B A₀ A₁ A₂ hP hirr hpos x0 z
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun t => bot_le) fun t => ?_
  exact x5bd_AV_mono _ _ _ (fun w hw (h : w = x0) => hx0 (h ▸ hw)) z t

lemma x5bd_levstep (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (ν : ℕ × ι → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (qbdP B A₀ A₁ A₂ x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (k : ℕ) (j : ι) :
    ν (k + 1, j) = ∑' i, ν (k, i) * matR (qbdP B A₀ A₁ A₂) 0 i j := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  rw [x5bd_tabooQ B A₀ A₁ A₂ hP hirr hpos ν hinv hfin (fun z => k < z.1) (0, j) (by simp)
    (k + 1, j) (by simp), ENNReal.tsum_prod', tsum_eq_single k]
  · refine tsum_congr fun i => ?_
    rw [if_neg (lt_irrefl k), ← x5bd_R_eq B A₀ A₁ A₂ k]
    congr 1
    unfold matR
    rw [x5bd_eva B A₀ A₁ A₂ k _ _ (by simp)]
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
    rw [x5bd_PS_zero, if_neg (by simp [Prod.ext_iff]), zero_add]
  · intro l hl
    refine ENNReal.tsum_eq_zero.mpr fun i => ?_
    by_cases hkl : k < l
    · rw [if_pos hkl]
    · rw [if_neg hkl]
      have hlk : l < k := by omega
      simp [x5bd_PS_low B A₀ A₁ A₂ k (l, i) hlk j]

end BDM1

-- ===== M2 =====

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric
open Filter Topology

lemma x5bd_Rsum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (i : ι) :
    ∑' k, ∑' j, matPowE (matR (qbdP B A₀ A₁ A₂) 0) k i j ≠ ⊤ := by
  classical
  have hnb := x5bd_nb B A₀ A₁ A₂ hP hirr hpos 0
  have hR := x5bd_hR B A₀ A₁ A₂ 0
  have hP0' := hP.1
  have hrow' := hP.2
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP0'
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hrow' z).summable, (hrow' z).tsum_eq,
      ENNReal.ofReal_one]
  have hconv : ∀ (x0 : ℕ × ι) T, ENNReal.ofReal (returnTailC P x0 T) =
      x5bd_AV P x0 (fun z => z ≠ x0) T := by
    intro x0 T
    have hAVle : x5bd_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
      le_self_add.trans_eq (x5bd_mass P hrow x0 _ T)
    unfold returnTailC setAvoidTailC
    rw [x5bd_ofReal_tsum]
    · unfold x5bd_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5bd_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
    · intro ω; split_ifs
      · exact Finset.prod_nonneg fun s _ => hP0 _ _
      · exact le_rfl
    · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
      unfold x5bd_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5bd_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
  have hnn : ∀ x0 t, 0 ≤ returnTailC P x0 t := by
    intro x0 t
    unfold returnTailC setAvoidTailC
    refine tsum_nonneg fun ω => ?_
    split_ifs
    · exact Finset.prod_nonneg fun s _ => hP0 _ _
    · exact le_rfl
  set R := matR P 0 with hRd
  have hpow : ∀ k, matPowE R (k + 1) = matMulE (ennMat A₀) (matNblock P 0 (k + 1)) := by
    intro k
    have e := (hnb.2 (k + 1) (by omega)).2
    rw [show k + 1 - 1 = k by omega] at e
    rw [← x5bd_pow_succ']
    nth_rewrite 1 [hR]
    rw [x5bd_mm_assoc, ← e]
  have hent : ∀ k i j, matPowE R (k + 1) i j ≤
      ∑' t, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) := by
    intro k i j
    rw [hpow]
    unfold matMulE ennMat
    have e2 : ∀ l, matNblock P 0 (k + 1) l j =
        ∑' t, x5bd_PS P (1, l) t (k + 1, j) (fun z => 0 < z.1) := fun l => by
      unfold matNblock
      have := x5bd_eva B A₀ A₁ A₂ 0 (0 + 1, l) (0 + (k + 1), j) (by simp)
      simp only [zero_add] at this ⊢
      rw [← hPd] at this
      exact this
    simp_rw [e2, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum fun t => ?_
    rw [x5bd_PS_cons P (0, i) t]
    have hinj : Function.Injective (fun l : ι => ((1 : ℕ), l)) := fun a b h => (Prod.mk.inj h).2
    refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
    refine ENNReal.tsum_le_tsum fun l => ?_
    have hP1 : P (0, i) (1, l) = A₀ i l := by simp [hPd, qbdP]
    simp only [hP1]
    rw [if_pos (Or.inr (by norm_num))]
  have htot : ∀ i, ∑' k, ∑' j, matPowE R (k + 1) i j ≤
      ∑' t, ENNReal.ofReal (returnTailC P (0, i) (t + 1)) := by
    intro i
    calc _ ≤ ∑' k, ∑' j, ∑' t, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) :=
          ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j => hent k i j
      _ = ∑' t, ∑' k, ∑' j, x5bd_PS P (0, i) (t + 1) (k + 1, j) (fun z => 0 < z.1) := by
          conv_lhs => arg 1; ext k; rw [ENNReal.tsum_comm]
          rw [ENNReal.tsum_comm]
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun t => ?_
          rw [hconv, x5bd_AV_eq]
          have hinj : Function.Injective (fun p : ℕ × ι => (p.1 + 1, p.2)) := by
            intro a b h
            simp only [Prod.mk.injEq] at h
            exact Prod.ext (by omega) h.2
          rw [← ENNReal.tsum_prod]
          refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj _)
          refine ENNReal.tsum_le_tsum fun p => ?_
          have hne : (p.1 + 1, p.2) ≠ ((0 : ℕ), i) := by simp
          rw [if_pos hne]
          exact x5bd_PS_mono P _ _ (fun z hz h => by rw [h] at hz; simp at hz) _ _ _
  have hfinT : ∀ i, ∑' t, ENNReal.ofReal (returnTailC P (0, i) (t + 1)) ≠ ⊤ := by
    intro i
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => hnn _ _)
      ((hpos (0, i)).comp_injective (add_left_injective 1))]
    exact ENNReal.ofReal_ne_top
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_ne_top.mpr ⟨?_, ne_top_of_le_ne_top (hfinT i) (htot i)⟩
  show ∑' j, (matOneE i j : ℝ≥0∞) ≠ ⊤
  rw [tsum_eq_single i]
  · simp [matOneE]
  · intro j hj; simp [matOneE, Ne.symm hj]

lemma x5bd_Gle {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (i j : ι) :
    matG (qbdP B A₀ A₁ A₂) 1 i j ≤ 1 := by
  classical
  show firstEntrance (qbdP B A₀ A₁ A₂) (level 0) (1, i) (0, j) ≤ 1
  rw [x5bd_fe _ _ _ _ (by simp [level])]
  exact x5bd_sum_PS_le _ (x5bd_rowE B A₀ A₁ A₂ hP) _ _ _ (by simp [level])

lemma x5bd_mulE {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hY : ∀ i j, 0 ≤ Y i j) (i j : ι) :
    ENNReal.ofReal ((X * Y) i j) = ∑' l, ENNReal.ofReal (X i l) * ENNReal.ofReal (Y l j) := by
  rw [Matrix.mul_apply, ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (hX _ _) (hY _ _)),
    tsum_fintype]
  simp_rw [ENNReal.ofReal_mul (hX _ _)]

section VE
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma x5bd_vecMulE_mm (u : ι → ℝ≥0∞) (X Y : ι → ι → ℝ≥0∞) :
    vecMulE u (matMulE X Y) = vecMulE (vecMulE u X) Y := by
  funext j
  unfold vecMulE matMulE
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun l => tsum_congr fun i => ?_
  ring

lemma x5bd_vecMulE_add (u : ι → ℝ≥0∞) (X Y : ι → ι → ℝ≥0∞) :
    vecMulE u (X + Y) = vecMulE u X + vecMulE u Y := by
  funext j
  simp only [vecMulE, Pi.add_apply, mul_add, ENNReal.tsum_add]

lemma x5bd_vecMulE_pow (u : ι → ℝ≥0∞) (X : ι → ι → ℝ≥0∞) (k : ℕ) :
    vecMulE u (matPowE X (k + 1)) = vecMulE (vecMulE u (matPowE X k)) X := by
  rw [show matPowE X (k + 1) = matMulE (matPowE X k) X from rfl, x5bd_vecMulE_mm]

lemma x5bd_vecMulE_zero (u : ι → ℝ≥0∞) : vecMulE u (matPowE (ι := ι) (fun _ _ => 0) 0) = u := by
  funext j
  show ∑' i, u i * matOneE i j = u j
  rw [tsum_eq_single j]
  · simp [matOneE]
  · intro i hi; simp [matOneE, hi]

lemma x5bd_vecMulE_one (u : ι → ℝ≥0∞) (X : ι → ι → ℝ≥0∞) : vecMulE u (matPowE X 0) = u := by
  funext j
  show ∑' i, u i * matOneE i j = u j
  rw [tsum_eq_single j]
  · simp [matOneE]
  · intro i hi; simp [matOneE, hi]

end VE

lemma x5bd_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (R : Matrix ι ι ℝ)
    (h : spectralRadius ℂ (Matrix.of fun i j => ((R i j : ℝ) : ℂ)) < 1) : IsUnit (1 - R) := by
  set Rc : Matrix ι ι ℂ := Matrix.of fun i j => ((R i j : ℝ) : ℂ) with hRc
  have hspec : (1 : ℂ) ∉ spectrum ℂ Rc := by
    intro h1
    have : ((‖(1 : ℂ)‖₊ : NNReal) : ℝ≥0∞) ≤ spectralRadius ℂ Rc :=
      le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ Rc) => ((‖k‖₊ : NNReal) : ℝ≥0∞)) 1 h1
    simp at this
    exact absurd (this.trans_lt h) (lt_irrefl _)
  rw [spectrum.mem_iff, not_not, map_one] at hspec
  have hmap : (1 : Matrix ι ι ℂ) - Rc = Complex.ofRealHom.mapMatrix (1 - R) := by
    ext i j
    simp [hRc, Matrix.one_apply]
    split_ifs <;> simp
  rw [hmap, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, isUnit_iff_ne_zero] at hspec
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  exact hspec (by rw [h0, map_zero])

-- ===== Main =====

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric
open Filter Topology

lemma x5bd_vM {ι : Type*} [Fintype ι] (v : ι → ℝ) (B R A₂ : Matrix ι ι ℝ) (j : ι) :
    Matrix.vecMul v (B + R * A₂) j =
      ∑ i, v i * B i j + ∑ i, (∑ l, v l * R l i) * A₂ i j := by
  simp only [Matrix.vecMul, dotProduct, Matrix.add_apply, Matrix.mul_apply, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem x5bd_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ) (π : ℕ × ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x)
    (hπ : IsStationaryC (qbdP B A₀ A₁ A₂) π) :
    let G : Matrix ι ι ℝ := Matrix.of fun i j => (matG (qbdP B A₀ A₁ A₂) 1 i j).toReal
    let R : Matrix ι ι ℝ := Matrix.of fun i j => (matR (qbdP B A₀ A₁ A₂) 0 i j).toReal
    let π₀ : ι → ℝ := fun i => π (0, i)
    (∀ i j, matG (qbdP B A₀ A₁ A₂) 1 i j ≠ ⊤) ∧
      (∀ i j, matR (qbdP B A₀ A₁ A₂) 0 i j ≠ ⊤) ∧
      IsUnit (1 - R) ∧
      Matrix.vecMul π₀ (Matrix.of B + Matrix.of A₀ * G) = π₀ ∧
      dotProduct (Matrix.vecMul π₀ (1 - R)⁻¹) (fun _ => 1) = 1 ∧
      (∀ x : ι → ℝ, Matrix.vecMul x (Matrix.of B + Matrix.of A₀ * G) = x →
        dotProduct (Matrix.vecMul x (1 - R)⁻¹) (fun _ => 1) = 1 → x = π₀) ∧
      Matrix.of B + Matrix.of A₀ * G = Matrix.of B + R * Matrix.of A₂ := by
  classical
  intro G R π₀
  have hP0 : ∀ x y, 0 ≤ qbdP B A₀ A₁ A₂ x y := hP.1
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => by simpa [qbdP] using hP0 (0, i) (0, j)
  have hA00 : ∀ i j, 0 ≤ A₀ i j := fun i j => by simpa [qbdP] using hP0 (0, i) (1, j)
  have hA20 : ∀ i j, 0 ≤ A₂ i j := fun i j => by simpa [qbdP] using hP0 (1, i) (0, j)
  obtain ⟨hRfin, hsp⟩ := x5bd_spsol B A₀ A₁ A₂ hP hirr hpos
  have hGfin : ∀ i j, matG (qbdP B A₀ A₁ A₂) 1 i j ≠ ⊤ := fun i j =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (x5bd_Gle B A₀ A₁ A₂ hP i j)
  have hRE : ∀ i j, matR (qbdP B A₀ A₁ A₂) 0 i j = ENNReal.ofReal (R i j) := fun i j => by
    simp [R, ENNReal.ofReal_toReal (hRfin i j)]
  have hGE : ∀ i j, matG (qbdP B A₀ A₁ A₂) 1 i j = ENNReal.ofReal (G i j) := fun i j => by
    simp [G, ENNReal.ofReal_toReal (hGfin i j)]
  have hR0 : ∀ i j, 0 ≤ R i j := fun i j => ENNReal.toReal_nonneg
  have hG0 : ∀ i j, 0 ≤ G i j := fun i j => ENNReal.toReal_nonneg
  -- `A₀ G = R A₂`
  have hF4E : matMulE (ennMat A₀) (matG (qbdP B A₀ A₁ A₂) 1) = matMulE (matR (qbdP B A₀ A₁ A₂) 0) (ennMat A₂) := by
    obtain ⟨hu1, hu2, -, -⟩ := x5bd_ugr B A₀ A₁ A₂ hP hirr hpos 1 le_rfl
    rw [hu2, ← x5bd_mm_assoc, ← hu1, x5bd_R_eq B A₀ A₁ A₂ 1]
  have hF4 : Matrix.of A₀ * G = R * Matrix.of A₂ := by
    ext i j
    have h1 := congrFun (congrFun hF4E i) j
    unfold matMulE ennMat at h1
    simp_rw [hRE, hGE] at h1
    have e1 := x5bd_mulE (Matrix.of A₀) G hA00 hG0 i j
    have e2 := x5bd_mulE R (Matrix.of A₂) hR0 hA20 i j
    simp only [Matrix.of_apply] at e1 e2
    rw [← e1, ← e2] at h1
    have n1 : 0 ≤ (Matrix.of A₀ * G) i j := by
      rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun l _ => mul_nonneg (hA00 _ _) (hG0 _ _)
    have n2 : 0 ≤ (R * Matrix.of A₂) i j := by
      rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun l _ => mul_nonneg (hR0 _ _) (hA20 _ _)
    exact (ENNReal.ofReal_eq_ofReal_iff n1 n2).mp h1
  have hπ0 : ∀ x, 0 ≤ π x := hπ.1
  have hinvπ : ∀ y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (qbdP B A₀ A₁ A₂ x y) =
      ENNReal.ofReal (π y) := by
    intro y
    have h := hπ.2.2 y
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (hπ0 x) (hP0 x y)) h.summable]
    simp_rw [ENNReal.ofReal_mul (hπ0 _)]
  have hfinπ : ∑' x, ENNReal.ofReal (π x) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hπ0 hπ.2.1.summable, hπ.2.1.tsum_eq]
    exact ENNReal.ofReal_ne_top
  have hstepπ : ∀ k j, π (k + 1, j) = ∑ i, π (k, i) * R i j := by
    intro k j
    have h := x5bd_levstep B A₀ A₁ A₂ hP hirr hpos (fun x => ENNReal.ofReal (π x)) hinvπ hfinπ k j
    simp_rw [hRE, ← ENNReal.ofReal_mul (hπ0 _), tsum_fintype] at h
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hπ0 _) (hR0 _ _))] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (hπ0 _)
      (Finset.sum_nonneg fun i _ => mul_nonneg (hπ0 _) (hR0 _ _))).mp h
  have hbal : ∀ j, π (0, j) = ∑ i, π (0, i) * B i j + ∑ i, π (1, i) * A₂ i j := by
    intro j
    have h := hinvπ (0, j)
    rw [x5bd_bal0] at h
    simp_rw [← ENNReal.ofReal_mul (hπ0 _), tsum_fintype] at h
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hπ0 _) (hB0 _ _)),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hπ0 _) (hA20 _ _)),
      ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => mul_nonneg (hπ0 _) (hB0 _ _))
        (Finset.sum_nonneg fun i _ => mul_nonneg (hπ0 _) (hA20 _ _))] at h
    exact ((ENNReal.ofReal_eq_ofReal_iff (add_nonneg
      (Finset.sum_nonneg fun i _ => mul_nonneg (hπ0 _) (hB0 _ _))
      (Finset.sum_nonneg fun i _ => mul_nonneg (hπ0 _) (hA20 _ _))) (hπ0 _)).mp h).symm
  have hπpos : ∀ i, 0 < π (0, i) := by
    intro i
    by_contra hc
    push Not at hc
    have hz : π (0, i) = 0 := le_antisymm hc (hπ0 _)
    have hall : ∀ y, π y = 0 := by
      intro y
      by_cases hy : y = (0, i)
      · rw [hy, hz]
      · have h := x5bd_tabooQ B A₀ A₁ A₂ hP hirr hpos (fun x => ENNReal.ofReal (π x)) hinvπ hfinπ
          (fun z => z ≠ (0, i)) (0, i) (by simp) y hy
        rw [tsum_eq_single (0, i)] at h
        · simp only [ne_eq, not_true_eq_false, if_false, hz, ENNReal.ofReal_zero, zero_mul] at h
          exact le_antisymm (ENNReal.ofReal_eq_zero.mp h) (hπ0 y)
        · intro b hb; simp [hb]
    have h1 : HasSum π 0 := by
      have : π = fun _ => 0 := funext hall
      rw [this]; exact hasSum_zero
    exact one_ne_zero (hπ.2.1.unique h1)
  have hπM : Matrix.vecMul π₀ (Matrix.of B + R * Matrix.of A₂) = π₀ := by
    funext j
    rw [x5bd_vM]
    have e := hstepπ 0
    simp only [zero_add] at e
    simp only [Matrix.of_apply, π₀]
    rw [hbal j]
    simp_rw [e]
  have hU : IsUnit (1 - R) := x5bd_isUnit R hsp
  -- normalization
  have hsumk : ∀ j, Summable (fun k => π (k, j)) := fun j =>
    hπ.2.1.summable.comp_injective (fun a b h => by simpa using congrArg Prod.fst h)
  set w : ι → ℝ := fun j => ∑' k, π (k, j) with hw
  have hwR : Matrix.vecMul w (1 - R) = π₀ := by
    funext j
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply]
    have h1 : Matrix.vecMul w R j = ∑' k, π (k + 1, j) := by
      simp only [Matrix.vecMul, dotProduct, hw]
      simp_rw [← tsum_mul_right]
      rw [← Summable.tsum_finsetSum (fun i _ => (hsumk i).mul_right _)]
      exact tsum_congr fun k => (hstepπ k j).symm
    rw [h1, hw]
    simp only [π₀]
    rw [(hsumk j).tsum_eq_zero_add]
    ring
  have hw1 : ∑ j, w j = 1 := by
    simp only [hw]
    rw [← Summable.tsum_finsetSum (fun j _ => hsumk j)]
    have := hπ.2.1.summable.tsum_prod' (fun k => (Summable.of_finite : Summable fun j : ι => π (k, j)))
    rw [hπ.2.1.tsum_eq] at this
    rw [this]
    exact tsum_congr fun k => (tsum_fintype _).symm
  have hinvw : Matrix.vecMul π₀ (1 - R)⁻¹ = w := by
    rw [← hwR, Matrix.vecMul_vecMul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.vecMul_one]
  have hnorm : dotProduct (Matrix.vecMul π₀ (1 - R)⁻¹) (fun _ => 1) = 1 := by
    rw [hinvw]; simp [dotProduct, hw1]
  -- uniqueness
  have huniq : ∀ x : ι → ℝ, Matrix.vecMul x (Matrix.of B + Matrix.of A₀ * G) = x →
      dotProduct (Matrix.vecMul x (1 - R)⁻¹) (fun _ => 1) = 1 → x = π₀ := by
    intro x hx hxn
    rw [hF4] at hx
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
    · funext i; exact (IsEmpty.false i).elim
    set c : ℝ := ∑ i, |x i| / π₀ i with hc
    have hc_ge : ∀ i, |x i| / π₀ i ≤ c := fun i =>
      Finset.single_le_sum (f := fun i => |x i| / π₀ i)
        (fun i _ => div_nonneg (abs_nonneg _) (hπpos i).le) (Finset.mem_univ i)
    set u : ι → ℝ := x + c • π₀ with hu
    have hu0 : ∀ i, 0 ≤ u i := by
      intro i
      have h1 := hc_ge i
      have hp : 0 < π₀ i := hπpos i
      have h2 : |x i| ≤ c * π₀ i := by rwa [div_le_iff₀ hp] at h1
      have h3 := neg_abs_le (x i)
      simp only [hu, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    have huM : Matrix.vecMul u (Matrix.of B + R * Matrix.of A₂) = u := by
      rw [hu, Matrix.add_vecMul, Matrix.smul_vecMul, hx, hπM]
    set uE : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (u i) with huE_def
    set RE := matR (qbdP B A₀ A₁ A₂) 0 with hREd
    set ν : ℕ × ι → ℝ≥0∞ := fun p => vecMulE uE (matPowE RE p.1) p.2 with hν
    have hν0 : ∀ i, ν (0, i) = uE i := fun i => congrFun (x5bd_vecMulE_one uE RE) i
    have hν1 : ∀ i, ν (1, i) = ∑' l, uE l * RE l i := by
      intro i
      simp only [hν]
      rw [x5bd_vecMulE_pow, x5bd_vecMulE_one]
      rfl
    have huE : ∀ j, uE j = ∑' i, uE i * ENNReal.ofReal (B i j) +
        ∑' i, (∑' l, uE l * RE l i) * ENNReal.ofReal (A₂ i j) := by
      intro j
      have h := congrFun huM j
      rw [x5bd_vM] at h
      simp only [Matrix.of_apply] at h
      have n1 : ∀ i, 0 ≤ ∑ l, u l * R l i := fun i =>
        Finset.sum_nonneg fun l _ => mul_nonneg (hu0 l) (hR0 l i)
      simp only [huE_def]
      rw [← h, ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => mul_nonneg (hu0 i) (hB0 i j))
        (Finset.sum_nonneg fun i _ => mul_nonneg (n1 i) (hA20 i j)),
        ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hu0 i) (hB0 i j)),
        ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (n1 i) (hA20 i j)), tsum_fintype,
        tsum_fintype]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul (hu0 i)
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (n1 i), ENNReal.ofReal_sum_of_nonneg
          (fun l _ => mul_nonneg (hu0 l) (hR0 l i)), tsum_fintype]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [ENNReal.ofReal_mul (hu0 l), hRE]
    have hinvν : ∀ y, ∑' x, ν x * ENNReal.ofReal (qbdP B A₀ A₁ A₂ x y) = ν y := by
      rintro ⟨_ | k, j⟩
      · rw [x5bd_bal0]
        simp_rw [hν0, hν1]
        exact (huE j).symm
      · rw [x5bd_balk]
        set v := vecMulE uE (matPowE RE k) with hv
        have e1 : ∀ i, ν (k + 1, i) = vecMulE v RE i := fun i => by
          simp only [hν]; rw [x5bd_vecMulE_pow]
        have e2 : ∀ i, ν (k + 2, i) = vecMulE (vecMulE v RE) RE i := fun i => by
          simp only [hν]; rw [x5bd_vecMulE_pow, x5bd_vecMulE_pow]
        have e0 : ∀ i, ν (k, i) = v i := fun i => rfl
        simp_rw [e0, e1, e2]
        have hq := (x5bd_quad B A₀ A₁ A₂ hP hirr hpos 1 le_rfl).2.2
        rw [x5bd_R_eq B A₀ A₁ A₂ 1, ← hREd] at hq
        conv_rhs => rw [hq]
        rw [x5bd_vecMulE_add, x5bd_vecMulE_add, x5bd_vecMulE_mm, x5bd_vecMulE_mm, x5bd_vecMulE_mm]
        simp only [Pi.add_apply, vecMulE, ennMat]
    have hfinν : ∑' p, ν p ≠ ⊤ := by
      rw [ENNReal.tsum_prod']
      have : ∑' k, ∑' j, ν (k, j) = ∑' i, uE i * ∑' k, ∑' j, matPowE RE k i j := by
        simp only [hν, vecMulE]
        simp_rw [← ENNReal.tsum_mul_left]
        conv_lhs => arg 1; ext k; rw [ENNReal.tsum_comm]
        rw [ENNReal.tsum_comm]
      rw [this, tsum_fintype]
      exact ENNReal.sum_ne_top.mpr fun i _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (x5bd_Rsum B A₀ A₁ A₂ hP hirr hpos i)
    have hprop : ∀ j, u j * π₀ i0 = u i0 * π₀ j := by
      intro j
      by_cases hj : j = i0
      · rw [hj]
      have hy : ((0 : ℕ), j) ≠ (0, i0) := by simp [hj]
      have h1 := x5bd_tabooQ B A₀ A₁ A₂ hP hirr hpos ν hinvν hfinν (fun z => z ≠ (0, i0)) (0, i0)
        (by simp) _ hy
      have h2 := x5bd_tabooQ B A₀ A₁ A₂ hP hirr hpos (fun x => ENNReal.ofReal (π x)) hinvπ hfinπ
        (fun z => z ≠ (0, i0)) (0, i0) (by simp) _ hy
      rw [tsum_eq_single (0, i0) (by intro b hb; simp [hb])] at h1 h2
      simp only [ne_eq, not_true_eq_false, if_false] at h1 h2
      rw [hν0, hν0] at h1
      have h3 : uE j * ENNReal.ofReal (π (0, i0)) = uE i0 * ENNReal.ofReal (π (0, j)) := by
        rw [h1, h2]; ring
      simp only [huE_def] at h3
      rw [← ENNReal.ofReal_mul (hu0 j), ← ENNReal.ofReal_mul (hu0 i0)] at h3
      exact (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (hu0 j) (hπ0 _))
        (mul_nonneg (hu0 i0) (hπ0 _))).mp h3
    set lam : ℝ := u i0 / π₀ i0 with hlam
    have hx_eq : x = (lam - c) • π₀ := by
      funext j
      have hj := hprop j
      have hp : 0 < π₀ i0 := hπpos i0
      have h1 : u j = lam * π₀ j := by
        rw [hlam, div_mul_eq_mul_div, eq_div_iff hp.ne']
        linarith
      have h2 : u j = x j + c * π₀ j := by simp [hu]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [sub_mul]
      linarith
    rw [hx_eq] at hxn ⊢
    rw [Matrix.smul_vecMul, smul_dotProduct, hnorm, smul_eq_mul, mul_one] at hxn
    rw [hxn, one_smul]
  exact ⟨hGfin, hRfin, hU, by rw [hF4]; exact hπM, hnorm, huniq, by rw [hF4]⟩


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ) (π : ℕ × ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x)
    (hπ : IsStationaryC (qbdP B A₀ A₁ A₂) π) :
    let G : Matrix ι ι ℝ := Matrix.of fun i j => (matG (qbdP B A₀ A₁ A₂) 1 i j).toReal
    let R : Matrix ι ι ℝ := Matrix.of fun i j => (matR (qbdP B A₀ A₁ A₂) 0 i j).toReal
    let π₀ : ι → ℝ := fun i => π (0, i)
    (∀ i j, matG (qbdP B A₀ A₁ A₂) 1 i j ≠ ⊤) ∧
      (∀ i j, matR (qbdP B A₀ A₁ A₂) 0 i j ≠ ⊤) ∧
      IsUnit (1 - R) ∧
      Matrix.vecMul π₀ (Matrix.of B + Matrix.of A₀ * G) = π₀ ∧
      dotProduct (Matrix.vecMul π₀ (1 - R)⁻¹) (fun _ => 1) = 1 ∧
      (∀ x : ι → ℝ, Matrix.vecMul x (Matrix.of B + Matrix.of A₀ * G) = x →
        dotProduct (Matrix.vecMul x (1 - R)⁻¹) (fun _ => 1) = 1 → x = π₀) ∧
      Matrix.of B + Matrix.of A₀ * G = Matrix.of B + R * Matrix.of A₂ :=
  x5bd_main B A₀ A₁ A₂ π hP hirr hpos hπ

#print axioms solution
