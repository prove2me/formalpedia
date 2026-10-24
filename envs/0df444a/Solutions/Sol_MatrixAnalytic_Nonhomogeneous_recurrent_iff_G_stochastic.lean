-- Prove2me | solution 1 for MatrixAnalytic.Nonhomogeneous.recurrent_iff_G_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:38:24.86339+00:00
-- url     : https://prove2.me/submissions/27140085-4917-4971-8574-152ed64eab93

import Mathlib
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Chain
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Passage

-- ==== Base ====

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous

noncomputable def x5nh_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def x5nh_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then x5nh_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5nh_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * x5nh_W P ω := by
  unfold x5nh_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma x5nh_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5nh_W P (Fin.snoc ω k : Fin (n + 2) → V) = x5nh_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold x5nh_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma x5nh_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma x5nh_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma x5nh_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma x5nh_PS_zero (x y : V) (A : V → Prop) :
    x5nh_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold x5nh_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [x5nh_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma x5nh_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma x5nh_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5nh_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then x5nh_PS P z L y A else 0) := by
  classical
  unfold x5nh_PS
  rw [x5nh_tsum_cons, tsum_eq_single x]
  · simp_rw [x5nh_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := x5nh_cond_cons x y A ω
      rw [x5nh_W_cons]
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

lemma x5nh_PS_one (x y : V) (A : V → Prop) :
    x5nh_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [x5nh_PS_cons P, tsum_eq_single y]
  · simp [x5nh_PS_zero]
  · intro z hz; simp [x5nh_PS_zero, hz]

open Classical in
noncomputable def x5nh_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then x5nh_W P ω else 0

open Classical in
noncomputable def x5nh_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then x5nh_W P ω else 0

lemma x5nh_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P x A (t + 1) + x5nh_EX P x A (t + 1) = x5nh_AV P x A t := by
  classical
  unfold x5nh_AV x5nh_EX
  rw [x5nh_tsum_snoc, x5nh_tsum_snoc, ← ENNReal.tsum_add]
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
  simp_rw [hz, hA, hB, Fin.snoc_last, x5nh_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        x5nh_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        x5nh_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        x5nh_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
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

lemma x5nh_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P x A t + ∑ k ∈ Finset.range t, x5nh_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold x5nh_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [x5nh_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (x5nh_EX P x A (t + 1)), ← add_assoc,
      add_comm (x5nh_EX P x A (t + 1)), x5nh_step P hrow x A t, ih]

lemma x5nh_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    x5nh_PS P x k y A ≤ x5nh_EX P x A k := by
  classical
  unfold x5nh_PS x5nh_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma x5nh_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, x5nh_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← x5nh_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => x5nh_PS_le_EX P x y A hy (k + 1)).trans le_add_self

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma x5nh_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → x5nh_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5nh_PS P x (s + 1) z (fun z => m + 1 < lev z) * x5nh_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [x5nh_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', x5nh_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then x5nh_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        x5nh_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * x5nh_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [x5nh_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5nh_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        x5nh_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          x5nh_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5nh_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          x5nh_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          x5nh_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          x5nh_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5nh_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [x5nh_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
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

lemma x5nh_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma x5nh_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5nh_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then x5nh_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold x5nh_PS
  rw [x5nh_tsum_snoc]
  simp_rw [x5nh_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := x5nh_cond_snoc x y A ω
    rw [x5nh_W_snoc]
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
lemma x5nh_conv3 (InvT mid A A' : V → Prop) [DecidablePred mid] (x : V) (hx : mid x)
    (hstep : ∀ w y, InvT y → P w y ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ InvT w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ L y, InvT y → x5nh_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5nh_PS P x s z A * x5nh_PS P z (L + 1 - s) y A' else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [x5nh_PS_one]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, x5nh_PS_one]
    rw [tsum_eq_single x]
    · rw [if_pos hx, x5nh_PS_zero, if_pos rfl, one_mul]
    · intro z hz
      rw [x5nh_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ L ih =>
    intro y hy
    rw [Finset.sum_range_succ, x5nh_PS_snoc P x (L + 1)]
    have hlast : ∀ z, (if mid z then x5nh_PS P x (L + 1) z A *
        x5nh_PS P z (L + 1 + 1 - (L + 1)) y A' else 0) =
        if mid z then x5nh_PS P x (L + 1) z A * ENNReal.ofReal (P z y) else 0 := fun z => by
      rw [show L + 1 + 1 - (L + 1) = 1 by omega, x5nh_PS_one]
    simp_rw [hlast]
    have h1 : ∀ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5nh_PS P x s z A * x5nh_PS P z (L + 1 + 1 - s) y A' else 0) =
        ∑' w, (if A' w then ∑' z, (if mid z then
          x5nh_PS P x s z A * x5nh_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
      intro s hs
      have hs' : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have e : ∀ z, (if mid z then
          x5nh_PS P x s z A * x5nh_PS P z (L + 1 + 1 - s) y A' else 0) =
          ∑' w, (if A' w then (if mid z then
          x5nh_PS P x s z A * x5nh_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
        intro z
        rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, x5nh_PS_snoc P z (L + 1 - s)]
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

lemma x5nh_cauchy0 (a b : ℕ → ℝ≥0∞) :
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
lemma x5nh_swap0 {V : Type*} (mid : V → Prop) [DecidablePred mid] (a : V → ℕ → ℝ≥0∞)
    (b : V → ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) =
      ∑' z, if mid z then (∑' s, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact x5nh_cauchy0 (a z) (b z)
  · simp [hz]

section GRK
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma x5nh_EX_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5nh_EX P x A k = ∑' y, if ¬ A y then x5nh_PS P x k y A else 0 := by
  classical
  unfold x5nh_EX x5nh_PS
  simp_rw [x5nh_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last k))]
  · by_cases hA : A (ω (Fin.last k)) <;> simp [hA]
  · intro y hy; simp [Ne.symm hy]

open Classical in
lemma x5nh_AV_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5nh_AV P x A (k + 1) = ∑' y, if A y then x5nh_PS P x (k + 1) y A else 0 := by
  classical
  unfold x5nh_AV x5nh_PS
  simp_rw [x5nh_ite_tsum]
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

lemma x5nh_PS_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x y : V) (L : ℕ) :
    x5nh_PS P x L y A ≤ x5nh_PS P x L y A' := by
  classical
  unfold x5nh_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, fun m h1 h2 => hAA _ (h.2.2 m h1 h2)⟩]
  · rw [if_neg h]; exact bot_le

lemma x5nh_PS_concat (A : V → Prop) (y z : V) (hy : A y) :
    ∀ u x t, x5nh_PS P x u y A * x5nh_PS P y t z A ≤ x5nh_PS P x (u + t) z A := by
  classical
  intro u
  induction u with
  | zero =>
    intro x t
    rw [x5nh_PS_zero, zero_add]
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]; exact bot_le
  | succ u ih =>
    intro x t
    rw [x5nh_PS_cons P x u y A, show u + 1 + t = (u + t) + 1 by omega,
      x5nh_PS_cons P x (u + t) z A, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [mul_assoc]
    gcongr
    by_cases hw : A w
    · rw [if_pos (Or.inr hw), if_pos (Or.inr hw)]; exact ih w t
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg (fun h => hw (by rw [h]; exact hy)), zero_mul]
        exact bot_le
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hw h]), zero_mul]; exact bot_le

lemma x5nh_taboo_extract (x0 y : V) (hy : y ≠ x0) (L : ℕ)
    (h : x5nh_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ u, x5nh_PS P x0 u y (fun z => z ≠ x0) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [x5nh_PS_zero, if_neg (Ne.symm hy)] at h; exact absurd rfl h
  rw [x5nh_conv3 P (fun _ => True) (fun z => z = x0) (fun _ => True) (fun z => z ≠ x0) x0 rfl
    (fun w _ _ _ => by by_cases hw : w = x0 <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if z = x0 then x5nh_PS P x0 s z (fun _ => True) *
      x5nh_PS P z (L + 1 - s) y (fun z => z ≠ x0) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzx : z = x0
  · rw [if_pos hzx] at hz
    subst hzx
    exact ⟨_, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzx] at hz; exact absurd rfl hz

lemma x5nh_ofReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  exact ENNReal.ofReal_tsum_of_nonneg hf hs
end GRK


section BDGen
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_AV_zero (x : V) (A : V → Prop) : x5nh_AV P x A 0 = 1 := by
  classical
  unfold x5nh_AV
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  rw [tsum_eq_single x]
  · simp [x5nh_W]
  · intro b hb; simp [hb]

lemma x5nh_AV_anti (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P x A (t + 1) ≤ x5nh_AV P x A t := by
  rw [← x5nh_step P hrow x A t]; exact le_self_add

lemma x5nh_PS_le_AV (x y : V) (A : V → Prop) (hy : A y) (t : ℕ) :
    x5nh_PS P x t y A ≤ x5nh_AV P x A t := by
  classical
  unfold x5nh_PS x5nh_AV
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → A (ω m)
  · rw [if_pos h, if_pos]
    refine ⟨h.1, fun i hi => ?_⟩
    by_cases hl : i = Fin.last t
    · rw [hl, h.2.1]; exact hy
    · exact h.2.2 i hi hl
  · rw [if_neg h]; exact bot_le

lemma x5nh_AV_concat (A : V → Prop) (x z : V) (hz : A z) (u t : ℕ) :
    x5nh_PS P x u z A * x5nh_AV P z A t ≤ x5nh_AV P x A (u + t) := by
  classical
  rcases t with _ | s
  · rw [x5nh_AV_zero, mul_one, add_zero]; exact x5nh_PS_le_AV P x z A hz u
  · rw [x5nh_AV_eq P z A s, show u + (s + 1) = (u + s) + 1 by omega, x5nh_AV_eq P x A (u + s),
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    split_ifs with hy
    · have := x5nh_PS_concat P A z y hz u x (s + 1)
      rwa [show u + (s + 1) = u + s + 1 by omega] at this
    · simp

lemma x5nh_stepPow_nonneg [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y; simp only [stepPow]
    exact tsum_nonneg fun z => mul_nonneg (ih x z) (hP0 z y)

lemma x5nh_stepPow_PS [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 < stepPow P t x y → x5nh_PS P x t y (fun _ => True) ≠ 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro x y h
    simp only [stepPow] at h
    rw [x5nh_PS_zero]
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
        le_antisymm (hc z) (mul_nonneg (x5nh_stepPow_nonneg P hP0 t x z) (hP0 z y))
      simp [this] at h
    have ha := x5nh_stepPow_nonneg P hP0 t x z
    have h1 : 0 < stepPow P t x z :=
      lt_of_le_of_ne ha (fun h0 => by rw [← h0, zero_mul] at hz; exact lt_irrefl 0 hz)
    have h2 : 0 < P z y :=
      lt_of_le_of_ne (hP0 z y) (fun h0 => by rw [← h0, mul_zero] at hz; exact lt_irrefl 0 hz)
    rw [x5nh_PS_snoc P x t y (fun _ => True)]
    intro h0
    have := (ENNReal.tsum_eq_zero.mp h0) z
    rw [if_pos (Or.inr trivial)] at this
    rcases mul_eq_zero.mp this with h3 | h3
    · exact ih x z h1 h3
    · exact absurd h3 (by simpa using h2)

lemma x5nh_AV_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P x A t ≤ 1 :=
  le_self_add.trans_eq (x5nh_mass P hrow x A t)

end BDGen

-- ==== Fin ====

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous

section NHFin
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_partial (a b : ℕ → ℝ≥0∞) (T : ℕ) :
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
  rw [e1, ← e2, ← x5nh_cauchy0]
  exact ENNReal.sum_le_tsum _

lemma x5nh_PS_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (t : ℕ) : x5nh_PS P x t y A ≤ 1 := by
  classical
  rcases t with _ | k
  · rw [x5nh_PS_zero]; split_ifs <;> simp
  by_cases hA : A y
  · exact (x5nh_PS_le_AV P x y A hA _).trans (x5nh_AV_le_one P hrow x A _)
  · refine (x5nh_PS_le_EX P x y A hA _).trans ?_
    rw [← x5nh_mass P hrow x A (k + 1)]
    exact (Finset.single_le_sum (f := fun j => x5nh_EX P x A (j + 1)) (fun _ _ => bot_le)
      (Finset.self_mem_range_succ k)).trans le_add_self

/-- first-visit decomposition at `y` -/
lemma x5nh_fv (A : V → Prop) (y : V) (hy : A y) :
    ∀ L x, x ≠ y → x5nh_PS P x L y A =
      ∑ s ∈ Finset.range (L + 1),
        x5nh_PS P x s y (fun z => A z ∧ z ≠ y) * x5nh_PS P y (L - s) y A := by
  classical
  intro L
  induction L with
  | zero => intro x hx; simp [x5nh_PS_zero, hx]
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', x5nh_PS_zero P x y, if_neg hx, zero_mul, add_zero]
    simp_rw [x5nh_PS_cons P x _ y]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine tsum_congr fun z => ?_
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    by_cases hzy : z = y
    · subst hzy
      rw [if_pos (Or.inr hy), Finset.sum_eq_single 0]
      · simp [x5nh_PS_zero]
      · intro s _ hs
        rw [if_neg (by simp [hs])]; simp
      · simp
    · by_cases hAz : A z
      · rw [if_pos (Or.inr hAz), ih z hzy]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [if_pos (Or.inr ⟨hAz, hzy⟩)]
        congr 2
        omega
      · rcases Nat.eq_zero_or_pos L with hL | hL
        · subst hL; simp [x5nh_PS_zero, hzy]
        · rw [if_neg (by rintro (h | h) <;> [omega; exact hAz h])]
          symm
          refine Finset.sum_eq_zero fun s _ => ?_
          by_cases hs : s = 0
          · subst hs; simp [x5nh_PS_zero, hzy]
          · rw [if_neg (by rintro (h | h) <;> [exact hs h; exact hAz h.1])]; simp

/-- the diagonal entry is bounded by `(1 - q)⁻¹` -/
lemma x5nh_diag (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (y : V) (hy : A y)
    (hq : ∑' u, x5nh_PS P y (u + 1) y (fun z => A z ∧ z ≠ y) < 1) :
    ∑' t, x5nh_PS P y t y A ≠ ⊤ := by
  classical
  set q := ∑' u, x5nh_PS P y (u + 1) y (fun z => A z ∧ z ≠ y) with hqd
  set f : ℕ → ℝ≥0∞ := fun t => x5nh_PS P y t y A with hf
  have hstep : ∀ w y', (fun _ => True) y' → P w y' ≠ 0 →
      ((fun z => z = y) w ∧ A w ∧ ¬ (fun z => A z ∧ z ≠ y) w) ∨
      ((fun z => A z ∧ z ≠ y) w ∧ A w ∧ (fun _ => True) w ∧ ¬ (fun z => z = y) w) ∨
      (¬ A w ∧ ¬ (fun z => A z ∧ z ≠ y) w ∧ ¬ (fun z => z = y) w) := by
    intro w _ _ _
    by_cases hw : w = y
    · subst hw; left; exact ⟨rfl, hy, by simp⟩
    · by_cases hA : A w
      · right; left; exact ⟨⟨hA, hw⟩, hA, trivial, hw⟩
      · right; right; exact ⟨hA, by tauto, hw⟩
  have hconv : ∀ L, f (L + 1) = ∑ s ∈ Finset.range (L + 1),
      f s * x5nh_PS P y ((L - s) + 1) y (fun z => A z ∧ z ≠ y) := by
    intro L
    rw [hf]; dsimp only
    rw [x5nh_conv3 P (fun _ => True) (fun z => z = y) A (fun z => A z ∧ z ≠ y) y rfl hstep L y
      trivial]
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [tsum_eq_single y (fun z hz => if_neg hz), if_pos rfl, show L + 1 - s = L - s + 1 by omega]
  have hf0 : f 0 = 1 := by simp [hf, x5nh_PS_zero]
  have hS : ∀ T, ∑ t ∈ Finset.range (T + 1), f t ≤ 1 + (∑ t ∈ Finset.range T, f t) * q := by
    intro T
    rw [Finset.sum_range_succ', hf0, add_comm _ 1]
    gcongr
    rw [Finset.sum_congr rfl fun L _ => hconv L]
    exact x5nh_partial f (fun u => x5nh_PS P y (u + 1) y (fun z => A z ∧ z ≠ y)) T
  have hfin : ∀ T, ∑ t ∈ Finset.range T, f t ≠ ⊤ := fun T =>
    ENNReal.sum_ne_top.mpr fun t _ => ne_top_of_le_ne_top ENNReal.one_ne_top
      (x5nh_PS_le_one P hrow y y A t)
  have hq1 : q ≠ ⊤ := ne_top_of_lt hq
  have hbound : ∀ T, ∑ t ∈ Finset.range T, f t ≤ (1 - q)⁻¹ := by
    intro T
    set S := ∑ t ∈ Finset.range T, f t
    have h1 : S ≤ 1 + S * q :=
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ T))).trans (hS T)
    rw [ENNReal.le_inv_iff_mul_le, mul_comm, ENNReal.sub_mul (fun _ _ => hfin T), one_mul]
    exact tsub_le_iff_left.mpr (h1.trans_eq (by rw [add_comm, mul_comm]))
  have hne : (1 - q)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_of_lt hq))
  refine ne_top_of_le_ne_top hne ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le hbound

/-- an escape path forces `q < 1` -/
lemma x5nh_q_lt (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (y z : V)
    (hz : ¬ A z) (k0 : ℕ) (he : x5nh_PS P y (k0 + 1) z (fun w => A w ∧ w ≠ y) ≠ 0)
    (hy : A y) :
    ∑' u, x5nh_PS P y (u + 1) y (fun z => A z ∧ z ≠ y) < 1 := by
  classical
  set A' : V → Prop := fun w => A w ∧ w ≠ y
  set e := x5nh_PS P y (k0 + 1) z A'
  have hyz : y ≠ z := fun h => hz (h ▸ hy)
  have hEX : ∑' k, x5nh_EX P y A' (k + 1) ≤ 1 := by
    refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
    rw [← x5nh_mass P hrow y A' t]
    exact le_add_self
  have hterm : ∀ k, x5nh_PS P y (k + 1) y A' + (if k = k0 then e else 0) ≤
      x5nh_EX P y A' (k + 1) := by
    intro k
    rw [x5nh_EX_eq]
    refine le_trans ?_ (ENNReal.sum_le_tsum ({y, z} : Finset V))
    rw [Finset.sum_pair hyz, if_pos (show ¬ A' y from fun h => h.2 rfl),
      if_pos (show ¬ A' z from fun h => hz h.1)]
    gcongr
    by_cases hk : k = k0
    · rw [if_pos hk, hk]
    · rw [if_neg hk]; exact bot_le
  have h2 : ∑' u, x5nh_PS P y (u + 1) y A' + e ≤ 1 := by
    refine le_trans ?_ hEX
    calc ∑' u, x5nh_PS P y (u + 1) y A' + e
        = ∑' k, (x5nh_PS P y (k + 1) y A' + if k = k0 then e else 0) := by
          rw [ENNReal.tsum_add, tsum_ite_eq]
      _ ≤ _ := ENNReal.tsum_le_tsum hterm
  have hq1 : ∑' u, x5nh_PS P y (u + 1) y A' ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans h2)
  exact (ENNReal.lt_add_right hq1 he).trans_le h2

/-- first exit from `A` along a nonzero path -/
lemma x5nh_exit (A B : V → Prop) (z0 : V) (hz0 : ¬ A z0) :
    ∀ u x, x5nh_PS P x (u + 1) z0 B ≠ 0 →
      ∃ z k, ¬ A z ∧ x5nh_PS P x (k + 1) z (fun w => A w ∧ B w) ≠ 0 := by
  classical
  intro u
  induction u with
  | zero =>
    intro x h
    exact ⟨z0, 0, hz0, by rw [x5nh_PS_one] at h ⊢; exact h⟩
  | succ u ih =>
    intro x h
    rw [x5nh_PS_cons] at h
    obtain ⟨w, hw⟩ : ∃ w, ENNReal.ofReal (P x w) *
        (if u + 1 = 0 ∨ B w then x5nh_PS P w (u + 1) z0 B else 0) ≠ 0 := by
      by_contra hc; push Not at hc; exact h (ENNReal.tsum_eq_zero.mpr hc)
    have hBw : B w := by
      by_contra hb; rw [if_neg (by rintro (h | h) <;> [omega; exact hb h])] at hw; simp at hw
    rw [if_pos (Or.inr hBw)] at hw
    have hPw := left_ne_zero_of_mul hw
    have hPS := right_ne_zero_of_mul hw
    by_cases hAw : A w
    · obtain ⟨z, k, hz, hk⟩ := ih w hPS
      refine ⟨z, k + 1, hz, ?_⟩
      rw [x5nh_PS_cons]
      intro h0
      have := (ENNReal.tsum_eq_zero.mp h0) w
      rw [if_pos (Or.inr ⟨hAw, hBw⟩)] at this
      rcases mul_eq_zero.mp this with h3 | h3
      · exact hPw h3
      · exact hk h3
    · exact ⟨w, 0, hAw, by rw [x5nh_PS_one]; exact hPw⟩

/-- finiteness of the expected number of visits to `y` within `A` -/
lemma x5nh_N_fin (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (y : V) (hy : A y)
    (z0 : V) (hz0 : ¬ A z0) (t0 : ℕ) (hreach : x5nh_PS P y t0 z0 (fun _ => True) ≠ 0) (x : V) :
    ∑' t, x5nh_PS P x t y A ≠ ⊤ := by
  classical
  have hyz : z0 ≠ y := fun h => hz0 (h ▸ hy)
  obtain ⟨u, hu⟩ := x5nh_taboo_extract P y z0 hyz t0 hreach
  obtain ⟨u, rfl⟩ : ∃ u', u = u' + 1 := by
    rcases u with _ | u'
    · rw [x5nh_PS_zero, if_neg (Ne.symm hyz)] at hu; exact absurd rfl hu
    · exact ⟨u', rfl⟩
  obtain ⟨z, k, hz, hk⟩ := x5nh_exit P A (fun w => w ≠ y) z0 hz0 u y hu
  have hq := x5nh_q_lt P hrow A y z hz k hk hy
  have hd := x5nh_diag P hrow A y hy hq
  by_cases hxy : x = y
  · subst hxy; exact hd
  rw [tsum_congr fun L => x5nh_fv P A y hy L x hxy,
    x5nh_cauchy0 (fun s => x5nh_PS P x s y (fun z => A z ∧ z ≠ y)) (fun u => x5nh_PS P y u y A)]
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ?_) hd
  rw [tsum_eq_zero_add' ENNReal.summable, x5nh_PS_zero, if_neg hxy, zero_add]
  exact x5nh_sum_PS_le P hrow x y _ (by simp)

end NHFin

-- ==== Ugr ====

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous

section NHU
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_PS_congr (I A A' : V → Prop) (y : V)
    (hstep : ∀ w z, I w → P w z ≠ 0 → (A z ↔ A' z) ∧ (A z → I z)) :
    ∀ L x, I x → x5nh_PS P x L y A = x5nh_PS P x L y A' := by
  classical
  intro L
  induction L with
  | zero => intro x _; rw [x5nh_PS_zero, x5nh_PS_zero]
  | succ L ih =>
    intro x hx
    rw [x5nh_PS_cons P x L y A, x5nh_PS_cons P x L y A']
    refine tsum_congr fun z => ?_
    by_cases hP0 : P x z = 0
    · simp [hP0]
    obtain ⟨hiff, hI⟩ := hstep x z hx hP0
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp only [true_or, if_true, x5nh_PS_zero]
    · by_cases hz : A z
      · rw [if_pos (Or.inr hz), if_pos (Or.inr (hiff.mp hz)), ih z (hI hz)]
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hz h]),
          if_neg (by rintro (h | h) <;> [omega; exact hz (hiff.mpr h)])]

lemma x5nh_swapT {W : Type*} (mid : W → Prop) [DecidablePred mid] (a : W → ℕ → ℝ≥0∞)
    (b : W → ℕ → ℝ≥0∞) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) ≤
      ∑' z, if mid z then (∑ s ∈ Finset.range T, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact x5nh_partial (a z) (b z) T
  · simp [hz]

lemma x5nh_seriesInv {ι : Type*} [Countable ι] [DecidableEq ι] (U N : ι → ι → ℝ≥0∞)
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

lemma x5nh_fe [DecidableEq V] (T : Set V) (x y : V) (hy : y ∈ T) :
    firstEntrance P T x y = ∑' t, x5nh_PS P x (t + 1) y (fun z => z ∉ T) := by
  classical
  unfold firstEntrance x5nh_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
      ∀ m : Fin (t + 1 + 1), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · rw [if_pos ⟨h.1, h.2.1, hy, h.2.2⟩, if_pos h]; rfl
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg h]

lemma x5nh_eva' [DecidableEq V] (T : Set V) (x y : V) (hy : y ∉ T) :
    expVisitsAvoid P T x y = ∑' t, x5nh_PS P x t y (fun z => z ∉ T) := by
  classical
  unfold expVisitsAvoid x5nh_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  have hc : (ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ T) ↔
      (ω 0 = x ∧ ω (Fin.last t) = y ∧
        ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → ω m ∉ T) := by
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun m hm _ => h3 m hm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun m hm => ?_⟩
      by_cases hl : m = Fin.last t
      · rw [hl, h2]; exact hy
      · exact h3 m hm hl
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧
      ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → ω m ∉ T
  · rw [if_pos (hc.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

end NHU

section NHQ
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]

lemma x5nh_levn (n : ℕ) (f : (Σ k, ι k) → ℝ≥0∞) :
    ∑' z : Σ k, ι k, (if z.1 = n then f z else 0) = ∑' l, f ⟨n, l⟩ := by
  rw [ENNReal.tsum_sigma', tsum_eq_single n]
  · simp
  · intro m hm; simp [hm]

variable (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)

omit [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)] in
lemma x5nh_qnz (x w : Σ k, ι k) (h : ndqbdP A₀ A₁ A₂ x w ≠ 0) :
    w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 := by
  unfold ndqbdP at h
  split_ifs at h <;> first | omega | exact absurd rfl h

omit [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)] in
lemma x5nh_P0 (n : ℕ) (i : ι n) (l : ι (n + 1)) :
    ndqbdP A₀ A₁ A₂ ⟨n, i⟩ ⟨n + 1, l⟩ = A₀ n i l := by
  simp [ndqbdP]

omit [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)] in
lemma x5nh_P1 (n : ℕ) (i l : ι n) :
    ndqbdP A₀ A₁ A₂ ⟨n, i⟩ ⟨n, l⟩ = A₁ n i l := by
  simp [ndqbdP]

omit [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)] in
lemma x5nh_P2 (m : ℕ) (i : ι (m + 1)) (l : ι m) :
    ndqbdP A₀ A₁ A₂ ⟨m + 1, i⟩ ⟨m, l⟩ = A₂ m i l := by
  simp only [ndqbdP]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos trivial]
  rfl

end NHQ

-- ==== Main ====

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous

section NHMain
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)

/-- the expected-visits matrix `N` at level `m + 1` before the first visit to `ℓ(≤ m)` -/
noncomputable def x5nh_N (m : ℕ) : ι (m + 1) → ι (m + 1) → ℝ≥0∞ := fun i j =>
  ∑' t, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 1, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1)

lemma x5nh_hU (n : ℕ) (i j : ι n) : matU (ndqbdP A₀ A₁ A₂) n i j =
    ∑' t, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨n, i⟩ (t + 1) ⟨n, j⟩ (fun z => n < z.1) := by
  show firstEntrance _ (levelsUpTo n) _ _ = _
  rw [x5nh_fe _ _ _ _ (by simp [levelsUpTo])]
  simp only [levelsUpTo, Set.mem_setOf_eq, not_le]

lemma x5nh_hG (m : ℕ) (i : ι (m + 1)) (j : ι m) : matG (ndqbdP A₀ A₁ A₂) m i j =
    ∑' t, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m + 1, i⟩ (t + 1) ⟨m, j⟩ (fun z => m < z.1) := by
  show firstEntrance _ (level m) _ _ = _
  rw [x5nh_fe _ _ _ _ (by simp [level])]
  refine tsum_congr fun t => x5nh_PS_congr _ (fun z => m < z.1) _ _ _ ?_ _ _ (by simp)
  intro w z hw hz
  have := x5nh_qnz A₀ A₁ A₂ w z hz
  simp only [level, Set.mem_setOf_eq] at hw ⊢
  refine ⟨⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩

lemma x5nh_hst (m : ℕ) : ∀ w y : Σ k, ι k, (fun z : Σ k, ι k => m ≤ z.1) y →
    ndqbdP A₀ A₁ A₂ w y ≠ 0 →
      ((fun z : Σ k, ι k => z.1 = m + 1) w ∧ (fun z : Σ k, ι k => m < z.1) w ∧
          ¬ (fun z : Σ k, ι k => m + 1 < z.1) w) ∨
      ((fun z : Σ k, ι k => m + 1 < z.1) w ∧ (fun z : Σ k, ι k => m < z.1) w ∧
          (fun z : Σ k, ι k => m ≤ z.1) w ∧ ¬ (fun z : Σ k, ι k => z.1 = m + 1) w) ∨
      (¬ (fun z : Σ k, ι k => m < z.1) w ∧ ¬ (fun z : Σ k, ι k => m + 1 < z.1) w ∧
          ¬ (fun z : Σ k, ι k => z.1 = m + 1) w) := by
  intro w y _ _
  simp only
  omega

lemma x5nh_GN (m : ℕ) : matG (ndqbdP A₀ A₁ A₂) m = matMulE (x5nh_N A₀ A₁ A₂ m) (ennMat (A₂ m)) := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  have hb : ∀ (l : ι (m + 1)) (j : ι m) (u : ℕ),
      x5nh_PS P ⟨m + 1, l⟩ (u + 1) ⟨m, j⟩ (fun z => m + 1 < z.1) =
      if u = 0 then ENNReal.ofReal (A₂ m l j) else 0 := by
    intro l j u
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; rw [x5nh_PS_one, if_pos rfl, hPd, x5nh_P2]
    · rw [if_neg (by omega), x5nh_PS_snoc]
      refine ENNReal.tsum_eq_zero.mpr fun w => ?_
      by_cases hw : m + 1 < w.1
      · have : P w ⟨m, j⟩ = 0 := by
          by_contra h; have := x5nh_qnz A₀ A₁ A₂ w ⟨m, j⟩ h; simp at this; omega
        simp [this]
      · rw [if_neg (by omega)]; simp
  funext i j
  rw [x5nh_hG A₀ A₁ A₂ m i j]
  rw [tsum_congr fun t => x5nh_conv3 P (fun z : Σ k, ι k => m ≤ z.1)
    (fun z : Σ k, ι k => z.1 = m + 1) (fun z : Σ k, ι k => m < z.1)
    (fun z : Σ k, ι k => m + 1 < z.1) ⟨m + 1, i⟩ rfl (x5nh_hst A₀ A₁ A₂ m) t ⟨m, j⟩ le_rfl]
  have e : ∀ t, ∑ s ∈ Finset.range (t + 1), ∑' z : Σ k, ι k, (if z.1 = m + 1 then
      x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1) *
        x5nh_PS P z (t + 1 - s) ⟨m, j⟩ (fun z => m + 1 < z.1) else 0) =
      ∑ s ∈ Finset.range (t + 1), ∑' z : Σ k, ι k, (if z.1 = m + 1 then
      x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1) *
        (fun z u => x5nh_PS P z (u + 1) ⟨m, j⟩ (fun z => m + 1 < z.1)) z (t - s) else 0) := by
    intro t
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show t + 1 - s = t - s + 1 by omega]
  rw [tsum_congr e, x5nh_swap0 (fun z : Σ k, ι k => z.1 = m + 1)
    (fun z s => x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1))
    (fun z u => x5nh_PS P z (u + 1) ⟨m, j⟩ (fun z => m + 1 < z.1)), x5nh_levn]
  unfold matMulE ennMat x5nh_N
  refine tsum_congr fun l => ?_
  simp only [hb]
  rw [tsum_eq_single 0 (fun u hu => if_neg hu), if_pos rfl]

lemma x5nh_NS (m : ℕ) : x5nh_N A₀ A₁ A₂ m = seriesInvE (matU (ndqbdP A₀ A₁ A₂) (m + 1)) := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  have hyz : ∀ i j : ι (m + 1),
      x5nh_PS P ⟨m + 1, i⟩ 0 ⟨m + 1, j⟩ (fun z => m < z.1) = matOneE i j := by
    intro i j; rw [x5nh_PS_zero]; simp [matOneE]
  have hconvN : ∀ (i j : ι (m + 1)) t,
      x5nh_PS P ⟨m + 1, i⟩ (t + 1) ⟨m + 1, j⟩ (fun z => m < z.1) =
      ∑ s ∈ Finset.range (t + 1), ∑' z : Σ k, ι k, (if z.1 = m + 1 then
        x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1) *
          (fun z u => x5nh_PS P z (u + 1) ⟨m + 1, j⟩ (fun z => m + 1 < z.1)) z (t - s) else 0) := by
    intro i j t
    rw [x5nh_conv3 P (fun z : Σ k, ι k => m ≤ z.1) (fun z : Σ k, ι k => z.1 = m + 1)
      (fun z : Σ k, ι k => m < z.1) (fun z : Σ k, ι k => m + 1 < z.1) ⟨m + 1, i⟩ rfl
      (x5nh_hst A₀ A₁ A₂ m) t ⟨m + 1, j⟩ (Nat.le_succ m)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show t + 1 - s = t - s + 1 by omega]
  have hNeq : ∀ i j, x5nh_N A₀ A₁ A₂ m i j =
      matOneE i j + ∑' l, x5nh_N A₀ A₁ A₂ m i l * matU P (m + 1) l j := by
    intro i j
    show ∑' t, x5nh_PS P ⟨m + 1, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1) = _
    rw [tsum_eq_zero_add' ENNReal.summable, hyz]
    congr 1
    rw [tsum_congr (hconvN i j), x5nh_swap0 (fun z : Σ k, ι k => z.1 = m + 1)
      (fun z s => x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1))
      (fun z u => x5nh_PS P z (u + 1) ⟨m + 1, j⟩ (fun z => m + 1 < z.1)), x5nh_levn]
    refine tsum_congr fun l => ?_
    rw [x5nh_hU A₀ A₁ A₂ (m + 1) l j]
    rfl
  have hpart : ∀ T (i j : ι (m + 1)), ∑ t ∈ Finset.range (T + 1),
      x5nh_PS P ⟨m + 1, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1) ≤
      matOneE i j + ∑' l, (∑ t ∈ Finset.range T,
        x5nh_PS P ⟨m + 1, i⟩ t ⟨m + 1, l⟩ (fun z => m < z.1)) * matU P (m + 1) l j := by
    intro T i j
    rw [Finset.sum_range_succ', hyz, add_comm (∑ t ∈ Finset.range T, _)]
    gcongr
    rw [Finset.sum_congr rfl fun t _ => hconvN i j t]
    refine (x5nh_swapT (fun z : Σ k, ι k => z.1 = m + 1)
      (fun z s => x5nh_PS P ⟨m + 1, i⟩ s z (fun z => m < z.1))
      (fun z u => x5nh_PS P z (u + 1) ⟨m + 1, j⟩ (fun z => m + 1 < z.1)) T).trans (le_of_eq ?_)
    rw [x5nh_levn]
    refine tsum_congr fun l => ?_
    rw [x5nh_hU A₀ A₁ A₂ (m + 1) l j]
  exact x5nh_seriesInv _ _ (fun i j t => x5nh_PS P ⟨m + 1, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1))
    (fun i j => rfl) hNeq hpart

lemma x5nh_levn' (n : ℕ) (f : (Σ k, ι k) → ℝ≥0∞) (g : ι n → ℝ≥0∞) (hfg : ∀ l, f ⟨n, l⟩ = g l)
    (h0 : ∀ k (l : ι k), k ≠ n → f ⟨k, l⟩ = 0) : ∑' z, f z = ∑' l, g l := by
  rw [ENNReal.tsum_sigma', tsum_eq_single n]
  · exact tsum_congr hfg
  · intro k hk; exact ENNReal.tsum_eq_zero.mpr fun l => h0 k l hk

lemma x5nh_RN (m : ℕ) : matR (ndqbdP A₀ A₁ A₂) m = matMulE (ennMat (A₀ m)) (x5nh_N A₀ A₁ A₂ m) := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  funext i j
  show expVisitsAvoid P (levelsUpTo m) ⟨m, i⟩ ⟨m + 1, j⟩ = _
  rw [x5nh_eva' P _ _ _ (by simp [levelsUpTo]), tsum_eq_zero_add' ENNReal.summable,
    x5nh_PS_zero, if_neg (by simp), zero_add]
  simp_rw [x5nh_PS_cons P ⟨m, i⟩]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  refine x5nh_levn' (m + 1) _ _ (fun l => ?_) (fun k l hk => ?_)
  · rw [hPd, x5nh_P0]
    congr 1
    unfold x5nh_N
    refine tsum_congr fun t => ?_
    rw [if_pos (Or.inr (by simp [levelsUpTo]))]
    simp only [levelsUpTo, Set.mem_setOf_eq, not_le]
  · by_cases hle : k ≤ m
    · rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
      intro t
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht
        rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg]
        intro h; simp only [Sigma.mk.inj_iff] at h; omega
      · rw [if_neg (by simp only [levelsUpTo, Set.mem_setOf_eq, not_not]; omega)]
    · have : P ⟨m, i⟩ ⟨k, l⟩ = 0 := by
        by_contra h; have := x5nh_qnz A₀ A₁ A₂ _ _ h; simp only at this; omega
      simp [this]

lemma x5nh_UAG (n : ℕ) : matU (ndqbdP A₀ A₁ A₂) n =
    ennMat (A₁ n) + matMulE (ennMat (A₀ n)) (matG (ndqbdP A₀ A₁ A₂) n) := by
  classical
  set P := ndqbdP A₀ A₁ A₂ with hPd
  funext i j
  rw [x5nh_hU A₀ A₁ A₂ n i j, ← hPd]
  simp_rw [x5nh_PS_cons P ⟨n, i⟩]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  set F : (Σ k, ι k) → ℝ≥0∞ := fun z => ENNReal.ofReal (P ⟨n, i⟩ z) * ∑' t,
    (if t = 0 ∨ n < z.1 then x5nh_PS P z t ⟨n, j⟩ (fun z => n < z.1) else 0) with hF
  have hsplit : ∑' z, F z = ∑' z, (if z.1 = n then F z else 0) + ∑' z, (if z.1 = n then 0 else F z) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    split_ifs <;> simp
  rw [hsplit, x5nh_levn]
  have h2 : ∑' z, (if z.1 = n then 0 else F z) = ∑' l, ENNReal.ofReal (A₀ n i l) * matG P n l j := by
    refine x5nh_levn' (n + 1) _ _ (fun l => ?_) (fun k l hk => ?_)
    · rw [if_neg (by simp), hF]
      dsimp only
      rw [hPd, x5nh_P0, ← hPd]
      rw [x5nh_hG A₀ A₁ A₂ n l j]
      congr 1
      rw [tsum_eq_zero_add' ENNReal.summable, if_pos (Or.inl rfl), x5nh_PS_zero,
        if_neg (by simp), zero_add]
      refine tsum_congr fun t => ?_
      rw [if_pos (Or.inr (by simp))]
    · by_cases h1 : k = n
      · subst h1; simp
      rw [if_neg h1, hF]
      dsimp only
      by_cases hle : k < n
      · rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
        intro t
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg]
          intro h; simp only [Sigma.mk.inj_iff] at h; omega
        · rw [if_neg (by omega)]
      · have : P ⟨n, i⟩ ⟨k, l⟩ = 0 := by
          by_contra h; have := x5nh_qnz A₀ A₁ A₂ _ _ h; simp only at this; omega
        simp [this]
  rw [h2]
  simp only [Pi.add_apply, ennMat, matMulE]
  congr 1
  rw [tsum_eq_single j]
  · rw [hF]
    dsimp only
    rw [hPd, x5nh_P1, ← hPd]
    simp only [lt_irrefl, or_false]
    rw [tsum_eq_single 0 (fun t ht => if_neg ht), if_pos rfl, x5nh_PS_zero, if_pos rfl, mul_one]
  · intro l hl
    rw [hF]
    dsimp only
    simp only [lt_irrefl, or_false]
    rw [tsum_eq_single 0 (fun t ht => if_neg ht), if_pos rfl, x5nh_PS_zero, if_neg (by simp [hl]),
      mul_zero]

end NHMain

-- ==== Tab ====

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHTab
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_recur (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V)
    (hret : Tendsto (fun t => x5nh_AV P x0 (fun z => z ≠ x0) t) atTop (𝓝 0))
    (hreach : ∀ z, z ≠ x0 → ∃ u, x5nh_PS P x0 u z (fun z => z ≠ x0) ≠ 0) :
    ∀ z, Tendsto (fun t => x5nh_AV P z (fun w => w ≠ x0) t) atTop (𝓝 0) := by
  intro z
  by_cases hz : z = x0
  · subst hz; exact hret
  obtain ⟨u, hu⟩ := hreach z hz
  set c := x5nh_PS P x0 u z (fun z => z ≠ x0) with hc
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((x5nh_PS_le_AV P x0 z _ hz u).trans (x5nh_AV_le_one P hrow x0 _ u))
  have hb : ∀ t, x5nh_AV P z (fun w => w ≠ x0) t ≤ c⁻¹ * x5nh_AV P x0 (fun w => w ≠ x0) (t + u) := by
    intro t
    have h1 := x5nh_AV_concat P (fun w => w ≠ x0) x0 z hz u t
    rw [add_comm u t] at h1
    calc x5nh_AV P z (fun w => w ≠ x0) t = c⁻¹ * (c * x5nh_AV P z (fun w => w ≠ x0) t) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hu hctop, one_mul]
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun t => c⁻¹ * x5nh_AV P x0 (fun w => w ≠ x0) (t + u)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ((Filter.tendsto_add_atTop_iff_nat u).mpr hret)
      (Or.inr (ENNReal.inv_ne_top.mpr hu))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => bot_le) hb

/-- The taboo identity: an invariant measure of finite mass is determined on `A` by its values
off `A`, provided the chain leaves `A` almost surely from every state of `A`. -/
theorem x5nh_taboo (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (ν : V → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (A : V → Prop) [DecidablePred A]
    (hAV : ∀ z, A z → Tendsto (fun t => x5nh_AV P z A t) atTop (𝓝 0)) :
    ∀ y, A y → ν y = ∑' x, if A x then 0 else ν x * ∑' t, x5nh_PS P x (t + 1) y A := by
  classical
  intro y hy
  set a : ℕ → ℝ≥0∞ := fun t => ∑' x, if A x then 0 else ν x * x5nh_PS P x (t + 1) y A with ha
  set r : ℕ → ℝ≥0∞ := fun t => ∑' z, if A z then ν z * x5nh_PS P z t y A else 0 with hr
  have hcons : ∀ t x, x5nh_PS P x (t + 1) y A =
      ∑' z, if A z then ENNReal.ofReal (P x z) * x5nh_PS P z t y A else 0 := by
    intro t x
    rw [x5nh_PS_cons P x t y A]
    refine tsum_congr fun z => ?_
    by_cases hAz : A z
    · rw [if_pos (Or.inr hAz), if_pos hAz]
    · rw [if_neg hAz]
      by_cases ht : t = 0
      · subst ht
        rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg (fun (h : z = y) => hAz (h ▸ hy)), mul_zero]
      · rw [if_neg (by tauto), mul_zero]
  have hstep : ∀ t, r t = a t + r (t + 1) := by
    intro t
    have e1 : r t = ∑' x, ν x * x5nh_PS P x (t + 1) y A := by
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
    · rw [if_pos hy, x5nh_PS_zero, if_pos rfl, mul_one]
    · intro z hz; rw [x5nh_PS_zero, if_neg hz]; simp
  have hsum : ∀ t, ν y = ∑ s ∈ Finset.range t, a s + r t := by
    intro t
    induction t with
    | zero => simp [hr0]
    | succ t ih => rw [ih, hstep t, Finset.sum_range_succ, add_assoc]
  -- the remainder tends to zero (dominated convergence for the counting measure)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    letI : MeasurableSpace V := ⊤
    have hdc := MeasureTheory.tendsto_lintegral_of_dominated_convergence (μ := MeasureTheory.Measure.count)
      (F := fun t z => if A z then ν z * x5nh_AV P z A t else 0) (f := fun _ => 0) ν
      (fun t => measurable_from_top)
      (fun t => Filter.Eventually.of_forall fun z => by
        by_cases hAz : A z
        · simp only [if_pos hAz]
          calc ν z * x5nh_AV P z A t ≤ ν z * 1 := by gcongr; exact x5nh_AV_le_one P hrow z A t
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
    · simp only [if_pos hAz]; gcongr; exact x5nh_PS_le_AV P z y A hy t
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


lemma x5nh_AV_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x : V) (t : ℕ) :
    x5nh_AV P x A t ≤ x5nh_AV P x A' t := by
  classical
  unfold x5nh_AV
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos h, if_pos ⟨h.1, fun i hi => hAA _ (h.2 i hi)⟩]
  · rw [if_neg h]; exact bot_le


lemma x5nh_AVlim [Countable V] [DecidableEq V] (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (hpos : ∀ x : V, PositiveRecurrent P x) :
    ∀ x0 z, Tendsto (fun t => x5nh_AV P z (fun w => w ≠ x0) t) atTop (𝓝 0) := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  have hconv : ∀ (x0 : V) T, ENNReal.ofReal (returnTailC P x0 T) =
      x5nh_AV P x0 (fun z => z ≠ x0) T := by
    intro x0 T
    have hAVle : x5nh_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
      le_self_add.trans_eq (x5nh_mass P hrow x0 _ T)
    unfold returnTailC setAvoidTailC
    rw [x5nh_ofReal_tsum]
    · unfold x5nh_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5nh_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
    · intro ω; split_ifs
      · exact Finset.prod_nonneg fun s _ => hP0 _ _
      · exact le_rfl
    · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
      unfold x5nh_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC x5nh_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
  intro x0
  apply x5nh_recur P hrow x0
  · have h1 : Tendsto (fun t => returnTailC P x0 t) atTop (𝓝 0) := (hpos x0).tendsto_atTop_zero
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simp only [ENNReal.ofReal_zero] at h2
    refine h2.congr fun t => ?_
    simp [Function.comp_def, hconv]
  · intro z hz
    obtain ⟨t, ht⟩ := hirr x0 z
    exact x5nh_taboo_extract P x0 z hz t (x5nh_stepPow_PS P hP0 t x0 z ht)


end NHTab

-- ==== Lim ====

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHLim
variable {V : Type*} (P : V → V → ℝ)

lemma x5nh_hasSum_of_ennreal {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (h : ∑' a, ENNReal.ofReal (f a) = 1) : HasSum f 1 := by
  have hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤ := by rw [h]; exact ENNReal.one_ne_top
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  have h2 := x5nh_ofReal_tsum f hf hne
  rw [h] at h2
  have h3 : ∑' a, f a = 1 := by
    have := congrArg ENNReal.toReal h2
    simpa [ENNReal.toReal_ofReal (tsum_nonneg hf)] using this
  exact h3 ▸ hs.hasSum

lemma x5nh_P_le_one (hP : IsStochasticC P) (x y : V) : P x y ≤ 1 :=
  le_hasSum (hP.2 x) y (fun z _ => hP.1 x z)

lemma x5nh_summ_mul [Countable V] [DecidableEq V] (hP : IsStochasticC P) (s : V → ℝ)
    (hs0 : ∀ z, 0 ≤ s z) (hs : Summable s) (y : V) : Summable fun z => s z * P z y :=
  Summable.of_nonneg_of_le (fun z => mul_nonneg (hs0 z) (hP.1 z y))
    (fun z => mul_le_of_le_one_right (hs0 z) (x5nh_P_le_one P hP z y)) hs

lemma x5nh_stepPow_hasSum [Countable V] [DecidableEq V] (hP : IsStochasticC P) :
    ∀ t x, HasSum (fun y => stepPow P t x y) 1 := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  intro t
  induction t with
  | zero =>
    intro x
    simp only [stepPow]
    exact hasSum_ite_eq x 1
  | succ t ih =>
    intro x
    have hs0 := x5nh_stepPow_nonneg P hP0 t x
    refine x5nh_hasSum_of_ennreal _ (x5nh_stepPow_nonneg P hP0 (t + 1) x) ?_
    simp only [stepPow]
    have e : ∀ y, ENNReal.ofReal (∑' z, stepPow P t x z * P z y) =
        ∑' z, ENNReal.ofReal (stepPow P t x z) * ENNReal.ofReal (P z y) := by
      intro y
      rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hs0 z) (hP0 z y))
        (x5nh_summ_mul P hP _ hs0 (ih x).summable y)]
      exact tsum_congr fun z => ENNReal.ofReal_mul (hs0 z)
    simp_rw [e]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hrow, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hs0 (ih x).summable, (ih x).tsum_eq, ENNReal.ofReal_one]

lemma x5nh_limit_stat [Countable V] [DecidableEq V] [Nonempty V] (hP : IsStochasticC P)
    (π : V → ℝ) (hlim : ∀ x y, Tendsto (fun t => stepPow P t x y) atTop (𝓝 (π y))) :
    (∀ y, 0 ≤ π y) ∧ (∑' y, ENNReal.ofReal (π y) ≤ 1) ∧
      ∀ y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) = ENNReal.ofReal (π y) := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  set x0 : V := Classical.arbitrary V
  have hnn : ∀ y, 0 ≤ π y := fun y =>
    ge_of_tendsto (hlim x0 y) (Eventually.of_forall fun t => x5nh_stepPow_nonneg P hP0 t x0 y)
  have hmass : ∑' y, ENNReal.ofReal (π y) ≤ 1 := by
    refine ENNReal.summable.tsum_le_of_sum_le fun F => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hnn y), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_of_tendsto' (tendsto_finset_sum F fun y _ => hlim x0 y) fun t => ?_
    exact sum_le_hasSum F (fun y _ => x5nh_stepPow_nonneg P hP0 t x0 y)
      (x5nh_stepPow_hasSum P hP t x0)
  have hsup : ∀ y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) ≤ ENNReal.ofReal (π y) := by
    intro y
    refine ENNReal.summable.tsum_le_of_sum_le fun F => ?_
    have e : ∑ x ∈ F, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) =
        ENNReal.ofReal (∑ x ∈ F, π x * P x y) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (hnn x) (hP0 x y))]
      exact Finset.sum_congr rfl fun x _ => (ENNReal.ofReal_mul (hnn x)).symm
    rw [e]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Tendsto (fun t => ∑ x ∈ F, stepPow P t x0 x * P x y) atTop
        (𝓝 (∑ x ∈ F, π x * P x y)) :=
      tendsto_finset_sum F fun x _ => (hlim x0 x).mul_const _
    have h2 : Tendsto (fun t => stepPow P (t + 1) x0 y) atTop (𝓝 (π y)) :=
      (hlim x0 y).comp (tendsto_add_atTop_nat 1)
    refine le_of_tendsto_of_tendsto' h1 h2 fun t => ?_
    have hs0 := x5nh_stepPow_nonneg P hP0 t x0
    show _ ≤ ∑' z, stepPow P t x0 z * P z y
    exact (x5nh_summ_mul P hP _ hs0 (x5nh_stepPow_hasSum P hP t x0).summable y).sum_le_tsum F
      (fun z _ => mul_nonneg (hs0 z) (hP0 z y))
  refine ⟨hnn, hmass, fun y => ?_⟩
  by_contra hne
  have hlt := lt_of_le_of_ne (hsup y) hne
  have hfin : ∑' y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) ≠ ⊤ := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hrow, mul_one]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hmass
  have := ENNReal.tsum_lt_tsum hfin hsup hlt
  rw [ENNReal.tsum_comm] at this
  simp_rw [ENNReal.tsum_mul_left, hrow, mul_one] at this
  exact lt_irrefl _ this

/-- uniform bound by the diagonal entry -/
lemma x5nh_N_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (y : V) (hy : A y)
    (x : V) : ∑' t, x5nh_PS P x t y A ≤ ∑' t, x5nh_PS P y t y A := by
  classical
  by_cases hxy : x = y
  · subst hxy; exact le_rfl
  rw [tsum_congr fun L => x5nh_fv P A y hy L x hxy,
    x5nh_cauchy0 (fun s => x5nh_PS P x s y (fun z => A z ∧ z ≠ y)) (fun u => x5nh_PS P y u y A)]
  refine (mul_le_of_le_one_left bot_le ?_)
  rw [tsum_eq_zero_add' ENNReal.summable, x5nh_PS_zero, if_neg hxy, zero_add]
  exact x5nh_sum_PS_le P hrow x y _ (by simp)

end NHLim

section NHLimQ
variable {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ)

lemma x5nh_R_eq (m : ℕ) (i : ι m) (j : ι (m + 1)) : matR (ndqbdP A₀ A₁ A₂) m i j =
    ∑' t, x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨m, i⟩ t ⟨m + 1, j⟩ (fun z => m < z.1) := by
  show expVisitsAvoid _ (levelsUpTo m) _ _ = _
  rw [x5nh_eva' _ _ _ _ (by simp [levelsUpTo])]
  simp only [levelsUpTo, Set.mem_setOf_eq, not_le]

lemma x5nh_low (m k : ℕ) (hk : k < m) (l : ι k) (j : ι (m + 1)) (t : ℕ) :
    x5nh_PS (ndqbdP A₀ A₁ A₂) ⟨k, l⟩ (t + 1) ⟨m + 1, j⟩ (fun z => m < z.1) = 0 := by
  classical
  rw [x5nh_PS_cons]
  refine ENNReal.tsum_eq_zero.mpr fun z => ?_
  by_cases hP0 : ndqbdP A₀ A₁ A₂ ⟨k, l⟩ z = 0
  · simp [hP0]
  have := x5nh_qnz A₀ A₁ A₂ _ _ hP0
  simp only at this
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rw [if_pos (Or.inl rfl), x5nh_PS_zero, if_neg, mul_zero]
    rintro rfl; simp only at this; omega
  · rw [if_neg (by rintro (h | h) <;> omega), mul_zero]

end NHLimQ

-- ==== Rec ====

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

section NHRec
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma x5nh_AV_cons (z : V) (A : V → Prop) (t : ℕ) :
    x5nh_AV P z A (t + 1) =
      ∑' w, ENNReal.ofReal (P z w) * (if A w then x5nh_AV P w A t else 0) := by
  classical
  rw [x5nh_AV_eq]
  simp_rw [x5nh_PS_cons P z t]
  simp_rw [x5nh_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun w => ?_
  have e : ∀ y, (if A y then ENNReal.ofReal (P z w) *
      (if t = 0 ∨ A w then x5nh_PS P w t y A else 0) else 0) =
      ENNReal.ofReal (P z w) * (if A y then (if t = 0 ∨ A w then x5nh_PS P w t y A else 0)
        else 0) := by
    intro y; split_ifs <;> simp
  simp_rw [e, ENNReal.tsum_mul_left]
  congr 1
  rcases t with _ | s
  · simp only [true_or, if_true, x5nh_PS_zero, x5nh_AV_zero]
    rw [tsum_eq_single w]
    · by_cases hw : A w <;> simp [hw]
    · intro y hy; simp [Ne.symm hy]
  · by_cases hw : A w
    · simp only [hw, or_true, if_true]
      rw [x5nh_AV_eq]
    · simp [hw]

lemma x5nh_AV_cons' (z : V) (A : V → Prop) [DecidablePred A] (t : ℕ) :
    x5nh_AV P z A (t + 1) =
      ∑' w, ENNReal.ofReal (P z w) * (if A w then x5nh_AV P w A t else 0) := by
  rw [x5nh_AV_cons]
  refine tsum_congr fun w => ?_
  congr 1
  split_ifs <;> rfl

/-- the exit mass: if the chain leaves `A` a.s., the exit distribution has mass one -/
lemma x5nh_exit_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) :
    Tendsto (fun t => x5nh_AV P x A t) atTop (𝓝 0) ↔ ∑' k, x5nh_EX P x A (k + 1) = 1 := by
  have hm := x5nh_mass P hrow x A
  have hS : Tendsto (fun t => ∑ k ∈ Finset.range t, x5nh_EX P x A (k + 1)) atTop
      (𝓝 (∑' k, x5nh_EX P x A (k + 1))) := ENNReal.tendsto_nat_tsum _
  have hAV : ∀ t, x5nh_AV P x A t = 1 - ∑ k ∈ Finset.range t, x5nh_EX P x A (k + 1) := by
    intro t
    rw [← hm t, ENNReal.add_sub_cancel_right]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq (hm t))
  constructor
  · intro h
    have h2 : Tendsto (fun t => 1 - x5nh_AV P x A t) atTop (𝓝 (1 - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at h2
    refine tendsto_nhds_unique hS (h2.congr fun t => ?_)
    rw [hAV t, ENNReal.sub_sub_cancel ENNReal.one_ne_top]
    rw [← hm t]; exact le_add_self
  · intro h
    rw [h] at hS
    have h2 : Tendsto (fun t => 1 - ∑ k ∈ Finset.range t, x5nh_EX P x A (k + 1)) atTop
        (𝓝 (1 - 1)) := ENNReal.Tendsto.sub tendsto_const_nhds hS (Or.inl ENNReal.one_ne_top)
    rw [tsub_self] at h2
    exact h2.congr fun t => (hAV t).symm

open Classical in
/-- first entrance into a set `F`, inequality form -/
lemma x5nh_fvset (F : V → Prop) (y : V) :
    ∀ L x, ∑ s ∈ Finset.range (L + 1), ∑' w, (if F w then
        x5nh_PS P x (s + 1) w (fun v => ¬ F v) * x5nh_PS P w (L - s) y (fun _ => True) else 0) ≤
      x5nh_PS P x (L + 1) y (fun _ => True) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, x5nh_PS_zero,
      x5nh_PS_one]
    rw [tsum_eq_single y]
    · split_ifs <;> simp
    · intro w hw; simp [hw]
  | succ L ih =>
    intro x
    rw [Finset.sum_range_succ', x5nh_PS_cons P x (L + 1) y]
    have hs : ∀ s, ∑' w, (if F w then
        x5nh_PS P x (s + 1 + 1) w (fun v => ¬ F v) * x5nh_PS P w (L + 1 - (s + 1)) y (fun _ => True)
        else 0) =
        ∑' v, ENNReal.ofReal (P x v) * (if ¬ F v then ∑' w, (if F w then
          x5nh_PS P v (s + 1) w (fun v => ¬ F v) * x5nh_PS P w (L - s) y (fun _ => True)
          else 0) else 0) := by
      intro s
      rw [show L + 1 - (s + 1) = L - s by omega]
      simp_rw [x5nh_PS_cons P x (s + 1) _ (fun v => ¬ F v)]
      have e : ∀ w, (if F w then (∑' v, ENNReal.ofReal (P x v) * (if s + 1 = 0 ∨ ¬ F v then
          x5nh_PS P v (s + 1) w (fun v => ¬ F v) else 0)) *
          x5nh_PS P w (L - s) y (fun _ => True) else 0) =
          ∑' v, ENNReal.ofReal (P x v) * (if ¬ F v then (if F w then
            x5nh_PS P v (s + 1) w (fun v => ¬ F v) * x5nh_PS P w (L - s) y (fun _ => True)
            else 0) else 0) := by
        intro w
        by_cases hw : F w
        · simp only [hw, if_true, ← ENNReal.tsum_mul_right]
          refine tsum_congr fun v => ?_
          by_cases hv : F v
          · simp [hv]
          · simp [hv, mul_assoc]
        · simp [hw]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun v => ?_
      rw [ENNReal.tsum_mul_left]
      by_cases hv : F v
      · simp [hv]
      · simp only [hv, not_false_eq_true, if_true]
    have hA : ∑ s ∈ Finset.range (L + 1), ∑' w, (if F w then
        x5nh_PS P x (s + 1 + 1) w (fun v => ¬ F v) * x5nh_PS P w (L + 1 - (s + 1)) y (fun _ => True)
        else 0) =
        ∑' v, ENNReal.ofReal (P x v) * (if ¬ F v then ∑ s ∈ Finset.range (L + 1), ∑' w, (if F w then
          x5nh_PS P v (s + 1) w (fun v => ¬ F v) * x5nh_PS P w (L - s) y (fun _ => True)
          else 0) else 0) := by
      simp_rw [hs]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr fun v => ?_
      rw [← Finset.mul_sum]
      by_cases hv : F v
      · simp [hv]
      · simp only [hv, not_false_eq_true, if_true]
    have hB : ∑' w, (if F w then x5nh_PS P x (0 + 1) w (fun v => ¬ F v) *
        x5nh_PS P w (L + 1 - 0) y (fun _ => True) else 0) =
        ∑' v, ENNReal.ofReal (P x v) * (if F v then x5nh_PS P v (L + 1) y (fun _ => True) else 0) := by
      refine tsum_congr fun v => ?_
      rw [zero_add, x5nh_PS_one, Nat.sub_zero]
      split_ifs <;> simp
    rw [hA, hB, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun v => ?_
    rw [← mul_add]
    gcongr
    simp only [or_true, if_true]
    by_cases hv : F v
    · simp [hv]
    · simp only [hv, not_false_eq_true, if_true, if_false, add_zero]
      exact ih v

lemma x5nh_hconv [Countable V] [DecidableEq V] (hP : IsStochasticC P) (x0 : V) (T : ℕ) :
    ENNReal.ofReal (returnTailC P x0 T) = x5nh_AV P x0 (fun z => z ≠ x0) T := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  have hAVle : x5nh_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
    le_self_add.trans_eq (x5nh_mass P hrow x0 _ T)
  unfold returnTailC setAvoidTailC
  rw [x5nh_ofReal_tsum]
  · unfold x5nh_AV
    refine tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · unfold pathWeightC x5nh_W
      exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
    · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
    · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
    · simp
  · intro ω; split_ifs
    · exact Finset.prod_nonneg fun s _ => hP0 _ _
    · exact le_rfl
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
    unfold x5nh_AV
    refine tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · unfold pathWeightC x5nh_W
      exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
    · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
    · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
    · simp

lemma x5nh_rec_iff [Countable V] [DecidableEq V] (hP : IsStochasticC P) (x : V) :
    Recurrent P x ↔ Tendsto (fun t => x5nh_AV P x (fun z => z ≠ x) t) atTop (𝓝 0) := by
  have hnn : ∀ t, 0 ≤ returnTailC P x t := by
    intro t
    unfold returnTailC setAvoidTailC
    refine tsum_nonneg fun ω => ?_
    split_ifs
    · exact Finset.prod_nonneg fun s _ => hP.1 _ _
    · exact le_rfl
  constructor
  · intro h
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
    simp only [ENNReal.ofReal_zero] at h2
    exact h2.congr fun t => x5nh_hconv P hP x t
  · intro h
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simp only [ENNReal.toReal_zero] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp_apply]
    rw [← x5nh_hconv P hP x t, ENNReal.toReal_ofReal (hnn t)]

open Classical in
/-- if the chain returns a.s. to a finite set `F`, the expected number of visits to `F` is
infinite -/
lemma x5nh_visits_top (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (F : Finset V)
    (hret : ∀ z ∈ F, Tendsto (fun t => x5nh_AV P z (fun v => v ∉ F) t) atTop (𝓝 0)) :
    ∀ z ∈ F, ∑ y ∈ F, ∑' t, x5nh_PS P z t y (fun _ => True) = ⊤ := by
  classical
  set g : V → ℝ≥0∞ := fun z => ∑ y ∈ F, ∑' t, x5nh_PS P z t y (fun _ => True) with hg
  set K : V → V → ℝ≥0∞ := fun z w => ∑' s, x5nh_PS P z (s + 1) w (fun v => v ∉ F) with hK
  have hK1 : ∀ z ∈ F, ∑' w, (if w ∈ F then K z w else 0) = 1 := by
    intro z hz
    rw [← (x5nh_exit_mass P hrow z _).mp (hret z hz)]
    simp_rw [x5nh_EX_eq]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun w => ?_
    by_cases hw : w ∈ F
    · simp [hw, hK]
    · simp [hw]
  have hN : ∀ z y, (if z = y then 1 else 0) +
      ∑' w, (if w ∈ F then K z w * ∑' u, x5nh_PS P w u y (fun _ => True) else 0) ≤
      ∑' t, x5nh_PS P z t y (fun _ => True) := by
    intro z y
    rw [tsum_eq_zero_add' ENNReal.summable, x5nh_PS_zero]
    gcongr
    rw [← x5nh_swap0 (fun w => w ∈ F) (fun w s => x5nh_PS P z (s + 1) w (fun v => v ∉ F))
      (fun w u => x5nh_PS P w u y (fun _ => True))]
    refine ENNReal.tsum_le_tsum fun L => ?_
    convert x5nh_fvset P (fun w => w ∈ F) y L z using 3 with s hs
    funext w
    congr 1
  have hstep : ∀ z ∈ F, 1 + ∑' w, (if w ∈ F then K z w * g w else 0) ≤ g z := by
    intro z hz
    rw [hg]
    dsimp only
    calc 1 + ∑' w, (if w ∈ F then K z w * ∑ y ∈ F, ∑' t, x5nh_PS P w t y (fun _ => True) else 0)
        = ∑ y ∈ F, ((if z = y then 1 else 0) +
            ∑' w, (if w ∈ F then K z w * ∑' u, x5nh_PS P w u y (fun _ => True) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq F z, if_pos hz]
          congr 1
          rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          refine tsum_congr fun w => ?_
          split_ifs
          · rw [Finset.mul_sum]
          · simp
      _ ≤ _ := Finset.sum_le_sum fun y _ => hN z y
  have hn : ∀ n : ℕ, ∀ z ∈ F, (n : ℝ≥0∞) ≤ g z := by
    intro n
    induction n with
    | zero => intro z _; simp
    | succ n ih =>
      intro z hz
      refine le_trans ?_ (hstep z hz)
      calc ((n + 1 : ℕ) : ℝ≥0∞) = 1 + (n : ℝ≥0∞) * 1 := by push_cast; ring
        _ = 1 + (n : ℝ≥0∞) * ∑' w, (if w ∈ F then K z w else 0) := by rw [hK1 z hz]
        _ ≤ _ := by
          gcongr
          rw [← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun w => ?_
          split_ifs with hw
          · rw [mul_comm]; gcongr; exact ih w hw
          · simp
  intro z hz
  by_contra hne
  obtain ⟨n, hn'⟩ := ENNReal.exists_nat_gt hne
  exact absurd (hn n z hz) (not_le.mpr hn')

/-- Green criterion: infinitely many expected visits to `y` force recurrence of `y` -/
lemma x5nh_rec_of_top (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V)
    (h : ∑' t, x5nh_PS P x t y (fun _ => True) = ⊤) :
    Tendsto (fun t => x5nh_AV P y (fun z => z ≠ y) t) atTop (𝓝 0) := by
  classical
  have hanti : Antitone fun t => x5nh_AV P y (fun z => z ≠ y) t :=
    antitone_nat_of_succ_le fun t => x5nh_AV_anti P hrow y _ t
  have hlim := tendsto_atTop_iInf hanti
  set c := ⨅ t, x5nh_AV P y (fun z => z ≠ y) t with hc
  by_cases hc0 : c = 0
  · rwa [hc0] at hlim
  exfalso
  have hA' : (fun z : V => True ∧ z ≠ y) = (fun z => z ≠ y) := by funext z; simp
  have hc1 : c ≤ 1 := (iInf_le _ 0).trans (x5nh_AV_le_one P hrow y _ 0)
  have hq : ∑' u, x5nh_PS P y (u + 1) y (fun z => True ∧ z ≠ y) < 1 := by
    rw [hA']
    refine lt_of_le_of_lt (b := 1 - c) ?_ (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc0)
    refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
    have hm := x5nh_mass P hrow y (fun z => z ≠ y) t
    have e : ∀ k, x5nh_EX P y (fun z => z ≠ y) (k + 1) = x5nh_PS P y (k + 1) y (fun z => z ≠ y) := by
      intro k
      rw [x5nh_EX_eq, tsum_eq_single y]
      · simp
      · intro w hw; simp [hw]
    simp_rw [e] at hm
    rw [← hm]
    exact ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ENNReal.one_ne_top hc1)
      (by gcongr; exact iInf_le _ t)
  have hd := x5nh_diag P hrow (fun _ => True) y trivial hq
  exact hd (top_le_iff.mp (h ▸ x5nh_N_le P hrow (fun _ => True) y trivial x))

/-- class property of infinite Green function -/
lemma x5nh_top_all [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) (hirr : IrreducibleC P)
    (w : V) (hw : ∑' t, x5nh_PS P w t w (fun _ => True) = ⊤) (x : V) :
    ∑' t, x5nh_PS P x t x (fun _ => True) = ⊤ := by
  classical
  obtain ⟨a, ha⟩ := hirr x w
  obtain ⟨b, hb⟩ := hirr w x
  have ha' := x5nh_stepPow_PS P hP0 a x w ha
  have hb' := x5nh_stepPow_PS P hP0 b w x hb
  have hle : x5nh_PS P x a w (fun _ => True) * (∑' t, x5nh_PS P w t w (fun _ => True)) *
      x5nh_PS P w b x (fun _ => True) ≤ ∑' t, x5nh_PS P x t x (fun _ => True) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective
      (f := fun t => a + t + b) (fun s t h => by simp only at h; omega) _)
    refine ENNReal.tsum_le_tsum fun t => ?_
    refine le_trans ?_ (x5nh_PS_concat P (fun _ => True) w x trivial (a + t) x b)
    gcongr
    exact x5nh_PS_concat P (fun _ => True) w w trivial a x t
  rw [hw, ENNReal.mul_top ha', ENNReal.top_mul hb', top_le_iff] at hle
  exact hle

end NHRec

-- ==== Sol3 ====

open scoped ENNReal
open MatrixAnalytic.Nonhomogeneous
open Filter Topology

lemma x5nh_tsum_fin {α : Type*} [Fintype α] (f : α → ℝ≥0∞) : ∑' a, f a = ∑ a, f a :=
  tsum_eq_sum (fun a ha => absurd (Finset.mem_univ a) ha)

theorem solution {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ) (P : (Σ n, ι n) → (Σ n, ι n) → ℝ)
    (hPdef : P = ndqbdP A₀ A₁ A₂)
    (hP : IsStochasticC P) (hirr : IrreducibleC P) :
    (∀ x : Σ n, ι n, Recurrent P x) ↔ ∀ i : ι 1, ∑ j : ι 0, matG P 0 i j = 1 := by
  classical
  subst hPdef
  set P := ndqbdP A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  set A : (Σ k, ι k) → Prop := fun z => z ∉ level 0 with hA
  have hGsum : ∀ i : ι 1, ∑ j : ι 0, matG P 0 i j = ∑' k, x5nh_EX P ⟨1, i⟩ A (k + 1) := by
    intro i
    simp_rw [x5nh_EX_eq]
    rw [ENNReal.tsum_comm, ← x5nh_tsum_fin]
    have e : ∀ (y : Σ k, ι k) (inst : Decidable (¬ A y)),
        (∑' k, @ite _ (¬ A y) inst (x5nh_PS P ⟨1, i⟩ (k + 1) y A) 0) =
        if y.1 = 0 then ∑' k, x5nh_PS P ⟨1, i⟩ (k + 1) y A else 0 := by
      intro y inst
      have : (¬ A y) ↔ y.1 = 0 := by simp [hA, level]
      by_cases hy : y.1 = 0
      · simp only [this.mpr hy, hy, if_true, not_false_eq_true]
      · simp only [show ¬ ¬ A y from fun h => hy (this.mp h), hy, if_false, tsum_zero]
    refine Eq.trans ?_ (tsum_congr fun y => e y _).symm
    rw [x5nh_levn]
    refine tsum_congr fun j => ?_
    show firstEntrance _ (level 0) _ _ = _
    rw [x5nh_fe _ _ _ _ (by simp [level])]
  let x0 : Σ k, ι k := ⟨0, Classical.arbitrary _⟩
  constructor
  · intro hrec i
    have hret := (x5nh_rec_iff P hP x0).mp (hrec x0)
    have hall := x5nh_recur P hrow x0 hret (fun z hz => by
      obtain ⟨t, ht⟩ := hirr x0 z
      exact x5nh_taboo_extract P x0 z hz t (x5nh_stepPow_PS P hP0 t x0 z ht))
    have h1 : Tendsto (fun t => x5nh_AV P ⟨1, i⟩ A t) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hall ⟨1, i⟩)
        (fun t => bot_le) fun t => x5nh_AV_mono P _ _ (fun w hw h => ?_) _ t
      exact hw (by rw [h]; simp [level, x0])
    rw [hGsum, ← (x5nh_exit_mass P hrow _ A).mp h1]
  · intro hG
    have h1 : ∀ i : ι 1, Tendsto (fun t => x5nh_AV P ⟨1, i⟩ A t) atTop (𝓝 0) := fun i =>
      (x5nh_exit_mass P hrow _ A).mpr ((hGsum i).symm.trans (hG i))
    set F : Finset (Σ k, ι k) := Finset.univ.image (fun j : ι 0 => (⟨0, j⟩ : Σ k, ι k)) with hF
    have hFm : ∀ v : Σ k, ι k, v ∈ F ↔ v ∈ level 0 := by
      intro v
      obtain ⟨k, l⟩ := v
      simp only [hF, Finset.mem_image, Finset.mem_univ, true_and, level, Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, hj⟩; exact (congrArg Sigma.fst hj).symm
      · intro hk; subst hk; exact ⟨l, rfl⟩
    have hAF : (fun v => v ∉ F) = A := by funext v; simp [hA, hFm]
    have hret : ∀ z ∈ F, Tendsto (fun t => x5nh_AV P z (fun v => v ∉ F) t) atTop (𝓝 0) := by
      intro z hz
      rw [hAF]
      obtain ⟨k, l⟩ := z
      have hk : k = 0 := by have := (hFm _).mp hz; simpa [level] using this
      subst hk
      refine (tendsto_add_atTop_iff_nat 1).mp ?_
      simp_rw [x5nh_AV_cons' P _ A]
      have e : ∀ t, (∑' w, ENNReal.ofReal (P ⟨0, l⟩ w) * (if A w then x5nh_AV P w A t else 0)) =
          ∑ m : ι 1, ENNReal.ofReal (P ⟨0, l⟩ ⟨1, m⟩) * x5nh_AV P ⟨1, m⟩ A t := by
        intro t
        rw [← x5nh_tsum_fin]
        refine x5nh_levn' 1 _ _ (fun m => ?_) (fun k m hk => ?_)
        · rw [if_pos (by simp [hA, level])]
        · by_cases h0 : k = 0
          · subst h0; rw [if_neg (by simp [hA, level])]; simp
          · have : P ⟨0, l⟩ ⟨k, m⟩ = 0 := by
              by_contra h; have := x5nh_qnz A₀ A₁ A₂ _ _ h; simp only at this; omega
            simp [this]
      simp_rw [e]
      have := tendsto_finset_sum (Finset.univ : Finset (ι 1)) fun m _ =>
        ENNReal.Tendsto.const_mul (h1 m) (Or.inr (ENNReal.ofReal_ne_top (r := P ⟨0, l⟩ ⟨1, m⟩)))
      simpa using this
    have hx0 : x0 ∈ F := (hFm x0).mpr rfl
    have htop := x5nh_visits_top P hrow F hret x0 hx0
    obtain ⟨y, hyF, hy⟩ := ENNReal.sum_eq_top.mp htop
    have hyy : ∑' t, x5nh_PS P y t y (fun _ => True) = ⊤ :=
      top_le_iff.mp (hy ▸ x5nh_N_le P hrow (fun _ => True) y trivial x0)
    intro x
    exact (x5nh_rec_iff P hP x).mpr
      (x5nh_rec_of_top P hrow x x (x5nh_top_all P hP0 hirr y hyy x))

