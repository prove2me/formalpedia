-- Prove2me | solution 1 for MatrixAnalytic.Taboo.restricted_chain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:15:37.152135+00:00
-- url     : https://prove2.me/submissions/1f144efb-20a7-4e2c-88ad-049720dfc50e

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices
import Definitions.Def_MatrixAnalytic_Taboo_Restricted

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace S202TB
open MatrixAnalytic.Taboo

def Recurrent {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (x : V) : Prop :=
  Filter.Tendsto (fun t => returnTailC P x t) Filter.atTop (nhds 0)


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

lemma g72mab_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    g72mab_PS P x k y A ≤ g72mab_EX P x A k := by
  classical
  unfold g72mab_PS g72mab_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma g72mab_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, g72mab_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← g72mab_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => g72mab_PS_le_EX P x y A hy (k + 1)).trans le_add_self

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

/-- last-visit decomposition -/
lemma g72mab_conv3 (InvT mid A A' : V → Prop) [DecidablePred mid] (x : V) (hx : mid x)
    (hstep : ∀ w y, InvT y → P w y ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ InvT w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ L y, InvT y → g72mab_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) y A' else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [g72mab_PS_one]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, g72mab_PS_one]
    rw [tsum_eq_single x]
    · rw [if_pos hx, g72mab_PS_zero, if_pos rfl, one_mul]
    · intro z hz
      rw [g72mab_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ L ih =>
    intro y hy
    rw [Finset.sum_range_succ, g72mab_PS_snoc P x (L + 1)]
    have hlast : ∀ z, (if mid z then g72mab_PS P x (L + 1) z A *
        g72mab_PS P z (L + 1 + 1 - (L + 1)) y A' else 0) =
        if mid z then g72mab_PS P x (L + 1) z A * ENNReal.ofReal (P z y) else 0 := fun z => by
      rw [show L + 1 + 1 - (L + 1) = 1 by omega, g72mab_PS_one]
    simp_rw [hlast]
    have h1 : ∀ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        g72mab_PS P x s z A * g72mab_PS P z (L + 1 + 1 - s) y A' else 0) =
        ∑' w, (if A' w then ∑' z, (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
      intro s hs
      have hs' : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have e : ∀ z, (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 + 1 - s) y A' else 0) =
          ∑' w, (if A' w then (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
        intro z
        rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, g72mab_PS_snoc P z (L + 1 - s)]
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

lemma g72mab_cauchy0 (a b : ℕ → ℝ≥0∞) :
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
lemma g72mab_levn {ι : Type*} (n : ℕ) (f : ℕ × ι → ℝ≥0∞) :
    ∑' z : ℕ × ι, (if z.1 = n then f z else 0) = ∑' l, f (n, l) := by
  rw [ENNReal.tsum_prod', tsum_eq_single n]
  · simp
  · intro m hm; simp [hm]
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

open Classical in
lemma g72mab_AV_eq (x : V) (A : V → Prop) (k : ℕ) :
    g72mab_AV P x A (k + 1) = ∑' y, if A y then g72mab_PS P x (k + 1) y A else 0 := by
  classical
  unfold g72mab_AV g72mab_PS
  simp_rw [g72mab_ite_tsum]
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

lemma g72mab_PS_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x y : V) (L : ℕ) :
    g72mab_PS P x L y A ≤ g72mab_PS P x L y A' := by
  classical
  unfold g72mab_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, fun m h1 h2 => hAA _ (h.2.2 m h1 h2)⟩]
  · rw [if_neg h]; exact bot_le

lemma g72mab_PS_concat (A : V → Prop) (y z : V) (hy : A y) :
    ∀ u x t, g72mab_PS P x u y A * g72mab_PS P y t z A ≤ g72mab_PS P x (u + t) z A := by
  classical
  intro u
  induction u with
  | zero =>
    intro x t
    rw [g72mab_PS_zero, zero_add]
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]; exact bot_le
  | succ u ih =>
    intro x t
    rw [g72mab_PS_cons P x u y A, show u + 1 + t = (u + t) + 1 by omega,
      g72mab_PS_cons P x (u + t) z A, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [mul_assoc]
    gcongr
    by_cases hw : A w
    · rw [if_pos (Or.inr hw), if_pos (Or.inr hw)]; exact ih w t
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg (fun h => hw (by rw [h]; exact hy)), zero_mul]
        exact bot_le
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hw h]), zero_mul]; exact bot_le

lemma g72mab_taboo_extract (x0 y : V) (hy : y ≠ x0) (L : ℕ)
    (h : g72mab_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ u, g72mab_PS P x0 u y (fun z => z ≠ x0) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [g72mab_PS_zero, if_neg (Ne.symm hy)] at h; exact absurd rfl h
  rw [g72mab_conv3 P (fun _ => True) (fun z => z = x0) (fun _ => True) (fun z => z ≠ x0) x0 rfl
    (fun w _ _ _ => by by_cases hw : w = x0 <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if z = x0 then g72mab_PS P x0 s z (fun _ => True) *
      g72mab_PS P z (L + 1 - s) y (fun z => z ≠ x0) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzx : z = x0
  · rw [if_pos hzx] at hz
    subst hzx
    exact ⟨_, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzx] at hz; exact absurd rfl hz

lemma g72mab_ofReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  exact ENNReal.ofReal_tsum_of_nonneg hf hs
end GRK
lemma g72mab_stepPow_nonneg {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) : ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih => intro x y; simp only [stepPow]; exact tsum_nonneg fun z => mul_nonneg (ih _ _) (hP0 _ _)

lemma g72mab_stepPow_PS {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) (x : V) :
    ∀ t y, 0 < stepPow P t x y → g72mab_PS P x t y (fun _ => True) ≠ 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro y h
    simp only [stepPow] at h
    rw [g72mab_PS_zero]
    split_ifs at h with hxy
    · simp [hxy]
    · norm_num at h
  | succ t ih =>
    intro y h
    simp only [stepPow] at h
    obtain ⟨z, hz⟩ : ∃ z, stepPow P t x z * P z y ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [tsum_congr hc, tsum_zero] at h
      exact lt_irrefl _ h
    have h1 : 0 < stepPow P t x z :=
      lt_of_le_of_ne (g72mab_stepPow_nonneg P hP0 t x z) (Ne.symm (left_ne_zero_of_mul hz))
    have h2 : 0 < P z y := lt_of_le_of_ne (hP0 z y) (Ne.symm (right_ne_zero_of_mul hz))
    rw [g72mab_PS_snoc P x t y (fun _ => True)]
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (if t = 0 ∨ True then g72mab_PS P x t z (fun _ => True) else 0) *
          ENNReal.ofReal (P z y) := by
          rw [if_pos (Or.inr trivial)]
          exact ENNReal.mul_pos (ih z h1) (by simp [h2])
      _ ≤ _ := ENNReal.le_tsum z


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

end Chain

structure Ker (V : Type*) where
  f : V → V → ℝ≥0∞

noncomputable section

section KerAlg
variable {V : Type*} [DecidableEq V]

instance : CoeFun (Ker V) (fun _ => V → V → ℝ≥0∞) := ⟨Ker.f⟩

lemma Ker.ext {M N : Ker V} (h : ∀ x y, M x y = N x y) : M = N := by
  cases M; cases N; congr; funext x y; exact h x y

instance : Add (Ker V) := ⟨fun M N => ⟨fun x y => M x y + N x y⟩⟩
instance : Zero (Ker V) := ⟨⟨fun _ _ => 0⟩⟩

lemma add_ap (M N : Ker V) (x y : V) : (M + N) x y = M x y + N x y := rfl
lemma zero_ap (x y : V) : (0 : Ker V) x y = 0 := rfl

instance : AddCommMonoid (Ker V) where
  add_assoc a b c := Ker.ext fun x y => by simp only [add_ap, add_assoc]
  zero_add a := Ker.ext fun x y => by simp only [add_ap, zero_ap, zero_add]
  add_zero a := Ker.ext fun x y => by simp only [add_ap, zero_ap, add_zero]
  add_comm a b := Ker.ext fun x y => by simp only [add_ap, add_comm]
  nsmul := nsmulRec

instance : PartialOrder (Ker V) where
  le M N := ∀ x y, M x y ≤ N x y
  le_refl M x y := le_rfl
  le_trans A B C h1 h2 x y := le_trans (h1 x y) (h2 x y)
  le_antisymm A B h1 h2 := Ker.ext fun x y => le_antisymm (h1 x y) (h2 x y)

lemma le_iff (M N : Ker V) : M ≤ N ↔ ∀ x y, M x y ≤ N x y := Iff.rfl

instance : Mul (Ker V) := ⟨fun M N => ⟨fun x y => ∑' z, M x z * N z y⟩⟩
instance : One (Ker V) := ⟨⟨fun x y => if x = y then 1 else 0⟩⟩

lemma mul_ap (M N : Ker V) (x y : V) : (M * N) x y = ∑' z, M x z * N z y := rfl
lemma one_ap (x y : V) : (1 : Ker V) x y = if x = y then 1 else 0 := rfl

instance : Semiring (Ker V) where
  left_distrib M N O := Ker.ext fun x y => by
    simp only [mul_ap, add_ap, mul_add, ENNReal.tsum_add]
  right_distrib M N O := Ker.ext fun x y => by
    simp only [mul_ap, add_ap, add_mul, ENNReal.tsum_add]
  zero_mul M := Ker.ext fun x y => by simp [mul_ap, zero_ap]
  mul_zero M := Ker.ext fun x y => by simp [mul_ap, zero_ap]
  mul_assoc M N O := Ker.ext fun x y => by
    simp only [mul_ap]
    simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
    exact ENNReal.tsum_comm
  one_mul M := Ker.ext fun x y => by
    simp only [mul_ap, one_ap]
    rw [tsum_eq_single x]
    · simp
    · intro b hb; simp [Ne.symm hb]
  mul_one M := Ker.ext fun x y => by
    simp only [mul_ap, one_ap]
    rw [tsum_eq_single y]
    · simp
    · intro b hb; simp [hb]

lemma sum_ap {α : Type*} (s : Finset α) (f : α → Ker V) (x y : V) :
    (∑ n ∈ s, f n) x y = ∑ n ∈ s, f n x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_ap]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_ap, ih]

lemma kmul_mono {M M' N N' : Ker V} (h1 : M ≤ M') (h2 : N ≤ N') : M * N ≤ M' * N' := by
  intro x y
  exact ENNReal.tsum_le_tsum fun z => mul_le_mul' (h1 x z) (h2 z y)

lemma kadd_mono {M M' N N' : Ker V} (h1 : M ≤ M') (h2 : N ≤ N') : M + N ≤ M' + N' := by
  intro x y
  exact add_le_add (h1 x y) (h2 x y)

/-- `Σ_ν M^ν` -/
def ser (M : Ker V) : Ker V := ⟨fun x y => ∑' n : ℕ, (M ^ n) x y⟩

lemma ser_ap (M : Ker V) (x y : V) : ser M x y = ∑' n : ℕ, (M ^ n) x y := rfl

lemma mul_ser_ap (M N : Ker V) (x y : V) : (M * ser N) x y = ∑' n, (M * N ^ n) x y := by
  simp only [mul_ap, ser_ap]
  simp_rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

lemma ser_mul_ap (M N : Ker V) (x y : V) : (ser N * M) x y = ∑' n, (N ^ n * M) x y := by
  simp only [mul_ap, ser_ap]
  simp_rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_comm

lemma ser_fp (M : Ker V) : ser M = 1 + M * ser M := by
  apply Ker.ext; intro x y
  rw [add_ap, mul_ser_ap, ser_ap, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  try (refine tsum_congr fun n => ?_; rw [pow_succ'])

lemma ser_fp' (M : Ker V) : ser M = 1 + ser M * M := by
  apply Ker.ext; intro x y
  rw [add_ap, ser_mul_ap, ser_ap, tsum_eq_zero_add' ENNReal.summable]
  congr 1
  try (refine tsum_congr fun n => ?_; rw [pow_succ])

lemma ser_comm (M : Ker V) : M * ser M = ser M * M := by
  apply Ker.ext; intro x y
  rw [mul_ser_ap, ser_mul_ap]
  simp only [← pow_succ, ← pow_succ']

lemma one_le_ser (M : Ker V) : 1 ≤ ser M := by
  rw [ser_fp M]; intro x y; rw [add_ap]; exact le_self_add

lemma ser_min {C M W : Ker V} (h : C + M * W ≤ W) : ser M * C ≤ W := by
  have hpart : ∀ N : ℕ, (∑ n ∈ Finset.range N, M ^ n) * C ≤ W := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_mul]; intro x y; exact bot_le
    | succ N ih =>
      rw [Finset.sum_range_succ', pow_zero]
      simp_rw [pow_succ']
      rw [← Finset.mul_sum, add_mul, one_mul, mul_assoc, add_comm]
      exact le_trans (kadd_mono le_rfl (kmul_mono le_rfl ih)) h
  rw [le_iff]; intro x y
  rw [ser_mul_ap]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have := (le_iff _ _).mp (hpart N) x y
  rwa [Finset.sum_mul, sum_ap] at this

lemma ser_min' {C M W : Ker V} (h : C + W * M ≤ W) : C * ser M ≤ W := by
  have hpart : ∀ N : ℕ, C * (∑ n ∈ Finset.range N, M ^ n) ≤ W := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero]; intro x y; exact bot_le
    | succ N ih =>
      rw [Finset.sum_range_succ', pow_zero]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul, mul_add, mul_one, ← mul_assoc, add_comm]
      exact le_trans (kadd_mono le_rfl (kmul_mono ih le_rfl)) h
  rw [le_iff]; intro x y
  rw [mul_ser_ap]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  have := (le_iff _ _).mp (hpart N) x y
  rwa [Finset.mul_sum, sum_ap] at this

lemma pow_mono {M N : Ker V} (h : M ≤ N) : ∀ n, M ^ n ≤ N ^ n := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [pow_succ, pow_succ]; exact kmul_mono ih h

lemma ser_mono {M N : Ker V} (h : M ≤ N) : ser M ≤ ser N := by
  rw [le_iff]; intro x y
  exact ENNReal.tsum_le_tsum fun n => (le_iff _ _).mp (pow_mono h n) x y

/-- resolvent identity `Σ(Q+D)^ν = Σ(Σ Q^ν D)^μ Σ Q^ν` -/
lemma ser_resolvent (Q D : Ker V) : ser (Q + D) = ser (ser Q * D) * ser Q := by
  set S' := ser Q with hS'
  set K := S' * D with hK
  set Y := ser K * S' with hY
  have hS : S' = 1 + Q * S' := ser_fp Q
  have hYe : Y = S' + K * Y := by
    rw [hY]
    conv_lhs => rw [ser_fp K]
    rw [add_mul, one_mul, mul_assoc]
  apply le_antisymm
  · have : ser (Q + D) * 1 ≤ Y := by
      apply ser_min
      apply le_of_eq
      have e1 : (Q + D) * Y = Q * S' + Q * (K * Y) + D * Y := by
        conv_lhs => rw [hYe]
        rw [add_mul, mul_add]
        conv_lhs => rw [← hYe]
      rw [e1]
      conv_rhs => rw [hYe]
      have e2 : K * Y = S' * (D * Y) := by rw [hK, mul_assoc]
      rw [e2]
      conv_rhs => rw [hS]
      rw [add_mul, one_mul, ← mul_assoc Q S' (D * Y)]
      simp only [add_assoc, add_comm, add_left_comm]
    simpa using this
  · apply ser_min
    rw [hK, mul_assoc]
    have h2 : S' * (1 + D * ser (Q + D)) ≤ ser (Q + D) := by
      apply ser_min
      apply le_of_eq
      conv_rhs => rw [ser_fp (Q + D)]
      rw [add_mul]
      simp only [add_assoc, add_comm, add_left_comm]
    calc S' + S' * (D * ser (Q + D)) = S' * (1 + D * ser (Q + D)) := by rw [mul_add, mul_one]
      _ ≤ _ := h2

end KerAlg
end


section Link
variable {V : Type*} [DecidableEq V] (P : V → V → ℝ)

noncomputable def PK : Ker V := ⟨fun x y => ENNReal.ofReal (P x y)⟩

lemma PK_ap (x y : V) : PK P x y = ENNReal.ofReal (P x y) := rfl

open Classical in
noncomputable def rc (A : V → Prop) (K : Ker V) : Ker V := ⟨fun x y => if A y then K x y else 0⟩

lemma rc_pos {A : V → Prop} (K : Ker V) (x : V) {y : V} (h : A y) : rc A K x y = K x y := by
  classical
  show (if A y then K x y else 0) = _
  exact if_pos h

lemma rc_neg {A : V → Prop} (K : Ker V) (x : V) {y : V} (h : ¬ A y) : rc A K x y = 0 := by
  classical
  show (if A y then K x y else 0) = _
  exact if_neg h

lemma mul_rc (M K : Ker V) (A : V → Prop) : M * rc A K = rc A (M * K) := by
  classical
  apply Ker.ext; intro x y
  by_cases h : A y
  · rw [rc_pos _ _ h, mul_ap, mul_ap]
    exact tsum_congr fun z => by rw [rc_pos _ _ h]
  · rw [rc_neg _ _ h, mul_ap]
    exact ENNReal.tsum_eq_zero.mpr fun z => by rw [rc_neg _ _ h, mul_zero]

lemma rc_pow_succ_neg (A : V → Prop) (K : Ker V) (n : ℕ) (u : V) {y : V} (hy : ¬ A y) :
    ((rc A K) ^ (n + 1)) u y = 0 := by
  rw [pow_succ, mul_rc, rc_neg _ _ hy]

lemma ser_rc_col (A : V → Prop) (K : Ker V) (u : V) {y : V} (hy : ¬ A y) :
    ser (rc A K) u y = if u = y then 1 else 0 := by
  rw [ser_ap, tsum_eq_zero_add' ENNReal.summable, pow_zero, one_ap]
  simp only [rc_pow_succ_neg A K _ u hy, tsum_zero, add_zero]

lemma rc_true (K : Ker V) : rc (fun _ => True) K = K :=
  Ker.ext fun x y => rc_pos K x trivial

lemma PS_pow (A : V → Prop) :
    ∀ n x y, g72mab_PS P x (n + 1) y A = ((rc A (PK P)) ^ n * PK P) x y := by
  classical
  intro n
  induction n with
  | zero => intro x y; rw [g72mab_PS_one, pow_zero, one_mul]; rfl
  | succ n ih =>
    intro x y
    rw [g72mab_PS_snoc P x (n + 1) y A, pow_succ, mul_rc, mul_ap]
    refine tsum_congr fun z => ?_
    by_cases hz : A z
    · rw [if_pos (Or.inr hz), rc_pos _ _ hz, ih]; rfl
    · rw [if_neg (by simp [hz]), rc_neg _ _ hz]; simp

open Classical in
noncomputable def WS (x : V) (t : ℕ) (y : V) (A : V → Prop) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ s : Fin (t + 1), s ≠ 0 → A (ω s) then g72mab_W P ω else 0

lemma WS_zero (x y : V) (A : V → Prop) : WS P x 0 y A = if x = y then 1 else 0 := by
  have h : WS P x 0 y A = g72mab_PS P x 0 y A := by
    classical
    unfold WS g72mab_PS
    refine tsum_congr fun ω => ?_
    have e : ∀ s : Fin (0 + 1), s = 0 := fun s => Fin.ext (by have := s.isLt; simp only [Fin.val_zero]; omega)
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2, fun m hm => absurd (e m) hm⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2, fun m hm => absurd (e m) hm⟩
  rw [h, g72mab_PS_zero]
  congr

lemma WS_succ (x : V) (t : ℕ) (y : V) (A : V → Prop) :
    WS P x (t + 1) y A = rc A ⟨fun u v => g72mab_PS P u (t + 1) v A⟩ x y := by
  classical
  have hl : Fin.last (t + 1) ≠ 0 := by simp [Fin.ext_iff]
  by_cases hy : A y
  · rw [rc_pos _ _ hy]
    show _ = g72mab_PS P x (t + 1) y A
    unfold WS g72mab_PS
    refine tsum_congr fun ω => ?_
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun m hm _ => h3 m hm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun m hm => ?_⟩
      by_cases hml : m = Fin.last (t + 1)
      · rw [hml, h2]; exact hy
      · exact h3 m hm hml
  · rw [rc_neg _ _ hy]
    unfold WS
    refine ENNReal.tsum_eq_zero.mpr fun ω => ?_
    rw [if_neg]
    rintro ⟨-, h2, h3⟩
    exact hy (h2 ▸ h3 _ hl)

lemma WS_pow (A : V → Prop) (t : ℕ) (x y : V) : WS P x t y A = ((rc A (PK P)) ^ t) x y := by
  rcases t with _ | t
  · rw [WS_zero, pow_zero, one_ap]
  · rw [WS_succ, pow_succ, mul_rc]
    by_cases hy : A y
    · rw [rc_pos _ _ hy, rc_pos _ _ hy]; exact PS_pow P A t x y
    · rw [rc_neg _ _ hy, rc_neg _ _ hy]

lemma AV_WS (x : V) (A : V → Prop) (t : ℕ) : g72mab_AV P x A t = ∑' y, WS P x t y A := by
  classical
  unfold g72mab_AV WS
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last t))]
  · simp only [true_and]; congr
  · intro y hy; rw [if_neg]; rintro ⟨-, h, -⟩; exact hy h.symm

lemma AV_pow (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A t = ∑' y, ((rc A (PK P)) ^ t) x y := by
  rw [AV_WS]; exact tsum_congr fun y => WS_pow P A t x y

lemma PK_pow (x y : V) : ∀ n, ((PK P) ^ n) x y = g72mab_PS P x n y (fun _ => True) := by
  intro n
  rcases n with _ | n
  · rw [pow_zero, one_ap, g72mab_PS_zero]; congr
  · rw [PS_pow, rc_true, pow_succ]

lemma ns_gam_ser (x y : V) : ns_gam P x y = (ser (rc (fun z => z ≠ x) (PK P)) * PK P) x y := by
  unfold ns_gam
  rw [ser_mul_ap]
  exact tsum_congr fun L => PS_pow P _ L x y

lemma gam_sum (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) :
    ∑' y, ns_gam P x y = ∑' t, g72mab_AV P x (fun z => z ≠ x) t := by
  unfold ns_gam
  simp_rw [PS_pow P]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun L => ?_
  rw [AV_pow]
  simp only [mul_ap]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  rw [ENNReal.tsum_mul_left]
  simp only [PK_ap]
  rw [hrow z, mul_one]

lemma pow_rcEq (x : V) (M : Ker V) : ∀ n, ((rc (fun z => z = x) M) ^ n) x x = (M x x) ^ n := by
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, one_ap, if_pos rfl]
  | succ n ih =>
    rw [pow_succ, mul_ap, tsum_eq_single x, ih, rc_pos (A := fun z => z = x) _ _ rfl, pow_succ]
    intro u hu
    rcases n with _ | n
    · rw [pow_zero, one_ap, if_neg (Ne.symm hu), zero_mul]
    · rw [rc_pow_succ_neg (fun z => z = x) _ _ _ hu, zero_mul]

lemma green (x : V) : ser (PK P) x x = ∑' n : ℕ, (ns_gam P x x) ^ n := by
  classical
  have hPK : PK P = rc (fun z => z ≠ x) (PK P) + rc (fun z => z = x) (PK P) := by
    apply Ker.ext; intro u v
    rw [add_ap]
    by_cases h : v = x
    · rw [rc_neg (A := fun z => z ≠ x) _ _ (not_not.mpr h), rc_pos (A := fun z => z = x) _ _ h,
        zero_add]
    · rw [rc_pos (A := fun z => z ≠ x) _ _ h, rc_neg (A := fun z => z = x) _ _ h, add_zero]
  rw [hPK, ser_resolvent, mul_ap, tsum_eq_single x, ser_rc_col (fun z => z ≠ x) _ _ (not_not.mpr rfl), if_pos rfl,
    mul_one, mul_rc, ser_ap]
  · refine tsum_congr fun n => ?_
    rw [pow_rcEq, ns_gam_ser]
  · intro u hu
    rw [ser_rc_col (fun z => z ≠ x) _ _ (not_not.mpr rfl), if_neg hu, mul_zero]

end Link

section LinkC
variable {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)

lemma rt_nonneg (hP0 : ∀ x y, 0 ≤ P x y) (x : V) (T : ℕ) : 0 ≤ returnTailC P x T := by
  unfold returnTailC setAvoidTailC
  refine tsum_nonneg fun ω => ?_
  split_ifs
  · exact Finset.prod_nonneg fun s _ => hP0 _ _
  · exact le_rfl

lemma AV_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A t ≤ 1 :=
  le_self_add.trans_eq (g72mab_mass P hrow x A t)

lemma rt_eq (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V)
    (T : ℕ) : ENNReal.ofReal (returnTailC P x0 T) = g72mab_AV P x0 (fun z => z ≠ x0) T := by
  classical
  have hAVle : g72mab_AV P x0 (fun z => z ≠ x0) T ≤ 1 := AV_le_one P hrow x0 _ T
  unfold returnTailC setAvoidTailC
  rw [g72mab_ofReal_tsum]
  · unfold g72mab_AV
    refine tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · unfold pathWeightC g72mab_W
      exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
    · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
    · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
    · simp
  · intro ω; split_ifs
    · exact Finset.prod_nonneg fun s _ => hP0 _ _
    · exact le_rfl
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
    unfold g72mab_AV
    refine tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · unfold pathWeightC g72mab_W
      exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
    · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
    · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
    · simp

lemma rt_toReal (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V)
    (T : ℕ) : returnTailC P x T = (g72mab_AV P x (fun z => z ≠ x) T).toReal := by
  rw [← rt_eq P hP0 hrow x T, ENNReal.toReal_ofReal (rt_nonneg P hP0 x T)]

lemma rec_iff (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) :
    Recurrent P x ↔ ns_gam P x x = 1 := by
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
  constructor
  · intro h
    apply ns_gam_kk P hrow x
    have h1 := ENNReal.tendsto_ofReal h
    rw [ENNReal.ofReal_zero] at h1
    have e : (fun t => ENNReal.ofReal (returnTailC P x t)) =
        fun t => g72mab_AV P x (fun z => z ≠ x) t := funext (rt_eq P hP0 hrow x)
    rwa [e] at h1
  · intro h
    have hS := ENNReal.tendsto_nat_tsum (fun s => g72mab_PS P x (s + 1) x (fun z => z ≠ x))
    have hAV : ∀ t, g72mab_AV P x (fun z => z ≠ x) t =
        1 - ∑ s ∈ Finset.range t, g72mab_PS P x (s + 1) x (fun z => z ≠ x) := by
      intro t
      refine ENNReal.eq_sub_of_add_eq ?_ (hmass t)
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq (hmass t))
    have hlim : Filter.Tendsto (fun t => g72mab_AV P x (fun z => z ≠ x) t) Filter.atTop
        (nhds 0) := by
      have := ENNReal.Tendsto.sub tendsto_const_nhds hS (Or.inl ENNReal.one_ne_top)
      have h' : ∑' s, g72mab_PS P x (s + 1) x (fun z => z ≠ x) = 1 := h
      rw [h', tsub_self] at this
      simpa only [hAV] using this
    unfold Recurrent
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    have e : (fun t => returnTailC P x t) = fun t => (g72mab_AV P x (fun z => z ≠ x) t).toReal :=
      funext (rt_toReal P hP0 hrow x)
    rw [e]; exact this

lemma pr_iff (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) :
    PositiveRecurrent P x ↔ ∑' t, g72mab_AV P x (fun z => z ≠ x) t ≠ ⊤ := by
  have hfin : ∀ t, g72mab_AV P x (fun z => z ≠ x) t ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (AV_le_one P hrow x _ t)
  unfold PositiveRecurrent
  simp only [rt_toReal P hP0 hrow x]
  constructor
  · intro hs
    have e : (fun t => g72mab_AV P x (fun z => z ≠ x) t) =
        fun t => ENNReal.ofReal (g72mab_AV P x (fun z => z ≠ x) t).toReal :=
      funext fun t => (ENNReal.ofReal_toReal (hfin t)).symm
    rw [e, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => ENNReal.toReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  · intro h
    exact ENNReal.summable_toReal h

lemma rec_class (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (x y : V) (hx : Recurrent P x) : Recurrent P y := by
  rw [rec_iff P hP0 hrow] at hx ⊢
  obtain ⟨a, ha⟩ := hirr y x
  obtain ⟨b, hb⟩ := hirr x y
  have ha' : ((PK P) ^ a) y x ≠ 0 := by rw [PK_pow]; exact g72mab_stepPow_PS P hP0 y a x ha
  have hb' : ((PK P) ^ b) x y ≠ 0 := by rw [PK_pow]; exact g72mab_stepPow_PS P hP0 x b y hb
  have hxx : ser (PK P) x x = ⊤ := by
    rw [green, hx]; simp only [one_pow]; exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  have hyy : ser (PK P) y y = ⊤ := by
    apply eq_top_iff.mpr
    calc (⊤ : ℝ≥0∞) = ((PK P) ^ a) y x * ser (PK P) x x * ((PK P) ^ b) x y := by
          rw [hxx, ENNReal.mul_top ha', ENNReal.top_mul hb']
      _ = ∑' n, ((PK P) ^ a) y x * ((PK P) ^ n) x x * ((PK P) ^ b) x y := by
          rw [ser_ap, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
      _ ≤ ∑' n, ((PK P) ^ (a + n + b)) y y := ENNReal.tsum_le_tsum fun n => by
            rw [pow_add, pow_add, mul_ap]
            calc _ ≤ ((PK P) ^ a * (PK P) ^ n) y x * ((PK P) ^ b) x y := by
                  gcongr
                  rw [mul_ap]
                  exact ENNReal.le_tsum (f := fun z => ((PK P) ^ a) y z * ((PK P) ^ n) z x) x
              _ ≤ _ := ENNReal.le_tsum (f := fun z => ((PK P) ^ a * (PK P) ^ n) y z *
                  ((PK P) ^ b) z y) x
      _ ≤ ∑' n, ((PK P) ^ n) y y :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun n => a + n + b)
            (fun m n h => by simp only at h; omega) (fun n => ((PK P) ^ n) y y)
      _ = _ := (ser_ap _ _ _).symm
  rw [green] at hyy
  have hle : ns_gam P y y ≤ 1 := g72mab_sum_PS_le P hrow y y (fun z => z ≠ y) (by simp)
  by_contra hne
  have hlt : ns_gam P y y < 1 := lt_of_le_of_ne hle hne
  rw [ENNReal.tsum_geometric] at hyy
  exact (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hlt).ne') hyy

lemma pr_class (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (hrec : ∀ z, Recurrent P z) (x y : V) (hx : PositiveRecurrent P x) :
    PositiveRecurrent P y := by
  classical
  rw [pr_iff P hP0 hrow] at hx ⊢
  rw [← gam_sum P hrow] at hx ⊢
  have hxx : ns_gam P x x = 1 := (rec_iff P hP0 hrow x).mp (hrec x)
  have hyy : ns_gam P y y = 1 := (rec_iff P hP0 hrow y).mp (hrec y)
  have hm := ns_gam_inv P x hxx
  have hfin : ∀ z, ns_gam P x z ≠ ⊤ := fun z => ne_top_of_le_ne_top hx (ENNReal.le_tsum z)
  have hirr' : ∀ w, ∃ L, g72mab_PS P w L y (fun _ => True) ≠ 0 := fun w => by
    obtain ⟨L, hL⟩ := hirr w y
    exact ⟨L, g72mab_stepPow_PS P hP0 w L y hL⟩
  have hu := ns_uniq P (ns_gam P x) hm hfin y hyy hirr'
  have hpos : ns_gam P x y ≠ 0 := by
    obtain ⟨L, hL⟩ := hirr x y
    have := ns_sub_iter P (ns_gam P x) hm L x y
    rw [hxx, one_mul] at this
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (g72mab_stepPow_PS P hP0 x L y hL)) this)
  intro htop
  apply hx
  rw [tsum_congr hu, ENNReal.tsum_mul_left, htop, ENNReal.mul_top hpos]

end LinkC


lemma hrow_of {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ) (hP : IsStochasticC P) :
    ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
  intro z
  rw [← ENNReal.ofReal_tsum_of_nonneg (hP.1 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
    ENNReal.ofReal_one]


end S202TB

namespace S202TB
open MatrixAnalytic.Taboo

section RL
variable {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T : Set S)

open Classical in
noncomputable def Rn (n : ℕ) (i : S) (js : List S) : ℝ≥0∞ :=
  ∑' ω : Fin (n + 1) → S,
    if ω 0 = i ∧ ω (Fin.last n) ∈ T ∧ (List.ofFn ω).filter (fun s => decide (s ∈ T)) = js
    then pathWeightE P ω else 0

lemma rl_eq (i : S) (js : List S) : restrictedLaw P T i js = ∑' n, Rn P T n i js := rfl

lemma pw_eq {n : ℕ} (ω : Fin (n + 1) → S) : pathWeightE P ω = g72mab_W P ω := rfl

open Classical in
lemma Rn_zero (i : S) (js : List S) :
    Rn P T 0 i js = if i ∈ T ∧ js = [i] then 1 else 0 := by
  unfold Rn
  rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq, tsum_eq_single i]
  · simp only [Equiv.funUnique_symm_apply, Fin.last_zero]
    have h1 : List.ofFn (uniqueElim i : Fin 1 → S) = [i] := by
      rw [List.ofFn_succ]; simp
    rw [h1]
    by_cases hi : i ∈ T
    · by_cases hj : js = [i]
      · subst hj; simp [hi, pathWeightE]
      · have : ¬ [i] = js := fun h => hj h.symm
        simp [hi, hj, this]
    · simp [hi]
  · intro b hb
    simp [hb]

lemma Rn_nil (n : ℕ) (i : S) : Rn P T n i [] = 0 := by
  unfold Rn
  refine ENNReal.tsum_eq_zero.mpr fun ω => if_neg ?_
  rintro ⟨-, h2, h3⟩
  rw [List.filter_eq_nil_iff] at h3
  exact h3 _ (List.mem_ofFn.mpr ⟨_, rfl⟩) (by simpa using h2)

open Classical in
lemma Rn_succ_gen (n : ℕ) (i : S) (js : List S) (c : List S → Prop)
    (hc : ∀ ω' : Fin (n + 1) → S,
      ((List.ofFn (Fin.cons i ω' : Fin (n + 2) → S)).filter (fun s => decide (s ∈ T)) = js ↔
        c ((List.ofFn ω').filter (fun s => decide (s ∈ T))))) :
    Rn P T (n + 1) i js = ∑' y, ennP P i y * ∑' ω' : Fin (n + 1) → S,
      (if ω' 0 = y ∧ ω' (Fin.last n) ∈ T ∧ c ((List.ofFn ω').filter (fun s => decide (s ∈ T)))
        then pathWeightE P ω' else 0) := by
  unfold Rn
  rw [g72mab_tsum_cons, tsum_eq_single i]
  · simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω' => ?_
    rw [tsum_eq_single (ω' 0)]
    · have hl : (Fin.cons i ω' : Fin (n + 2) → S) (Fin.last (n + 1)) = ω' (Fin.last n) := by
        rw [← Fin.succ_last, Fin.cons_succ]
      simp only [Fin.cons_zero, hl, true_and, hc ω']
      rw [pw_eq, pw_eq, g72mab_W_cons]
      split_ifs <;> simp [ennP]
    · intro y hy
      rw [if_neg (by rintro ⟨h, -⟩; exact hy h.symm), mul_zero]
  · intro k hk
    refine ENNReal.tsum_eq_zero.mpr fun ω' => if_neg ?_
    rintro ⟨h, -⟩
    exact hk (by simpa using h)

lemma Rn_succ_out (n : ℕ) (i : S) (hi : i ∉ T) (js : List S) :
    Rn P T (n + 1) i js = ∑' y, ennP P i y * Rn P T n y js := by
  classical
  rw [Rn_succ_gen P T n i js (fun F => F = js)]
  · refine tsum_congr fun y => ?_; congr 1; unfold Rn
    exact tsum_congr fun ω => by split_ifs <;> first | rfl | (exfalso; tauto)
  · intro ω'
    rw [List.ofFn_succ]
    simp [hi]

lemma Rn_succ_in (n : ℕ) (i : S) (hi : i ∈ T) (a : S) (js : List S) :
    Rn P T (n + 1) i (a :: js) = if a = i then ∑' y, ennP P i y * Rn P T n y js else 0 := by
  classical
  rw [Rn_succ_gen P T n i (a :: js) (fun F => a = i ∧ F = js)]
  · split_ifs with ha
    · refine tsum_congr fun y => ?_; congr 1; unfold Rn
      exact tsum_congr fun ω => by split_ifs <;> first | rfl | (exfalso; tauto)
    · refine ENNReal.tsum_eq_zero.mpr fun y => ?_
      refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun ω => if_neg ?_)
      rintro ⟨-, -, h, -⟩; exact ha h
  · intro ω'
    rw [List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, List.filter_cons, hi, decide_true, if_true,
      List.cons.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩

end RL
end S202TB

namespace S202TB
open MatrixAnalytic.Taboo

section Alg
variable {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T : Set S)

open Classical in
noncomputable def QK : Ker S := rc (fun y => y ∉ T) (PK P)

open Classical in
noncomputable def QR : Ker S := ⟨fun x y => if x ∉ T then ennP P x y else 0⟩

open Classical in
lemma QR_in {x : S} (hx : x ∈ T) (y : S) : QR P T x y = 0 := by
  show (if x ∉ T then ennP P x y else 0) = 0
  rw [if_neg (not_not.mpr hx)]

open Classical in
lemma QR_out {x : S} (hx : x ∉ T) (y : S) : QR P T x y = ennP P x y := by
  show (if x ∉ T then ennP P x y else 0) = _
  rw [if_pos hx]

lemma QK_in (x : S) {y : S} (hy : y ∈ T) : QK P T x y = 0 :=
  rc_neg (A := fun y => y ∉ T) _ _ (not_not.mpr hy)

lemma QK_out (x : S) {y : S} (hy : y ∉ T) : QK P T x y = ennP P x y :=
  rc_pos (A := fun y => y ∉ T) _ _ hy

lemma Rn_one {j : S} (hj : j ∈ T) : ∀ m y, Rn P T m y [j] = (QR P T ^ m) y j := by
  intro m
  induction m with
  | zero =>
    intro y
    rw [Rn_zero, pow_zero, one_ap]
    by_cases h : y = j
    · subst h; simp [hj]
    · rw [if_neg h, if_neg]; rintro ⟨-, h2⟩; exact h (by simpa using h2.symm)
  | succ m ih =>
    intro y
    rw [pow_succ', mul_ap]
    by_cases hy : y ∈ T
    · rw [Rn_succ_in P T m y hy]
      simp only [QR_in P T hy, zero_mul, tsum_zero, Rn_nil, mul_zero, ite_self]
    · rw [Rn_succ_out P T m y hy]
      exact tsum_congr fun z => by rw [ih, QR_out P T hy]

lemma rl_one {j : S} (hj : j ∈ T) (y : S) : restrictedLaw P T y [j] = ser (QR P T) y j := by
  rw [rl_eq, ser_ap]
  exact tsum_congr fun m => Rn_one P T hj m y

lemma PK_QR : PK P * QR P T = QK P T * PK P := by
  apply Ker.ext; intro x y
  rw [mul_ap, mul_ap]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ T
  · rw [QR_in P T hz, QK_in P T x hz, mul_zero, zero_mul]
  · rw [QR_out P T hz, QK_out P T x hz]; rfl

lemma PK_QR_pow : ∀ n, PK P * QR P T ^ n = QK P T ^ n * PK P := by
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one, one_mul]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, PK_QR, ← mul_assoc]

lemma CK_eq : PK P * ser (QR P T) = ser (QK P T) * PK P := by
  apply Ker.ext; intro x y
  rw [mul_ser_ap, ser_mul_ap]
  exact tsum_congr fun n => by rw [PK_QR_pow]

lemma QK_pow_in : ∀ ν (k : S) {z : S}, z ∈ T → (QK P T ^ ν) k z = 0 ∨ (ν = 0 ∧ k = z) := by
  intro ν k z hz
  rcases ν with _ | ν
  · rw [pow_zero, one_ap]
    by_cases h : k = z
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl (if_neg h)
  · left
    unfold QK
    rw [pow_succ, mul_rc, rc_neg (A := fun y => y ∉ T) _ _ (not_not.mpr hz)]

lemma QK_pow_in' (ν : ℕ) {k z : S} (hk : k ∉ T) (hz : z ∈ T) : (QK P T ^ ν) k z = 0 := by
  rcases QK_pow_in P T ν k hz with h | ⟨-, h⟩
  · exact h
  · exact absurd (h ▸ hz) hk

lemma QK_subPow : ∀ ν (k l : S), k ∉ T → l ∉ T → (QK P T ^ ν) k l = subPow (ennP P) Tᶜ ν k l := by
  intro ν
  induction ν with
  | zero => intro k l _ _; rw [pow_zero, one_ap]; rfl
  | succ ν ih =>
    intro k l hk hl
    rw [pow_succ, mul_ap]
    show _ = ∑' z : (Tᶜ : Set S), subPow (ennP P) Tᶜ ν k z * ennP P z l
    rw [← tsum_subtype_eq_of_support_subset (s := Tᶜ)]
    · refine tsum_congr fun z => ?_
      rw [ih k z hk z.2, QK_out P T _ hl]
    · intro z hz
      by_contra hzT
      apply hz
      show (QK P T ^ ν) k z * _ = 0
      rw [QK_pow_in' P T ν hk (not_not.mp hzT), zero_mul]

lemma QK_succ_PK (n : ℕ) (i j : S) :
    (QK P T ^ (n + 1) * PK P) i j = ∑' k : (Tᶜ : Set S), ∑' l : (Tᶜ : Set S),
      ennP P i k * subPow (ennP P) Tᶜ n k l * ennP P l j := by
  rw [pow_succ', mul_assoc, mul_ap, ← tsum_subtype_eq_of_support_subset (s := Tᶜ)]
  · refine tsum_congr fun k => ?_
    rw [QK_out P T _ k.2, mul_ap, ← ENNReal.tsum_mul_left,
      ← tsum_subtype_eq_of_support_subset (s := Tᶜ)]
    · refine tsum_congr fun l => ?_
      rw [QK_subPow P T n k l k.2 l.2, mul_assoc]; rfl
    · intro l hl
      by_contra hlT
      apply hl
      show _ * ((QK P T ^ n) k l * _) = 0
      rw [QK_pow_in' P T n k.2 (not_not.mp hlT), zero_mul, mul_zero]
  · intro k hk
    by_contra hkT
    apply hk
    show QK P T i k * _ = 0
    rw [QK_in P T _ (not_not.mp hkT), zero_mul]

lemma cm_eq (i j : S) : censoredMatrix P T i j = (ser (QK P T) * PK P) i j := by
  rw [ser_mul_ap, tsum_eq_zero_add' ENNReal.summable, pow_zero, one_mul]
  unfold censoredMatrix seriesInv
  congr 1
  simp_rw [QK_succ_PK]
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  conv_lhs => enter [1, k]; rw [ENNReal.tsum_comm]
  conv_lhs => rw [ENNReal.tsum_comm]

lemma cm_eq' (i j : S) : censoredMatrix P T i j = (PK P * ser (QR P T)) i j := by
  rw [cm_eq, CK_eq]

lemma rc_congr {A A' : S → Prop} (h : ∀ y, A y ↔ A' y) (K : Ker S) : rc A K = rc A' K := by
  classical
  apply Ker.ext; intro x y
  by_cases hy : A y
  · rw [rc_pos (A := A) _ _ hy, rc_pos (A := A') _ _ ((h y).mp hy)]
  · rw [rc_neg (A := A) _ _ hy, rc_neg (A := A') _ _ (fun h' => hy ((h y).mpr h'))]

lemma rc_le {A A' : S → Prop} (h : ∀ y, A y → A' y) (K : Ker S) : rc A K ≤ rc A' K := by
  classical
  intro x y
  by_cases hy : A y
  · rw [rc_pos (A := A) _ _ hy, rc_pos (A := A') _ _ (h y hy)]
  · rw [rc_neg (A := A) _ _ hy]; exact bot_le

lemma cens (B : S → Prop) (hB : ∀ y, B y → y ∈ T) (x : S) {b : S} (hb : b ∈ T) :
    ser (rc (fun y => y ∉ T ∨ B y) (PK P)) x b = ser (rc B (ser (QK P T) * PK P)) x b := by
  classical
  have hsplit : rc (fun y => y ∉ T ∨ B y) (PK P) = QK P T + rc B (PK P) := by
    apply Ker.ext; intro u y
    rw [add_ap]
    by_cases hy : y ∈ T
    · rw [QK_in P T _ hy, zero_add]
      by_cases hBy : B y
      · rw [rc_pos (A := fun y => y ∉ T ∨ B y) _ _ (Or.inr hBy), rc_pos (A := B) _ _ hBy]
      · rw [rc_neg (A := fun y => y ∉ T ∨ B y) _ _ (by tauto), rc_neg (A := B) _ _ hBy]
    · rw [rc_pos (A := fun y => y ∉ T ∨ B y) _ _ (Or.inl hy), QK_out P T _ hy,
        rc_neg (A := B) _ _ (fun h => hy (hB y h)), add_zero]; rfl
  rw [hsplit, ser_resolvent, mul_ap, tsum_eq_single b]
  · unfold QK
    rw [ser_rc_col (fun y => y ∉ T) _ _ (not_not.mpr hb), if_pos rfl, mul_one, ← mul_rc]
  · intro z hz
    unfold QK
    rw [ser_rc_col (fun y => y ∉ T) _ _ (not_not.mpr hb), if_neg hz, mul_zero]

/-- restriction of a kernel to the subtype -/
def resK (M : Ker S) : Ker T := ⟨fun a b => M a b⟩

lemma resK_pow (M : Ker S) (hM : ∀ x y, y ∉ T → M x y = 0) :
    ∀ n (a b : T), (resK T M ^ n) a b = (M ^ n) a b := by
  intro n
  induction n with
  | zero =>
    intro a b
    rw [pow_zero, pow_zero, one_ap, one_ap]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]
  | succ n ih =>
    intro a b
    rw [pow_succ', pow_succ', mul_ap, mul_ap, ← tsum_subtype_eq_of_support_subset (s := T)]
    · exact tsum_congr fun z => by rw [ih]; rfl
    · intro z hz
      by_contra hzT
      apply hz
      show M a z * _ = 0
      rw [hM _ _ hzT, zero_mul]

lemma resK_ser (M : Ker S) (hM : ∀ x y, y ∉ T → M x y = 0) (a b : T) :
    ser (resK T M) a b = ser M a b := by
  rw [ser_ap, ser_ap]
  exact tsum_congr fun n => resK_pow T M hM n a b

end Alg
end S202TB

namespace S202TB
open MatrixAnalytic.Taboo Filter Topology

section Gen9
variable {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)

lemma pk_row_pow (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) :
    ∀ t x, ∑' y, (PK P ^ t) x y = 1 := by
  intro t
  induction t with
  | zero =>
    intro x
    simp only [pow_zero, one_ap]
    rw [tsum_eq_single x (fun b hb => if_neg (Ne.symm hb)), if_pos rfl]
  | succ t ih =>
    intro x
    simp only [pow_succ', mul_ap]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ih, mul_one, PK_ap, hrow]

lemma stepPow_ofReal (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) :
    ∀ t x y, ENNReal.ofReal (stepPow P t x y) = (PK P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    simp only [stepPow, pow_zero, one_ap]
    by_cases h : x = y
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, ENNReal.ofReal_zero]
  | succ t ih =>
    intro x y
    simp only [stepPow]
    have hle : ∀ z, ENNReal.ofReal (stepPow P t x z * P z y) ≤ (PK P ^ t) x z := fun z => by
      rw [ENNReal.ofReal_mul (g72mab_stepPow_nonneg P hP0 t x z), ih]
      calc _ ≤ (PK P ^ t) x z * 1 := by
            gcongr
            rw [← hrow z]; exact ENNReal.le_tsum y
        _ = _ := mul_one _
    rw [g72mab_ofReal_tsum _ (fun z => mul_nonneg (g72mab_stepPow_nonneg P hP0 t x z) (hP0 z y))]
    · rw [pow_succ, mul_ap]
      refine tsum_congr fun z => ?_
      rw [ENNReal.ofReal_mul (g72mab_stepPow_nonneg P hP0 t x z), ih]; rfl
    · exact ne_top_of_le_ne_top (by rw [pk_row_pow P hrow t x]; exact ENNReal.one_ne_top)
        (ENNReal.tsum_le_tsum hle)

lemma hasSum_of_ofReal {α : Type*} (f : α → ℝ) (r : ℝ) (hf : ∀ a, 0 ≤ f a) (hr : 0 ≤ r)
    (h : ∑' a, ENNReal.ofReal (f a) = ENNReal.ofReal r) : HasSum f r := by
  have hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤ := by rw [h]; exact ENNReal.ofReal_ne_top
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  have h2 := g72mab_ofReal_tsum f hf hne
  rw [h] at h2
  have e : ∑' a, f a = r := (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hf) hr).mp h2
  exact e ▸ hs.hasSum

lemma inv_ofReal (hP0 : ∀ x y, 0 ≤ P x y) (μ : V → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hinv : ∀ y, HasSum (fun x => μ x * P x y) (μ y)) :
    ∀ y, ∑' x, ENNReal.ofReal (μ x) * ENNReal.ofReal (P x y) = ENNReal.ofReal (μ y) := by
  intro y
  rw [← (hinv y).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun x => mul_nonneg (hμ0 x) (hP0 x y)) (hinv y).summable]
  exact tsum_congr fun x => (ENNReal.ofReal_mul (hμ0 x)).symm

lemma rec_of_pr (x : V) (h : PositiveRecurrent P x) : Recurrent P x :=
  h.tendsto_atTop_zero

lemma stat_uniq (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (a : V) (hpr : PositiveRecurrent P a)
    (μ₁ μ₂ : V → ℝ) (h1 : IsStationaryC P μ₁) (h2 : IsStationaryC P μ₂) : μ₁ = μ₂ := by
  have hkk : ns_gam P a a = 1 := (rec_iff P hP0 hrow a).mp (rec_of_pr P a hpr)
  have hirr' : ∀ x, ∃ L, g72mab_PS P x L a (fun _ => True) ≠ 0 := fun x => by
    obtain ⟨t, ht⟩ := hirr x a
    exact ⟨t, g72mab_stepPow_PS P hP0 x t a ht⟩
  have key : ∀ μ : V → ℝ, IsStationaryC P μ →
      ∀ y, ENNReal.ofReal (μ y) = (∑' z, ns_gam P a z)⁻¹ * ns_gam P a y := by
    intro μ hμ
    have hm := inv_ofReal P hP0 μ hμ.1 hμ.2.2
    have hu := ns_uniq P (fun x => ENNReal.ofReal (μ x)) hm (fun _ => ENNReal.ofReal_ne_top) a hkk
      hirr'
    have hsum : ∑' z, ENNReal.ofReal (μ z) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.1.summable, hμ.2.1.tsum_eq, ENNReal.ofReal_one]
    have hmul : ENNReal.ofReal (μ a) * ∑' z, ns_gam P a z = 1 := by
      rw [← ENNReal.tsum_mul_left, ← hsum]; exact (tsum_congr hu).symm
    intro y
    rw [hu y, ENNReal.eq_inv_of_mul_eq_one_left hmul]
  funext y
  have e := (key μ₁ h1 y).trans (key μ₂ h2 y).symm
  exact (ENNReal.ofReal_eq_ofReal_iff (h1.1 y) (h2.1 y)).mp e

lemma hit_zero (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (t0 : V) (hpr : PositiveRecurrent P t0) (i : V) :
    Tendsto (fun t => ∑' y, ((rc (fun z => z ≠ t0) (PK P)) ^ t) i y) atTop (𝓝 0) := by
  classical
  set N := rc (fun z => z ≠ t0) (PK P) with hN
  have h0 : Tendsto (fun t => ∑' y, (N ^ t) t0 y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => ENNReal.ofReal (returnTailC P t0 t)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal hpr.tendsto_atTop_zero
      rwa [ENNReal.ofReal_zero] at this
    refine h1.congr fun t => ?_
    rw [rt_eq P hP0 hrow t0 t, AV_pow]
  by_cases hi : i = t0
  · subst hi; exact h0
  obtain ⟨m, hm⟩ : ∃ m, (N ^ m) t0 i ≠ 0 := by
    obtain ⟨L, hL⟩ := hirr t0 i
    obtain ⟨u, hu⟩ := g72mab_taboo_extract P t0 i hi L (g72mab_stepPow_PS P hP0 t0 L i hL)
    rcases u with _ | u
    · rw [g72mab_PS_zero, if_neg (Ne.symm hi)] at hu; exact absurd rfl hu
    · refine ⟨u + 1, ?_⟩
      rw [hN, pow_succ, mul_rc, rc_pos (A := fun z => z ≠ t0) _ _ hi, ← PS_pow]; exact hu
  set c := min ((N ^ m) t0 i) 1 with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (lt_min (pos_iff_ne_zero.mpr hm) one_pos).ne'
  have hcT : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hle : ∀ t, ∑' y, (N ^ t) i y ≤ c⁻¹ * ∑' y, (N ^ (t + m)) t0 y := by
    intro t
    rw [← ENNReal.mul_le_iff_le_inv hc0 hcT]
    calc c * ∑' y, (N ^ t) i y ≤ (N ^ m) t0 i * ∑' y, (N ^ t) i y := by
          gcongr; exact min_le_left _ _
      _ ≤ ∑' z, (N ^ m) t0 z * ∑' y, (N ^ t) z y := ENNReal.le_tsum i
      _ = ∑' y, (N ^ (t + m)) t0 y := by
          rw [add_comm, pow_add]
          simp only [mul_ap]
          rw [ENNReal.tsum_comm]
          simp_rw [ENNReal.tsum_mul_left]
  have hup : Tendsto (fun t => c⁻¹ * ∑' y, (N ^ (t + m)) t0 y) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ((tendsto_add_atTop_iff_nat m).mpr h0)
      (Or.inr (ENNReal.inv_ne_top.mpr hc0))
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le) hle

end Gen9
end S202TB

namespace S202TB
open MatrixAnalytic.Taboo Filter Topology

section Main1
variable {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T : Set S)

lemma QK_mass (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (hpos : ∀ x, PositiveRecurrent P x) {t0 : S} (ht0 : t0 ∈ T) (i : S) :
    ∑' n, ∑' j : T, (QK P T ^ n * PK P) i j = 1 := by
  classical
  set a : ℕ → ℝ≥0∞ := fun n => ∑' y, (QK P T ^ n) i y with ha
  set b : ℕ → ℝ≥0∞ := fun n => ∑' j : T, (QK P T ^ n * PK P) i j with hb
  have hab : ∀ n, a n = b n + a (n + 1) := by
    intro n
    have e1 : ∑' y, (QK P T ^ n * PK P) i y = a n := by
      simp only [mul_ap, ha]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left, PK_ap, hrow, mul_one]
    have e2 := (Summable.tsum_add_tsum_compl (s := T) (f := fun y => (QK P T ^ n * PK P) i y)
      ENNReal.summable ENNReal.summable)
    have e3 : ∑' y : (Tᶜ : Set S), (QK P T ^ n * PK P) i y = a (n + 1) := by
      simp only [ha]
      rw [pow_succ]
      unfold QK
      rw [mul_rc, ← tsum_subtype_eq_of_support_subset (s := Tᶜ)]
      · exact tsum_congr fun y => (rc_pos (A := fun y => y ∉ T) _ _ y.2).symm
      · intro y hy
        by_contra hyT
        exact hy (rc_neg (A := fun y => y ∉ T) _ _ hyT)
    rw [← e1, ← e2, e3]
  have hsum : ∀ t, ∑ k ∈ Finset.range t, b k + a t = 1 := by
    intro t
    induction t with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, ha, pow_zero, one_ap]
      rw [tsum_eq_single i (fun y hy => if_neg (Ne.symm hy)), if_pos rfl]
    | succ t ih => rw [Finset.sum_range_succ, add_assoc, ← hab]; exact ih
  have htend : Tendsto a atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hit_zero P hP0 hrow hirr t0 (hpos t0) i) (fun _ => zero_le) fun t => ?_
    refine ENNReal.tsum_le_tsum fun y => ?_
    unfold QK
    exact pow_mono (rc_le (fun y (hy : y ∉ T) => (fun (h : y = t0) => hy (h ▸ ht0) : y ≠ t0)) (PK P)) t i y
  have hlim := (ENNReal.tendsto_nat_tsum b).add htend
  rw [add_zero] at hlim
  have hconst : (fun t => ∑ k ∈ Finset.range t, b k + a t) = fun _ => (1 : ℝ≥0∞) := funext hsum
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

lemma serQR_in {y : S} (hy : y ∈ T) (j : S) : ser (QR P T) y j = if y = j then 1 else 0 := by
  rw [ser_ap, tsum_eq_zero_add' ENNReal.summable, pow_zero, one_ap]
  simp only [pow_succ', mul_ap, QR_in P T hy, zero_mul, tsum_zero, add_zero]

lemma serQR_out {y : S} (hy : y ∉ T) {j : S} (hj : j ∈ T) :
    ser (QR P T) y j = (ser (QK P T) * PK P) y j := by
  rw [ser_ap, tsum_eq_zero_add' ENNReal.summable, pow_zero, one_ap,
    if_neg (fun (h : y = j) => hy (h ▸ hj)), zero_add, ser_mul_ap]
  refine tsum_congr fun n => ?_
  rw [pow_succ', mul_ap, ← PK_QR_pow, mul_ap]
  exact tsum_congr fun z => by rw [QR_out P T hy]; rfl

lemma sum_serQR (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (hpos : ∀ x, PositiveRecurrent P x) {t0 : S} (ht0 : t0 ∈ T) (y : S) :
    ∑' j : T, ser (QR P T) y j = 1 := by
  by_cases hy : y ∈ T
  · simp_rw [serQR_in P T hy]
    rw [tsum_eq_single ⟨y, hy⟩, if_pos rfl]
    intro b hb
    exact if_neg (fun h => hb (Subtype.ext h.symm))
  · rw [tsum_congr fun j : T => serQR_out P T hy j.2]
    simp_rw [ser_mul_ap]
    rw [ENNReal.tsum_comm]
    exact QK_mass P T hP0 hrow hirr hpos ht0 y

lemma cm_row (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (hpos : ∀ x, PositiveRecurrent P x) {t0 : S} (ht0 : t0 ∈ T) (i : S) :
    ∑' j : T, censoredMatrix P T i j = 1 := by
  simp_rw [cm_eq', mul_ap]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, sum_serQR P T hP0 hrow hirr hpos ht0, mul_one, PK_ap, hrow]

lemma cm_le_one (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (hpos : ∀ x, PositiveRecurrent P x) {t0 : S} (ht0 : t0 ∈ T) (i : S)
    (j : T) : censoredMatrix P T i j ≤ 1 := by
  rw [← cm_row P T hP0 hrow hirr hpos ht0 i]
  exact ENNReal.le_tsum (f := fun j : T => censoredMatrix P T i j) j

lemma rl_sum (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (hpos : ∀ x, PositiveRecurrent P x) {t0 : S} (ht0 : t0 ∈ T) (i : S) :
    ∑' j : T, restrictedLaw P T i [(j : S)] = 1 := by
  rw [tsum_congr fun j : T => rl_one P T j.2 i]
  exact sum_serQR P T hP0 hrow hirr hpos ht0 i

lemma Rn_conv {j₀ : S} (hj₀ : j₀ ∈ T) (rest : List S) :
    ∀ n i, Rn P T n i (j₀ :: rest) =
      ∑ m ∈ Finset.range (n + 1), Rn P T m i [j₀] * Rn P T (n - m) j₀ (j₀ :: rest) := by
  intro n
  induction n with
  | zero =>
    intro i
    rw [zero_add, Finset.sum_range_one, Nat.sub_zero]
    by_cases h : i = j₀
    · subst h; rw [Rn_zero P T i [i], if_pos ⟨hj₀, rfl⟩, one_mul]
    · rw [Rn_zero P T i [j₀], if_neg (by rintro ⟨-, h2⟩; simp at h2; exact h h2.symm), zero_mul,
        Rn_zero, if_neg]
      rintro ⟨-, h2⟩; simp at h2; exact h h2.1.symm
  | succ n ih =>
    intro i
    by_cases hi : i ∈ T
    · rw [Finset.sum_range_succ']
      have hz : ∀ m ∈ Finset.range (n + 1),
          Rn P T (m + 1) i [j₀] * Rn P T (n + 1 - (m + 1)) j₀ (j₀ :: rest) = 0 := by
        intro m _
        rw [Rn_succ_in P T m i hi]
        simp [Rn_nil]
      rw [Finset.sum_eq_zero hz, zero_add, Nat.sub_zero]
      by_cases h : i = j₀
      · subst h; rw [Rn_zero P T i [i], if_pos ⟨hj₀, rfl⟩, one_mul]
      · rw [Rn_zero P T i [j₀], if_neg (by rintro ⟨-, h2⟩; simp at h2; exact h h2.symm), zero_mul,
          Rn_succ_in P T n i hi, if_neg (Ne.symm h)]
    · rw [Rn_succ_out P T n i hi, Finset.sum_range_succ', Rn_zero P T i [j₀],
        if_neg (fun h => hi h.1), zero_mul, add_zero]
      simp_rw [ih, Finset.mul_sum]
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Rn_succ_out P T m i hi, ← ENNReal.tsum_mul_right, Nat.add_sub_add_right]
      exact tsum_congr fun y => (mul_assoc _ _ _).symm

lemma rl_split {j₀ : S} (hj₀ : j₀ ∈ T) (rest : List S) (i : S) :
    restrictedLaw P T i (j₀ :: rest) =
      restrictedLaw P T i [j₀] * restrictedLaw P T j₀ (j₀ :: rest) := by
  rw [rl_eq, rl_eq, rl_eq, ← g72mab_cauchy0]
  exact tsum_congr fun n => Rn_conv P T hj₀ rest n i

lemma rl_self {j : S} (hj : j ∈ T) : restrictedLaw P T j [j] = 1 := by
  rw [rl_one P T hj, serQR_in P T hj, if_pos rfl]

lemma rl_step {j₀ j₁ : S} (hj₀ : j₀ ∈ T) (hj₁ : j₁ ∈ T) (rest : List S) :
    restrictedLaw P T j₀ (j₀ :: j₁ :: rest) =
      censoredMatrix P T j₀ j₁ * restrictedLaw P T j₁ (j₁ :: rest) := by
  rw [rl_eq, tsum_eq_zero_add' ENNReal.summable, Rn_zero, if_neg (by rintro ⟨-, h⟩; simp at h),
    zero_add]
  have e : ∀ n, Rn P T (n + 1) j₀ (j₀ :: j₁ :: rest) =
      ∑' y, ennP P j₀ y * Rn P T n y (j₁ :: rest) := fun n => by
    rw [Rn_succ_in P T n j₀ hj₀, if_pos rfl]
  rw [tsum_congr e, ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  have e2 : ∀ y, ennP P j₀ y * ∑' n, Rn P T n y (j₁ :: rest) =
      ennP P j₀ y * ser (QR P T) y j₁ * restrictedLaw P T j₁ (j₁ :: rest) := fun y => by
    rw [← rl_eq, rl_split P T hj₁ rest, rl_one P T hj₁, mul_assoc]
  rw [tsum_congr e2, ENNReal.tsum_mul_right, cm_eq', mul_ap]; rfl

lemma rl_chain : ∀ rest : List S, (∀ j ∈ rest, j ∈ T) → ∀ j₀ ∈ T,
    restrictedLaw P T j₀ (j₀ :: rest) = chainWeight (censoredMatrix P T) j₀ rest := by
  intro rest
  induction rest with
  | nil => intro _ j₀ hj₀; rw [rl_self P T hj₀]; rfl
  | cons j₁ rest ih =>
    intro h j₀ hj₀
    rw [rl_step P T hj₀ (h j₁ (List.mem_cons_self ..)) rest,
      ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) j₁ (h j₁ (List.mem_cons_self ..))]
    rfl

lemma stat_T (hP0 : ∀ x y, 0 ≤ P x y) (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1)
    (hirr : IrreducibleC P) (hpos : ∀ x, PositiveRecurrent P x) {t0 : S} (ht0 : t0 ∈ T)
    (π : S → ℝ) (hπ : IsStationaryC P π) :
    ∀ j : T, ∑' i : T, ENNReal.ofReal (π i) * censoredMatrix P T i j = ENNReal.ofReal (π j) := by
  classical
  set m : S → ℝ≥0∞ := fun x => ENNReal.ofReal (π x) with hmdef
  have hm : ∀ y, ∑' x, m x * ENNReal.ofReal (P x y) = m y := inv_ofReal P hP0 π hπ.1 hπ.2.2
  have hupper : ∀ j : T, ∑' i : T, m i * censoredMatrix P T i j ≤ m j := by
    intro j
    have hit := ns_iter P m hm (fun z => z ∉ T) (j : S)
    have hg : ∀ t, ∑ L ∈ Finset.range t, ∑' x, (if x ∉ T then 0 else
        m x * g72mab_PS P x (L + 1) j (fun z => z ∉ T)) ≤ m j := by
      intro t
      calc _ ≤ ∑ L ∈ Finset.range (t + 1), ∑' x, (if x ∉ T then 0 else
              m x * g72mab_PS P x (L + 1) j (fun z => z ∉ T)) := by
            rw [Finset.sum_range_succ]; exact le_self_add
        _ ≤ _ := by rw [hit t]; exact le_self_add
    have h2 := ENNReal.tsum_le_of_sum_range_le hg
    refine le_trans (le_of_eq ?_) h2
    rw [ENNReal.tsum_comm, ← tsum_subtype_eq_of_support_subset (s := T)]
    · refine tsum_congr fun i => ?_
      rw [cm_eq, ser_mul_ap, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun L => ?_
      rw [if_neg (not_not.mpr i.2), PS_pow]; rfl
    · intro x hx
      by_contra hxT
      apply hx
      exact ENNReal.tsum_eq_zero.mpr fun L => if_pos hxT
  have hfin : ∑' j : T, ∑' i : T, m i * censoredMatrix P T i j ≠ ⊤ := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, cm_row P T hP0 hrow hirr hpos ht0, mul_one]
    refine ne_top_of_le_ne_top (b := ∑' x, m x) ?_
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective m)
    rw [hmdef, ← ENNReal.ofReal_tsum_of_nonneg hπ.1 hπ.2.1.summable]
    exact ENNReal.ofReal_ne_top
  have htot : ∑' j : T, ∑' i : T, m i * censoredMatrix P T i j = ∑' j : T, m j := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, cm_row P T hP0 hrow hirr hpos ht0, mul_one]
  intro j
  by_contra hne
  have hlt := ENNReal.tsum_lt_tsum hfin hupper (lt_of_le_of_ne (hupper j) hne)
  rw [htot] at hlt
  exact lt_irrefl _ hlt

end Main1
end S202TB

open MatrixAnalytic.Taboo S202TB in
open scoped ENNReal in
theorem solution {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (hpos : ∀ x : S, PositiveRecurrent P x)
    (π : S → ℝ) (hπ : IsStationaryC P π)
    (T : Set S) (hT : T.Nonempty) :
    -- the restricted process is defined at time 0 (hence, with the next clauses, at all times)
    (∀ i : S, HasSum (fun j : T => restrictedLaw P T i [(j : S)]) 1) ∧
    -- it is a homogeneous Markov chain with transition matrix `P(T)`
    (∀ i : S, ∀ j₀ ∈ T, ∀ js : List S, (∀ j ∈ js, j ∈ T) →
      restrictedLaw P T i (j₀ :: js) =
        restrictedLaw P T i [j₀] * chainWeight (censoredMatrix P T) j₀ js) ∧
    -- `P(T)` is stochastic on `T`
    (∀ i ∈ T, HasSum (fun j : T => censoredMatrix P T i j) 1) ∧
    -- irreducible and positive recurrent
    IrreducibleC (censoredKernel P T) ∧
    (∀ i : T, PositiveRecurrent (censoredKernel P T) i) ∧
    -- `π_T P(T) = π_T`
    (∀ j : T, HasSum (fun i : T => π i * censoredKernel P T i j) (π j)) ∧
    -- the stationary probability vector of the restricted chain is `π_T / (π_T 1)`
    IsStationaryC (censoredKernel P T) (fun i : T => π i / ∑' k : T, π k) ∧
    (∀ μ : T → ℝ, IsStationaryC (censoredKernel P T) μ →
      μ = fun i : T => π i / ∑' k : T, π k) := by
  classical
  obtain ⟨t0, ht0⟩ := hT
  have hP0 := hP.1
  have hrow := hrow_of P hP
  set K := censoredKernel P T with hK
  have hcm_fin : ∀ (a b : T), censoredMatrix P T a b ≠ ⊤ := fun a b =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (cm_le_one P T hP0 hrow hirr hpos ht0 a b)
  have hK0 : ∀ a b, 0 ≤ K a b := fun a b => ENNReal.toReal_nonneg
  have hKof : ∀ a b, ENNReal.ofReal (K a b) = censoredMatrix P T a b := fun a b =>
    ENNReal.ofReal_toReal (hcm_fin a b)
  have hKrow : ∀ a, ∑' b, ENNReal.ofReal (K a b) = 1 := fun a => by
    simp_rw [hKof]; exact cm_row P T hP0 hrow hirr hpos ht0 a
  set C' := ser (QK P T) * PK P with hC'
  have hM : ∀ x y, y ∉ T → rc (fun y => y ∈ T) C' x y = 0 := fun x y hy =>
    rc_neg (A := fun y => y ∈ T) _ _ hy
  have hPKK : PK K = resK T (rc (fun y => y ∈ T) C') := Ker.ext fun a b => by
    show ENNReal.ofReal (K a b) = rc (fun y => y ∈ T) C' a b
    rw [hKof, rc_pos (A := fun y => y ∈ T) _ _ b.2, cm_eq]
  -- irreducibility of the censored chain
  have hirrK : IrreducibleC K := by
    intro a b
    obtain ⟨s, hs⟩ := hirr a b
    have h1 : (PK P ^ s) a b ≠ 0 := by
      rw [← stepPow_ofReal P hP0 hrow]; exact (ENNReal.ofReal_pos.mpr hs).ne'
    have h2 : ser (rc (fun y => y ∈ T) C') a b ≠ 0 := by
      rw [← cens P T (fun y => y ∈ T) (fun y h => h) a b.2,
        rc_congr (A' := fun _ => True) (fun y => by tauto), rc_true, ser_ap]
      exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr h1)
        (ENNReal.le_tsum (f := fun n => (PK P ^ n) a b) s))
    obtain ⟨t, ht⟩ : ∃ t, (rc (fun y => y ∈ T) C' ^ t) a b ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h2 (by rw [ser_ap]; exact ENNReal.tsum_eq_zero.mpr hc)
    refine ⟨t, ?_⟩
    have : ENNReal.ofReal (stepPow K t a b) ≠ 0 := by
      rw [stepPow_ofReal K hK0 hKrow, hPKK, resK_pow T _ hM]; exact ht
    exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr this)
  -- positive recurrence of the censored chain
  have hprK : ∀ a : T, PositiveRecurrent K a := by
    intro a
    rw [pr_iff K hK0 hKrow a]
    simp_rw [AV_pow]
    rw [ENNReal.tsum_comm]
    have hM2 : ∀ x y, y ∉ T → rc (fun y => y ∈ T ∧ y ≠ (a : S)) C' x y = 0 := fun x y hy =>
      rc_neg (A := fun y => y ∈ T ∧ y ≠ (a : S)) _ _ (fun h => hy h.1)
    have hres : rc (fun z => z ≠ a) (PK K) = resK T (rc (fun y => y ∈ T ∧ y ≠ (a : S)) C') :=
      Ker.ext fun u v => by
        by_cases hv : v = a
        · rw [rc_neg (A := fun z => z ≠ a) _ _ (not_not.mpr hv)]
          show 0 = rc (fun y => y ∈ T ∧ y ≠ (a : S)) C' u v
          rw [rc_neg (A := fun y => y ∈ T ∧ y ≠ (a : S)) _ _
            (by rintro ⟨-, h⟩; exact h (congrArg Subtype.val hv))]
        · rw [rc_pos (A := fun z => z ≠ a) _ _ hv]
          show ENNReal.ofReal (K u v) = rc (fun y => y ∈ T ∧ y ≠ (a : S)) C' u v
          rw [rc_pos (A := fun y => y ∈ T ∧ y ≠ (a : S)) _ _ ⟨v.2, fun h => hv (Subtype.ext h)⟩,
            hKof, cm_eq]
    have e : ∀ b : T, ∑' t, ((rc (fun z => z ≠ a) (PK K)) ^ t) a b =
        ser (rc (fun z => z ≠ (a : S)) (PK P)) a b := fun b => by
      rw [← ser_ap, hres, resK_ser T _ hM2,
        ← cens P T (fun y => y ∈ T ∧ y ≠ (a : S)) (fun y h => h.1) a b.2]
      congr 2
      apply rc_congr
      intro y
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact fun e => h (e ▸ a.2)
        · exact h
      · intro h
        by_cases hy : y ∈ T
        · exact Or.inr ⟨hy, h⟩
        · exact Or.inl hy
    rw [tsum_congr e]
    have horig := (pr_iff P hP0 hrow a).mp (hpos a)
    simp_rw [AV_pow] at horig
    refine ne_top_of_le_ne_top horig ?_
    calc ∑' b : T, ser (rc (fun z => z ≠ (a : S)) (PK P)) a b
        ≤ ∑' y, ser (rc (fun z => z ≠ (a : S)) (PK P)) a y :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
            (fun y => ser (rc (fun z => z ≠ (a : S)) (PK P)) a y)
      _ = _ := by simp only [ser_ap]; exact ENNReal.tsum_comm
  -- stationarity of π on T
  have hstat : ∀ j : T, HasSum (fun i : T => π i * K i j) (π j) := by
    intro j
    apply hasSum_of_ofReal _ _ (fun (i : T) => mul_nonneg (hπ.1 i) (hK0 i j)) (hπ.1 j)
    rw [← stat_T P T hP0 hrow hirr hpos ht0 π hπ j]
    exact tsum_congr fun i => by rw [ENNReal.ofReal_mul (hπ.1 i), hKof]
  -- positivity
  have hπpos : 0 < π t0 := by
    obtain ⟨x, hx⟩ : ∃ x, 0 < π x := by
      by_contra hc
      push Not at hc
      have h0 : ∀ x, π x = 0 := fun x => le_antisymm (hc x) (hπ.1 x)
      have := hπ.2.1.tsum_eq
      simp [h0] at this
    obtain ⟨L, hL⟩ := hirr x t0
    have hm := inv_ofReal P hP0 π hπ.1 hπ.2.2
    have h1 := ns_sub_iter P (fun x => ENNReal.ofReal (π x)) hm L x t0
    have h2 : 0 < ENNReal.ofReal (π x) * g72mab_PS P x L t0 (fun _ => True) :=
      ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hx).ne' (g72mab_stepPow_PS P hP0 x L t0 hL)
    exact ENNReal.ofReal_pos.mp (lt_of_lt_of_le h2 h1)
  have hsumT : Summable (fun k : T => π k) := hπ.2.1.summable.subtype T
  have hs : 0 < ∑' k : T, π k := hsumT.tsum_pos (fun k => hπ.1 k) ⟨t0, ht0⟩ hπpos
  have hν : IsStationaryC K (fun i : T => π i / ∑' k : T, π k) := by
    refine ⟨fun i => div_nonneg (hπ.1 i) hs.le, ?_, fun j => ?_⟩
    · have := hsumT.hasSum.div_const (∑' k : T, π k)
      rwa [div_self hs.ne'] at this
    · simp_rw [div_mul_eq_mul_div]
      exact (hstat j).div_const _
  refine ⟨fun i => ?_, fun i j₀ hj₀ js hjs => ?_, fun i _ => ?_, hirrK, hprK, hstat, hν,
    fun μ hμ => stat_uniq K hK0 hKrow hirrK ⟨t0, ht0⟩ (hprK _) μ _ hμ hν⟩
  · rw [ENNReal.summable.hasSum_iff]; exact rl_sum P T hP0 hrow hirr hpos ht0 i
  · rw [rl_split P T hj₀ js i, rl_chain P T js hjs j₀ hj₀]
  · rw [ENNReal.summable.hasSum_iff]; exact cm_row P T hP0 hrow hirr hpos ht0 i
