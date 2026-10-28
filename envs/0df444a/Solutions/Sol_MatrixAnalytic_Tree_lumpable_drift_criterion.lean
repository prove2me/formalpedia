-- Prove2me | solution 1 for MatrixAnalytic.Tree.lumpable_drift_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T15:38:57.644509+00:00
-- url     : https://prove2.me/submissions/1d2c0441-958b-483b-a840-e10122edbf3f

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Passage
import Theorems.Thm_MatrixAnalytic_Tree_positive_recurrent_iff_sp_lt_one
import Theorems.Thm_MatrixAnalytic_Stability_drift_criterion
import Theorems.Thm_MatrixAnalytic_Stability_positive_recurrent_iff_sp_lt_one

open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace S203LD

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


end Gen

section TreeFacts
open MatrixAnalytic.Tree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gen_nil (T : TreeData ι) (j : ι) (y : TreeState ι) :
    gen T (some ([], j)) y =
      (if y = none then T.d j else 0) + ∑ k, (if y = some ([], k) then T.C j k else 0)
      + ∑ m, ∑ k, (if y = some ([m], k) then T.A m j k else 0) := by
  rcases y with _ | ⟨l', k'⟩
  · simp [gen]
  · simp only [gen, tsum_fintype, reduceCtorEq, if_false, zero_add, Option.some.injEq,
      Prod.mk.injEq]
    have h3 : ∀ m : ι, ([] : List ι) ≠ l' ++ [m] := fun m h => by simp at h
    simp only [h3, if_false, Finset.sum_const_zero, add_zero, List.nil_append]
    congr 1
    · by_cases hl : l' = [] <;> simp [hl]
    · refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hl : l' = [m] <;> simp [hl]

lemma gen_snoc (T : TreeData ι) (l0 : List ι) (m0 j : ι) (y : TreeState ι) :
    gen T (some (l0 ++ [m0], j)) y =
      ∑ k, (if y = some (l0 ++ [m0], k) then T.C j k else 0)
      + ∑ m, ∑ k, (if y = some (l0 ++ [m0] ++ [m], k) then T.A m j k else 0)
      + ∑ k, (if y = some (l0, k) then T.D m0 j k else 0) := by
  rcases y with _ | ⟨l', k'⟩
  · simp [gen]
  · simp only [gen, tsum_fintype, Option.some.injEq, Prod.mk.injEq]
    congr 1
    · congr 1
      · by_cases hl : l' = l0 ++ [m0] <;> simp [hl]
      · refine Finset.sum_congr rfl fun m _ => ?_
        by_cases hl : l' = l0 ++ [m0] ++ [m] <;> simp_all
    · by_cases hl : l' = l0
      · subst hl
        rw [Finset.sum_eq_single m0]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [hl]
        · intro b _
          rw [if_neg]
          intro h
          exact hl (List.append_singleton_inj.mp h).1.symm
end TreeFacts

section TR
open MatrixAnalytic.Tree
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

end TR

section Defs
open MatrixAnalytic.Tree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def qv (T : TreeData ι) (i : ι) : ℝ := - T.C i i
noncomputable def As (T : TreeData ι) (i k : ι) : ℝ := ∑ m, T.A m i k
noncomputable def A0 (T : TreeData ι) (i k : ι) : ℝ := As T i k / qv T i
noncomputable def A1 (T : TreeData ι) (i k : ι) : ℝ := if i = k then 0 else T.C i k / qv T i
noncomputable def A2 (T : TreeData ι) (D : ι → ι → ℝ) (i k : ι) : ℝ := D i k / qv T i
noncomputable def Bm (T : TreeData ι) (i k : ι) : ℝ :=
  A1 T i k + T.d i * T.a k / (qv T i * ∑ m, T.a m)
noncomputable def PQ (T : TreeData ι) (D : ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  MatrixAnalytic.Stability.qbdP (Bm T) (A0 T) (A1 T) (A2 T D)

def psi (i0 : ι) : TreeState ι → ℕ × ι
  | none => (0, i0)
  | some (l, i) => (l.length + 1, i)

lemma hold_some (T : TreeData ι) (l : List ι) (i : ι) :
    holdRate (gen T) (some (l, i)) = qv T i := by
  unfold holdRate qv
  simp [gen]

lemma qv_pos (T : TreeData ι) (hT : IsTreeProcess T) (i : ι) : 0 < qv T i := by
  rw [← hold_some T [] i]
  rcases Relation.ReflTransGen.cases_head (hT.2 (some ([], i)) none) with h | ⟨c, ⟨hne, hpos⟩, -⟩
  · exact absurd h (by simp)
  · exact lt_of_lt_of_le hpos (g72mab_qge (gen T) hT.1 _ c hne)

lemma A_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (m i k : ι) : 0 ≤ T.A m i k := by
  have h := hT.1.1 (some ([], i)) (some ([m], k)) (by simp)
  rw [gen_nil] at h
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true, reduceCtorEq,
    if_false, zero_add, List.nil_eq, ne_eq] at h
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  simpa [Finset.sum_ite_eq'] using h

lemma D_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (m i k : ι) : 0 ≤ T.D m i k := by
  have h := hT.1.1 (some ([] ++ [m], i)) (some ([], k)) (by simp)
  rw [gen_snoc] at h
  simpa using h

lemma d_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (i : ι) : 0 ≤ T.d i := by
  have h := hT.1.1 (some ([], i)) none (by simp)
  simpa [gen] using h

lemma a_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (j : ι) : 0 ≤ T.a j := by
  have h := hT.1.1 none (some ([], j)) (by simp)
  simpa [gen] using h

lemma C_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (i k : ι) (h : i ≠ k) : 0 ≤ T.C i k := by
  have h := hT.1.1 (some ([], i)) (some ([], k)) (by simp [h])
  rw [gen_nil] at h
  simpa using h

lemma rowN (T : TreeData ι) (hT : IsTreeProcess T) (j : ι) :
    T.d j + ∑ k, T.C j k + ∑ m, ∑ k, T.A m j k = 0 := by
  have h1 : HasSum (gen T (some ([], j))) (T.d j + ∑ k, T.C j k + ∑ m, ∑ k, T.A m j k) := by
    have e : gen T (some ([], j)) = fun y => (if y = none then T.d j else 0) +
        ∑ k, (if y = some ([], k) then T.C j k else 0)
        + ∑ m, ∑ k, (if y = some ([m], k) then T.A m j k else 0) := funext (gen_nil T j)
    rw [e]
    refine ((hasSum_ite_eq none (T.d j)).add (hasSum_sum fun k _ => hasSum_ite_eq _ _)).add
      (hasSum_sum fun m _ => hasSum_sum fun k _ => hasSum_ite_eq _ _)
  exact h1.unique (hT.1.2 _)

lemma rowS (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (j : ι) : ∑ k, T.C j k + ∑ m, ∑ k, T.A m j k + ∑ k, D j k = 0 := by
  have h1 : HasSum (gen T (some ([] ++ [j], j)))
      (∑ k, T.C j k + ∑ m, ∑ k, T.A m j k + ∑ k, T.D j j k) := by
    have e : gen T (some ([] ++ [j], j)) = fun y =>
        ∑ k, (if y = some ([] ++ [j], k) then T.C j k else 0)
        + ∑ m, ∑ k, (if y = some ([] ++ [j] ++ [m], k) then T.A m j k else 0)
        + ∑ k, (if y = some ([], k) then T.D j j k else 0) := funext (gen_snoc T [] j j)
    rw [e]
    refine ((hasSum_sum fun k _ => hasSum_ite_eq _ _).add
      (hasSum_sum fun m _ => hasSum_sum fun k _ => hasSum_ite_eq _ _)).add
      (hasSum_sum fun k _ => hasSum_ite_eq _ _)
  have := h1.unique (hT.1.2 _)
  rwa [hD] at this

lemma jump_gen (T : TreeData ι) (l : List ι) (j : ι) (E : TreeState ι → ℝ)
    (hq : 0 < qv T j) (hE : E (some (l, j)) = 0)
    (hgen : ∀ y, gen T (some (l, j)) y = E y + ∑ k, (if y = some (l, k) then T.C j k else 0)
      + ∑ m, ∑ k, (if y = some (l ++ [m], k) then T.A m j k else 0)) (y : TreeState ι) :
    jumpP (gen T) (some (l, j)) y = E y / qv T j + ∑ k, (if y = some (l, k) then A1 T j k else 0)
      + ∑ m, ∑ k, (if y = some (l ++ [m], k) then T.A m j k / qv T j else 0) := by
  unfold jumpP
  rw [hold_some, if_neg hq.ne']
  by_cases hy : y = some (l, j)
  · subst hy
    rw [if_pos rfl, hE, zero_div, zero_add]
    have h2 : ∀ m k, (some (l, j) : TreeState ι) ≠ some (l ++ [m], k) := by
      intro m k h; simp at h
    simp [h2, A1]
  · rw [if_neg hy, hgen, add_div, add_div, Finset.sum_div, Finset.sum_div]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : y = some (l, k)
      · subst hk
        have hjk : j ≠ k := fun h => hy (by rw [h])
        simp [A1, hjk]
      · simp [hk]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
end Defs

section Lump
open MatrixAnalytic.Tree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma tsum_ind {V : Type*} [DecidableEq V] (p : V) (c : ℝ≥0∞) :
    ∑' y : V, (if y = p then c else 0) = c := by
  rw [tsum_eq_single p]
  · simp
  · intro b hb; simp [hb]

lemma lump_core (T : TreeData ι) (hT : IsTreeProcess T) (i0 : ι) (l : List ι) (j : ι)
    (E : TreeState ι → ℝ) (hE : ∀ y, 0 ≤ E y) (n : ℕ) (k0 : ι) :
    ∑' y, (if psi i0 y = (n, k0) then ENNReal.ofReal (E y / qv T j
      + ∑ k, (if y = some (l, k) then A1 T j k else 0)
      + ∑ m, ∑ k, (if y = some (l ++ [m], k) then T.A m j k / qv T j else 0)) else 0)
    = ∑' y, (if psi i0 y = (n, k0) then ENNReal.ofReal (E y / qv T j) else 0)
      + (if n = l.length + 1 then ENNReal.ofReal (A1 T j k0) else 0)
      + (if n = l.length + 1 + 1 then ENNReal.ofReal (A0 T j k0) else 0) := by
  have hq := qv_pos T hT j
  have hA1 : ∀ k, 0 ≤ A1 T j k := by
    intro k; unfold A1; split_ifs with h
    · exact le_rfl
    · exact div_nonneg (C_nonneg T hT j k h) hq.le
  have hAq : ∀ m k, 0 ≤ T.A m j k / qv T j := fun m k => div_nonneg (A_nonneg T hT m j k) hq.le
  have hpt : ∀ y, (if psi i0 y = (n, k0) then ENNReal.ofReal (E y / qv T j
      + ∑ k, (if y = some (l, k) then A1 T j k else 0)
      + ∑ m, ∑ k, (if y = some (l ++ [m], k) then T.A m j k / qv T j else 0)) else 0)
      = (if psi i0 y = (n, k0) then ENNReal.ofReal (E y / qv T j) else 0)
        + ∑ k, (if y = some (l, k) then
            (if psi i0 (some (l, k)) = (n, k0) then ENNReal.ofReal (A1 T j k) else 0) else 0)
        + ∑ m, ∑ k, (if y = some (l ++ [m], k) then
            (if psi i0 (some (l ++ [m], k)) = (n, k0) then ENNReal.ofReal (T.A m j k / qv T j)
              else 0) else 0) := by
    intro y
    by_cases hpw : psi i0 y = (n, k0)
    · rw [if_pos hpw, if_pos hpw]
      rw [ENNReal.ofReal_add (add_nonneg (div_nonneg (hE y) hq.le)
          (Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hA1]))
          (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hAq]),
        ENNReal.ofReal_add (div_nonneg (hE y) hq.le)
          (Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hA1]),
        ENNReal.ofReal_sum_of_nonneg (fun k _ => by split_ifs <;> simp [hA1]),
        ENNReal.ofReal_sum_of_nonneg (fun m _ =>
          Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hAq])]
      congr 1
      · congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : y = some (l, k)
        · rw [if_pos hk, if_pos hk, ← hk, if_pos hpw]
        · rw [if_neg hk, if_neg hk, ENNReal.ofReal_zero]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by split_ifs <;> simp [hAq])]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : y = some (l ++ [m], k)
        · rw [if_pos hk, if_pos hk, ← hk, if_pos hpw]
        · rw [if_neg hk, if_neg hk, ENNReal.ofReal_zero]
    · rw [if_neg hpw, if_neg hpw, zero_add]
      symm
      refine add_eq_zero.mpr ⟨Finset.sum_eq_zero fun k _ => ?_,
        Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => ?_⟩
      · by_cases hk : y = some (l, k)
        · rw [if_pos hk, ← hk, if_neg hpw]
        · rw [if_neg hk]
      · by_cases hk : y = some (l ++ [m], k)
        · rw [if_pos hk, ← hk, if_neg hpw]
        · rw [if_neg hk]
  simp_rw [hpt]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
    Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), tsum_ind]
  congr 1
  · congr 1
    simp only [psi, Prod.mk.injEq]
    by_cases hn : n = l.length + 1
    · rw [if_pos hn]
      simp only [hn.symm, true_and]
      rw [Finset.sum_ite_eq']; simp
    · rw [if_neg hn]
      exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hn h.1.symm)]
  · simp only [psi, Prod.mk.injEq, List.length_append, List.length_singleton]
    by_cases hn : n = l.length + 1 + 1
    · rw [if_pos hn]
      simp only [hn.symm, true_and]
      simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => hAq m k0), A0, As, Finset.sum_div]
    · rw [if_neg hn]
      exact Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => by
        rw [if_neg (fun h => hn h.1.symm)]
end Lump

section Lump2
open MatrixAnalytic.Tree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma lumpJ (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (i0 : ι) (l : List ι) (j : ι) (n : ℕ) (k0 : ι) (hn : n ≠ 0) :
    ∑' y, (if psi i0 y = (n, k0) then ENNReal.ofReal (jumpP (gen T) (some (l, j)) y) else 0)
      = ENNReal.ofReal (PQ T D (psi i0 (some (l, j))) (n, k0)) := by
  have hq := qv_pos T hT j
  rcases List.eq_nil_or_concat l with hl | ⟨l0, m0, hl⟩
  · subst hl
    have hJ := jump_gen T [] j (fun y => if y = none then T.d j else 0) hq (by simp)
      (fun y => by rw [gen_nil]; rfl)
    simp_rw [hJ]
    rw [lump_core T hT i0 [] j _ (fun y => by split_ifs <;> simp [d_nonneg T hT])]
    have h0 : ∑' y : TreeState ι, (if psi i0 y = (n, k0) then
        ENNReal.ofReal ((if y = none then T.d j else 0) / qv T j) else 0) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr fun y => ?_
      by_cases hy : y = none
      · subst hy; rw [if_neg]; simp [psi, Ne.symm hn]
      · simp [hy]
    rw [h0, zero_add]
    simp only [psi, PQ, MatrixAnalytic.Stability.qbdP, List.length_nil]
    rcases n with _ | _ | _ | n
    · exact absurd rfl hn
    · simp
    · simp
    · simp
  · rw [List.concat_eq_append] at hl
    subst hl
    have hJ := jump_gen T (l0 ++ [m0]) j
      (fun y => ∑ k, (if y = some (l0, k) then T.D m0 j k else 0)) hq
      (by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_neg]; intro h; simp at h)
      (fun y => by rw [gen_snoc]; ring)
    simp_rw [hJ]
    rw [lump_core T hT i0 _ j _ (fun y => Finset.sum_nonneg fun k _ => by
      split_ifs <;> simp [D_nonneg T hT])]
    have h0 : ∑' y : TreeState ι, (if psi i0 y = (n, k0) then
        ENNReal.ofReal ((∑ k, (if y = some (l0, k) then T.D m0 j k else 0)) / qv T j) else 0)
        = if n = l0.length + 1 then ENNReal.ofReal (A2 T D j k0) else 0 := by
      rw [tsum_eq_single (some (l0, k0))]
      · simp only [psi, Prod.mk.injEq, and_true, Option.some.injEq, true_and]
        simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        by_cases hn' : n = l0.length + 1
        · rw [if_pos hn'.symm, if_pos hn', A2, hD]
        · rw [if_neg (fun h => hn' h.symm), if_neg hn']
      · intro y hy
        by_cases hp : psi i0 y = (n, k0)
        · rw [if_pos hp, Finset.sum_eq_zero]
          · simp
          · intro k _
            rw [if_neg]
            intro hk
            subst hk
            simp only [psi, Prod.mk.injEq] at hp
            exact hy (by rw [hp.2])
        · rw [if_neg hp]
    rw [h0]
    simp only [psi, PQ, MatrixAnalytic.Stability.qbdP, List.length_append, List.length_singleton]
    set L := l0.length
    by_cases h1 : n = L + 1
    · subst h1; simp
    · by_cases h2 : n = L + 2
      · subst h2; simp
      · by_cases h3 : n = L + 3
        · subst h3; simp
        · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp
end Lump2

section LumpPS

lemma lump_PS {V W : Type*} [DecidableEq W] (P : V → V → ℝ) (Q : W → W → ℝ) (ψ : V → W)
    (AV : V → Prop) (AW : W → Prop) [DecidablePred AV] [DecidablePred AW]
    (hA : ∀ y, AV y ↔ AW (ψ y))
    (hJ : ∀ z, AV z → ∀ w, AW w →
      ∑' y, (if ψ y = w then ENNReal.ofReal (P z y) else 0) = ENNReal.ofReal (Q (ψ z) w))
    (x : V) (hx : AV x) :
    ∀ t w, AW w → ∑' y, (if ψ y = w then g72mab_PS P x t y AV else 0) = g72mab_PS Q (ψ x) t w AW := by
  classical
  intro t
  induction t with
  | zero =>
    intro w _
    rw [g72mab_PS_zero]
    simp_rw [g72mab_PS_zero]
    rw [tsum_eq_single x]
    · simp
    · intro b hb; simp [Ne.symm hb]
  | succ t ih =>
    intro w hw
    rw [g72mab_PS_snoc Q]
    simp_rw [g72mab_PS_snoc P]
    have e1 : ∀ z, (if t = 0 ∨ AV z then g72mab_PS P x t z AV else 0) =
        (if AV z then g72mab_PS P x t z AV else 0) := by
      intro z
      by_cases hz : AV z
      · simp [hz]
      · rw [if_neg hz]
        split_ifs with h
        · rcases h with h | h
          · subst h; rw [g72mab_PS_zero, if_neg]; rintro rfl; exact hz hx
          · exact absurd h hz
        · rfl
    have e2 : ∀ u, (if t = 0 ∨ AW u then g72mab_PS Q (ψ x) t u AW else 0) =
        (if AW u then g72mab_PS Q (ψ x) t u AW else 0) := by
      intro u
      by_cases hu : AW u
      · simp [hu]
      · rw [if_neg hu]
        split_ifs with h
        · rcases h with h | h
          · subst h; rw [g72mab_PS_zero, if_neg]; intro h; rw [← h] at hu; exact hu ((hA x).mp hx)
          · exact absurd h hu
        · rfl
    simp_rw [e1, e2]
    calc ∑' y, (if ψ y = w then ∑' z, (if AV z then g72mab_PS P x t z AV else 0) *
            ENNReal.ofReal (P z y) else 0)
        = ∑' z, (if AV z then g72mab_PS P x t z AV else 0) *
            ∑' y, (if ψ y = w then ENNReal.ofReal (P z y) else 0) := by
          simp_rw [g72mab_ite_tsum]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun z => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun y => ?_
          split_ifs <;> simp
      _ = ∑' z, (if AV z then g72mab_PS P x t z AV * ENNReal.ofReal (Q (ψ z) w) else 0) := by
          refine tsum_congr fun z => ?_
          by_cases hz : AV z
          · rw [if_pos hz, if_pos hz, hJ z hz w hw]
          · rw [if_neg hz, if_neg hz, zero_mul]
      _ = ∑' u, ∑' z, (if ψ z = u then
            (if AV z then g72mab_PS P x t z AV * ENNReal.ofReal (Q (ψ z) w) else 0) else 0) := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun z => ?_
          rw [tsum_eq_single (ψ z)]
          · simp
          · intro b hb; rw [if_neg (Ne.symm hb)]
      _ = ∑' u, (if AW u then g72mab_PS Q (ψ x) t u AW else 0) * ENNReal.ofReal (Q u w) := by
          refine tsum_congr fun u => ?_
          by_cases hu : AW u
          · rw [if_pos hu, ← ih u hu, ← ENNReal.tsum_mul_right]
            refine tsum_congr fun z => ?_
            by_cases hzu : ψ z = u
            · subst hzu; rw [if_pos rfl, if_pos rfl, if_pos ((hA z).mpr hu)]
            · rw [if_neg hzu, if_neg hzu, zero_mul]
          · rw [if_neg hu, zero_mul]
            refine ENNReal.tsum_eq_zero.mpr fun z => ?_
            by_cases hzu : ψ z = u
            · subst hzu; rw [if_pos rfl, if_neg (fun h => hu ((hA z).mp h))]
            · rw [if_neg hzu]
end LumpPS

section Rrel
open MatrixAnalytic.Tree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def AW (w : ℕ × ι) : Prop := w.1 ≠ 0

instance : DecidablePred (AW : ℕ × ι → Prop) := fun w => inferInstanceAs (Decidable (w.1 ≠ 0))

noncomputable def VV (T : TreeData ι) (D : ι → ι → ℝ) (k j : ι) : ℝ≥0∞ :=
  ∑' t, g72mab_PS (PQ T D) ((1 : ℕ), k) t ((1 : ℕ), j) AW

lemma N_eq0 (T : TreeData ι) (i j : ι) :
    matN T i j = (∑' t, g72mab_PS (jumpP (gen T)) (some ([], i)) t (some ([], j))
      (fun w => w ≠ none)) * ENNReal.ofReal (holdRate (gen T) (some ([], j)))⁻¹ := by
  classical
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

lemma N_eq (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (k j : ι) : matN T k j = VV T D k j * ENNReal.ofReal (qv T j)⁻¹ := by
  classical
  rw [N_eq0, hold_some]
  congr 1
  unfold VV
  refine tsum_congr fun t => ?_
  have hL := lump_PS (jumpP (gen T)) (PQ T D) (psi k) (fun w => w ≠ none) AW
    (fun y => by rcases y with _ | ⟨l, i⟩ <;> simp [psi, AW])
    (fun z hz w hw => by
      rcases z with _ | ⟨l, i⟩
      · exact absurd rfl hz
      · obtain ⟨n, k0⟩ := w
        exact lumpJ T hT D hD k l i n k0 hw)
    (some ([], k)) (by simp) t ((1 : ℕ), j) (by simp [AW])
  have hpk : psi k (some ([], k)) = ((1 : ℕ), k) := rfl
  rw [hpk] at hL
  rw [← hL, tsum_eq_single (some ([], j))]
  · simp [psi]
  · intro y hy
    rw [if_neg]
    intro h
    rcases y with _ | ⟨l, i⟩
    · simp [psi] at h
    · simp only [psi, Prod.mk.injEq, add_eq_right, List.length_eq_zero_iff] at h
      exact hy (by rw [h.1, h.2])

lemma Rq_eq (T : TreeData ι) (D : ι → ι → ℝ) (i j : ι) :
    MatrixAnalytic.Stability.matR (PQ T D) i j =
      ∑ k, ENNReal.ofReal (A0 T i k) * VV T D k j := by
  classical
  have h0 : MatrixAnalytic.Stability.matR (PQ T D) i j =
      ∑' t, g72mab_PS (PQ T D) ((0 : ℕ), i) t ((1 : ℕ), j) AW := by
    unfold MatrixAnalytic.Stability.matR MatrixAnalytic.Stability.expVisitsAvoid g72mab_PS
    refine tsum_congr fun t => tsum_congr fun ω => ?_
    by_cases h1 : ω 0 = ((0 : ℕ), i) ∧ ω (Fin.last t) = ((1 : ℕ), j) ∧
        ∀ s : Fin (t + 1), s ≠ 0 → ω s ∉ MatrixAnalytic.Stability.level 0
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, fun m hm _ => h1.2.2 m hm⟩]; rfl
    · rw [if_neg h1, if_neg]
      intro h2
      refine h1 ⟨h2.1, h2.2.1, fun m hm => ?_⟩
      by_cases hml : m = Fin.last t
      · rw [hml, h2.2.1]; simp [MatrixAnalytic.Stability.level]
      · simpa [MatrixAnalytic.Stability.level, AW] using h2.2.2 m hm hml
  rw [h0, tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero, if_neg (by simp), zero_add]
  have hstep : ∀ t, g72mab_PS (PQ T D) ((0 : ℕ), i) (t + 1) ((1 : ℕ), j) AW =
      ∑' k, ENNReal.ofReal (A0 T i k) * g72mab_PS (PQ T D) ((1 : ℕ), k) t ((1 : ℕ), j) AW := by
    intro t
    rw [g72mab_PS_cons]
    have hinj : Function.Injective (fun k : ι => ((1 : ℕ), k)) := fun a b h => by
      simpa using h
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun k => ?_
      simp [PQ, MatrixAnalytic.Stability.qbdP, AW]
    · intro z hz
      rw [Function.mem_support] at hz
      obtain ⟨n, k⟩ := z
      rcases n with _ | _ | n
      · exfalso; apply hz
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht; rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg (by simp), mul_zero]
        · rw [if_neg (by simp [AW]; omega), mul_zero]
      · exact ⟨k, rfl⟩
      · exfalso; apply hz
        simp [PQ, MatrixAnalytic.Stability.qbdP]
  simp_rw [hstep]
  rw [ENNReal.tsum_comm, tsum_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.tsum_mul_left]; rfl

lemma Rt_eq (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (i j : ι) : matR T i j =
      (∑ k, ENNReal.ofReal (As T i k) * VV T D k j) * ENNReal.ofReal (qv T j)⁻¹ := by
  unfold matR matRi matMulE ennMat
  simp_rw [N_eq T hT D hD, tsum_fintype]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [As, ENNReal.ofReal_sum_of_nonneg (fun m _ => A_nonneg T hT m i k), Finset.sum_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring
end Rrel

section Spec
open MatrixAnalytic.Tree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sr_conj (M : Matrix ι ι ℂ) (u : ι → ℂ) (hu : ∀ i, u i ≠ 0) :
    spectralRadius ℂ (Matrix.of fun i j => u i * M i j * (u j)⁻¹) = spectralRadius ℂ M := by
  let U : (Matrix ι ι ℂ)ˣ := ⟨Matrix.diagonal u, Matrix.diagonal (fun i => (u i)⁻¹),
    by rw [Matrix.diagonal_mul_diagonal]; simp [hu],
    by rw [Matrix.diagonal_mul_diagonal]; simp [hu]⟩
  have hU : (Matrix.of fun i j => u i * M i j * (u j)⁻¹) =
      (U : Matrix ι ι ℂ) * M * ((U⁻¹ : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) := by
    change _ = Matrix.diagonal u * M * Matrix.diagonal (fun i => (u i)⁻¹)
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [hU]
  unfold spectralRadius
  rw [spectrum.units_conjugate]

lemma spec_equiv (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D) :
    ((∀ i j : ι, matR T i j ≠ ⊤) ∧
        spectralRadius ℂ (Matrix.of fun i j : ι => (((matR T i j).toReal : ℝ) : ℂ)) < 1) ↔
    ((∀ i j : ι, MatrixAnalytic.Stability.matR (PQ T D) i j ≠ ⊤) ∧
        spectralRadius ℂ (Matrix.of fun i j : ι =>
          (((MatrixAnalytic.Stability.matR (PQ T D) i j).toReal : ℝ) : ℂ)) < 1) := by
  set S : ι → ι → ℝ≥0∞ := fun i j => ∑ k, ENNReal.ofReal (As T i k) * VV T D k j with hS
  have hq := qv_pos T hT
  have hRt : ∀ i j, matR T i j = S i j * ENNReal.ofReal (qv T j)⁻¹ := fun i j => Rt_eq T hT D hD i j
  have hRq : ∀ i j, MatrixAnalytic.Stability.matR (PQ T D) i j =
      ENNReal.ofReal (qv T i)⁻¹ * S i j := by
    intro i j
    rw [Rq_eq, hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [A0, div_eq_mul_inv, ENNReal.ofReal_mul (show 0 ≤ As T i k from
      Finset.sum_nonneg fun m _ => A_nonneg T hT m i k)]
    ring
  have hc : ∀ j, ENNReal.ofReal (qv T j)⁻¹ ≠ 0 := fun j => by
    simpa using inv_pos.mpr (hq j)
  have hfin : (∀ i j, matR T i j ≠ ⊤) ↔ (∀ i j, S i j ≠ ⊤) := by
    simp only [hRt]
    refine forall₂_congr fun i j => ?_
    constructor
    · intro h hS'; apply h; rw [hS', ENNReal.top_mul (hc j)]
    · intro h; exact ENNReal.mul_ne_top h ENNReal.ofReal_ne_top
  have hfin' : (∀ i j, MatrixAnalytic.Stability.matR (PQ T D) i j ≠ ⊤) ↔ (∀ i j, S i j ≠ ⊤) := by
    simp only [hRq]
    refine forall₂_congr fun i j => ?_
    constructor
    · intro h hS'; apply h; rw [hS', ENNReal.mul_top (hc i)]
    · intro h; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h
  rw [hfin, hfin']
  refine and_congr_right fun hSf => ?_
  have hM : (Matrix.of fun i j : ι => (((matR T i j).toReal : ℝ) : ℂ)) =
      Matrix.of fun i j => ((qv T i : ℝ) : ℂ) *
        (((MatrixAnalytic.Stability.matR (PQ T D) i j).toReal : ℝ) : ℂ) * ((qv T j : ℝ) : ℂ)⁻¹ := by
    ext i j
    simp only [Matrix.of_apply, hRt, hRq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (hq i).le),
      ENNReal.toReal_ofReal (inv_nonneg.mpr (hq j).le)]
    push_cast
    have : ((qv T i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hq i).ne'
    field_simp
  have hsc := sr_conj (Matrix.of fun i j : ι =>
      (((MatrixAnalytic.Stability.matR (PQ T D) i j).toReal : ℝ) : ℂ))
    (fun i => ((qv T i : ℝ) : ℂ)) (fun i => by exact_mod_cast (hq i).ne')
  simp only [Matrix.of_apply] at hsc
  rw [hM, hsc]
end Spec

section QBDProps
open MatrixAnalytic.Tree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sumA_pos (T : TreeData ι) (hT : IsTreeProcess T) (i : ι) : 0 < ∑ m, T.a m := by
  rcases Relation.ReflTransGen.cases_head (hT.2 none (some ([], i))) with h | ⟨c, ⟨hne, hpos⟩, -⟩
  · exact absurd h (by simp)
  · rcases c with _ | ⟨l, k⟩
    · exact absurd rfl hne
    · simp only [gen] at hpos
      split_ifs at hpos with hl
      · exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun m _ => a_nonneg T hT m)
          (Finset.mem_univ k))
      · exact absurd hpos (lt_irrefl 0)

lemma A1_eq (T : TreeData ι) (hT : IsTreeProcess T) (i k : ι) :
    A1 T i k = T.C i k / qv T i + if i = k then 1 else 0 := by
  have hq := qv_pos T hT i
  unfold A1
  split_ifs with h
  · subst h
    have : T.C i i = - qv T i := by simp [qv]
    rw [this, neg_div, div_self hq.ne']; ring
  · ring

lemma A0_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (i k : ι) : 0 ≤ A0 T i k :=
  div_nonneg (Finset.sum_nonneg fun m _ => A_nonneg T hT m i k) (qv_pos T hT i).le

lemma A1_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (i k : ι) : 0 ≤ A1 T i k := by
  unfold A1; split_ifs with h
  · exact le_rfl
  · exact div_nonneg (C_nonneg T hT i k h) (qv_pos T hT i).le

lemma A2_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (i k : ι) : 0 ≤ A2 T D i k := by
  unfold A2; rw [← hD i]; exact div_nonneg (D_nonneg T hT i i k) (qv_pos T hT i).le

lemma Bm_extra_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (i k : ι) :
    0 ≤ T.d i * T.a k / (qv T i * ∑ m, T.a m) :=
  div_nonneg (mul_nonneg (d_nonneg T hT i) (a_nonneg T hT k))
    (mul_nonneg (qv_pos T hT i).le (sumA_pos T hT i).le)

lemma Bm_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (i k : ι) : 0 ≤ Bm T i k :=
  add_nonneg (A1_nonneg T hT i k) (Bm_extra_nonneg T hT i k)

lemma PQ_nonneg (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (x y : ℕ × ι) : 0 ≤ PQ T D x y := by
  unfold PQ MatrixAnalytic.Stability.qbdP
  split_ifs <;> first
    | exact le_rfl | exact Bm_nonneg T hT _ _ | exact A0_nonneg T hT _ _
    | exact A1_nonneg T hT _ _ | exact A2_nonneg T hT D hD _ _

lemma hasSum_level (n : ℕ) (f : ι → ℝ) :
    HasSum (fun w : ℕ × ι => if w.1 = n then f w.2 else 0) (∑ k, f k) := by
  have hinj : Function.Injective (fun k : ι => (n, k)) := fun a b h => by simpa using h
  rw [← hinj.hasSum_iff]
  · simpa [Function.comp_def] using hasSum_fintype f
  · intro x hx
    rw [if_neg]
    intro h; apply hx; exact ⟨x.2, by ext <;> simp [h]⟩

lemma sum_A1 (T : TreeData ι) (hT : IsTreeProcess T) (i : ι) :
    ∑ k, A1 T i k = (∑ k, T.C i k) / qv T i + 1 := by
  simp_rw [A1_eq T hT, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_div]

lemma PQ_stoch (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D) :
    MatrixAnalytic.Stability.IsStochasticC (PQ T D) := by
  refine ⟨PQ_nonneg T hT D hD, fun x => ?_⟩
  obtain ⟨n, i⟩ := x
  have hq := qv_pos T hT i
  have hsA : ∑ k, A0 T i k = (∑ m, ∑ k, T.A m i k) / qv T i := by
    unfold A0 As; rw [← Finset.sum_div, Finset.sum_comm]
  rcases n with _ | n
  · have e : PQ T D ((0 : ℕ), i) = fun w => (if w.1 = 0 then Bm T i w.2 else 0) +
        (if w.1 = 1 then A0 T i w.2 else 0) := by
      funext w; unfold PQ MatrixAnalytic.Stability.qbdP
      split_ifs <;> simp_all
    rw [e]
    convert (hasSum_level 0 (Bm T i)).add (hasSum_level 1 (A0 T i)) using 1
    have hr := rowN T hT i
    have hSa := sumA_pos T hT i
    unfold Bm
    rw [Finset.sum_add_distrib, sum_A1 T hT, hsA, ← Finset.sum_div, ← Finset.mul_sum]
    field_simp
    linarith
  · have e : PQ T D ((n + 1 : ℕ), i) = fun w => (if w.1 = n + 2 then A0 T i w.2 else 0) +
        (if w.1 = n + 1 then A1 T i w.2 else 0) + (if w.1 = n then A2 T D i w.2 else 0) := by
      funext w; unfold PQ MatrixAnalytic.Stability.qbdP
      obtain ⟨m, k⟩ := w
      simp only
      by_cases h1 : m = n + 2
      · subst h1; simp
      · by_cases h2 : m = n + 1
        · subst h2; simp
        · by_cases h3 : m = n
          · subst h3; simp; intro h; omega
          · rw [if_neg (by omega), if_neg h1, if_neg h2, if_neg h3, if_neg h1, if_neg h2,
              if_neg (by omega)]
            simp
    rw [e]
    convert ((hasSum_level (n + 2) (A0 T i)).add (hasSum_level (n + 1) (A1 T i))).add
      (hasSum_level n (A2 T D i)) using 1
    have hr := rowS T hT D hD i
    unfold A2
    rw [sum_A1 T hT, hsA, ← Finset.sum_div]
    field_simp
    linarith
end QBDProps

section Irr
open MatrixAnalytic.Tree
open MatrixAnalytic.Stability (stepPow)

lemma stepPow_nonneg' {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) : ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih => intro x y; simp only [stepPow]; exact tsum_nonneg fun z => mul_nonneg (ih _ _) (hP0 _ _)

lemma stepPow_of_rtg {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) (hs : ∀ t x y, Summable (fun w => stepPow P t x w * P w y))
    (x y : V) (h : Relation.ReflTransGen (fun u v => 0 < P u v) x y) :
    ∃ t, 0 < stepPow P t x y := by
  induction h with
  | refl => exact ⟨0, by simp [stepPow]⟩
  | @tail b c _ hbc ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 1, ?_⟩
    simp only [stepPow]
    refine lt_of_lt_of_le (mul_pos ht hbc) ((hs t x c).le_tsum b fun j _ => ?_)
    exact mul_nonneg (stepPow_nonneg' P hP0 t x j) (hP0 j c)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pos_shift (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (a b : ℕ) (i k : ι)
    (h : 0 < PQ T D ((a + 1 : ℕ), i) ((b + 1 : ℕ), k)) : 0 < PQ T D (a, i) (b, k) := by
  have hB := Bm_extra_nonneg T hT i k
  unfold PQ MatrixAnalytic.Stability.qbdP at *
  simp only at *
  split_ifs at h ⊢ <;> first
    | (exfalso; omega) | exact h | (unfold Bm; linarith)

lemma tree_step (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (l l' : List ι) (i k : ι) (hne : (some (l, i) : TreeState ι) ≠ some (l', k))
    (hpos : 0 < gen T (some (l, i)) (some (l', k))) :
    0 < PQ T D ((l.length + 1 : ℕ), i) ((l'.length + 1 : ℕ), k) := by
  have hq := qv_pos T hT i
  have hj : 0 < jumpP (gen T) (some (l, i)) (some (l', k)) := by
    unfold jumpP; rw [hold_some, if_neg hq.ne', if_neg (Ne.symm hne)]
    exact div_pos hpos hq
  have h1 := ENNReal.le_tsum (f := fun y => if psi i y = psi i (some (l', k)) then
    ENNReal.ofReal (jumpP (gen T) (some (l, i)) y) else 0) (some (l', k))
  simp only [if_pos rfl] at h1
  have h2 := lumpJ T hT D hD i l i (l'.length + 1) k (by omega)
  rw [show psi i (some (l', k)) = ((l'.length + 1 : ℕ), k) from rfl, h2] at h1
  have h3 : 0 < ENNReal.ofReal (PQ T D (psi i (some (l, i))) ((l'.length + 1 : ℕ), k)) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hj) h1
  exact ENNReal.ofReal_pos.mp h3

def goalQ (T : TreeData ι) (D : ι → ι → ℝ) (x0 : ℕ × ι) : TreeState ι → Prop
  | none => ∃ i1, 0 < T.d i1 ∧ Relation.ReflTransGen (fun u v => 0 < PQ T D u v) x0 ((0 : ℕ), i1)
  | some (l, i) => Relation.ReflTransGen (fun u v => 0 < PQ T D u v) x0 (l.length, i)

lemma tree_to_q (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (l0 : List ι) (j0 : ι) (y : TreeState ι)
    (h : Relation.ReflTransGen (fun u v : TreeState ι => u ≠ v ∧ 0 < gen T u v) (some (l0, j0)) y) :
    goalQ T D (l0.length, j0) y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    obtain ⟨hne, hpos⟩ := hbc
    rcases b with _ | ⟨l, i⟩ <;> rcases c with _ | ⟨l', k⟩
    · exact absurd rfl hne
    · simp only [gen] at hpos
      split_ifs at hpos with hl
      · subst hl
        obtain ⟨i1, hd, hr⟩ := ih
        refine hr.tail ?_
        have hq := qv_pos T hT i1
        have hS := sumA_pos T hT i1
        have : PQ T D ((0 : ℕ), i1) ((0 : ℕ), k) = Bm T i1 k := by
          simp [PQ, MatrixAnalytic.Stability.qbdP]
        show 0 < PQ T D ((0 : ℕ), i1) (([] : List ι).length, k)
        rw [List.length_nil, this]
        unfold Bm
        exact add_pos_of_nonneg_of_pos (A1_nonneg T hT i1 k)
          (div_pos (mul_pos hd hpos) (mul_pos hq hS))
      · exact absurd hpos (lt_irrefl 0)
    · simp only [gen] at hpos
      split_ifs at hpos with hl
      · subst hl
        exact ⟨i, hpos, ih⟩
      · exact absurd hpos (lt_irrefl 0)
    · exact ih.tail (pos_shift T hT D _ _ _ _ (tree_step T hT D hD l l' i k hne hpos))

lemma PQ_summable (T : TreeData ι) (D : ι → ι → ℝ) (t : ℕ) (x y : ℕ × ι) :
    Summable (fun w => stepPow (PQ T D) t x w * PQ T D w y) := by
  refine summable_of_ne_finset_zero (s := Finset.range (y.1 + 2) ×ˢ Finset.univ) fun w hw => ?_
  have : PQ T D w y = 0 := by
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true, not_lt] at hw
    unfold PQ MatrixAnalytic.Stability.qbdP
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [this, mul_zero]

lemma PQ_irr (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D) :
    MatrixAnalytic.Stability.IrreducibleC (PQ T D) := by
  rintro ⟨n, i⟩ ⟨m, j⟩
  have h := tree_to_q T hT D hD (List.replicate n i) i (some (List.replicate m j, j))
    (hT.2 _ _)
  simp only [goalQ, List.length_replicate] at h
  exact stepPow_of_rtg _ (PQ_nonneg T hT D hD) (PQ_summable T D) _ _ h

lemma matA_irr (T : TreeData ι) (hT : IsTreeProcess T) (D : ι → ι → ℝ) (hD : ∀ i, T.D i = D)
    (hirr : IsIrreducibleGen (fun i j : ι => (∑ k : ι, T.A k i j) + T.C i j + D i j)) :
    MatrixAnalytic.Stability.IrreducibleC (MatrixAnalytic.Stability.matA (A0 T) (A1 T) (A2 T D)) := by
  have h0 : ∀ x y, 0 ≤ MatrixAnalytic.Stability.matA (A0 T) (A1 T) (A2 T D) x y := fun x y =>
    add_nonneg (add_nonneg (A0_nonneg T hT x y) (A1_nonneg T hT x y)) (A2_nonneg T hT D hD x y)
  intro x y
  refine stepPow_of_rtg _ h0 (fun _ _ _ => Summable.of_finite) x y ?_
  refine Relation.ReflTransGen.mono (fun u v huv => ?_) x y (hirr x y)
  obtain ⟨hne, hpos⟩ := huv
  unfold MatrixAnalytic.Stability.matA A0 A1 A2 As
  rw [if_neg hne, ← add_div, ← add_div]
  exact div_pos hpos (qv_pos T hT u)
end Irr

section Final
open MatrixAnalytic.Tree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma alpha_pos (M : ι → ι → ℝ) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 0)
    (hirr : ∀ x y, Relation.ReflTransGen (fun u v => u ≠ v ∧ 0 < M u v) x y)
    (α : ι → ℝ) (hα : ∀ j, ∑ i, α i * M i j = 0) (hα1 : ∑ i, α i = 1) : ∀ i, 0 < α i := by
  have hdiag : ∀ j, M j j ≤ 0 := by
    intro j
    have h := hrow j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h
    have : 0 ≤ ∑ k ∈ Finset.univ.erase j, M j k :=
      Finset.sum_nonneg fun k hk => hoff j k (Ne.symm (Finset.ne_of_mem_erase hk))
    linarith
  have hv : ∀ j, 0 ≤ ∑ i, |α i| * M i j := by
    intro j
    have h := hα j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h ⊢
    have h1 : |α j * M j j| ≤ ∑ i ∈ Finset.univ.erase j, |α i| * M i j := by
      have e : α j * M j j = - ∑ i ∈ Finset.univ.erase j, α i * M i j := by linarith
      rw [e, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
      rw [abs_mul, abs_of_nonneg (hoff i j (Finset.ne_of_mem_erase hi))]
    have h2 : |α j| * M j j = - |α j * M j j| := by
      rw [abs_mul, abs_of_nonpos (hdiag j)]; ring
    linarith
  have hv0 : ∀ j, ∑ i, |α i| * M i j = 0 := by
    have htot : ∑ j, ∑ i, |α i| * M i j = 0 := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).mp htot j (Finset.mem_univ j)
  set w : ι → ℝ := fun i => |α i| + α i with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => by simp only [hw]; linarith [neg_abs_le (α i)]
  have hwM : ∀ j, ∑ i, w i * M i j = 0 := by
    intro j; simp only [hw, add_mul, Finset.sum_add_distrib, hv0 j, hα j, add_zero]
  have hprop : ∀ k, w k = 0 → ∀ x, w x = 0 := by
    intro k hk x
    refine Relation.ReflTransGen.head_induction_on (hirr x k) hk ?_
    intro a c hac _ hc
    obtain ⟨hne, hpos⟩ := hac
    have h := hwM c
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), hc, zero_mul, zero_add] at h
    have hnn : ∀ i ∈ Finset.univ.erase c, 0 ≤ w i * M i c := fun i hi =>
      mul_nonneg (hw0 i) (hoff i c (Finset.ne_of_mem_erase hi))
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h a (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩)
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hpos.ne'
  intro i
  by_contra hcon
  push_neg at hcon
  have hk : w i = 0 := by simp only [hw]; rw [abs_of_nonpos hcon]; ring
  have hall := hprop i hk
  have : ∑ i, α i ≤ 0 := Finset.sum_nonpos fun x _ => by
    have := hall x; simp only [hw] at this; linarith [abs_nonneg (α x)]
  linarith

theorem main (T : TreeData ι) (hT : IsTreeProcess T)
    (D : ι → ι → ℝ) (hD : ∀ i : ι, T.D i = D)
    (hirr : IsIrreducibleGen (fun i j : ι => (∑ k : ι, T.A k i j) + T.C i j + D i j))
    (α : ι → ℝ)
    (hα : ∀ j : ι, ∑ i : ι, α i * ((∑ k : ι, T.A k i j) + T.C i j + D i j) = 0)
    (hα1 : ∑ i : ι, α i = 1) :
    IsPositiveRecurrentProcess (gen T) ↔
      ∑ i : ι, α i * ∑ j : ι, ∑ k : ι, T.A k i j < ∑ i : ι, α i * ∑ j : ι, D i j := by
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hα1
  have hq := qv_pos T hT
  have hpos := alpha_pos (fun i j : ι => (∑ k : ι, T.A k i j) + T.C i j + D i j)
    (fun i j hij => add_nonneg (add_nonneg (Finset.sum_nonneg fun k _ => A_nonneg T hT k i j)
      (C_nonneg T hT i j hij)) (by rw [← hD i]; exact D_nonneg T hT i i j))
    (fun i => by
      have := rowS T hT D hD i
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm]; linarith)
    hirr α hα hα1
  set S := ∑ i, α i * qv T i with hSdef
  have hS : 0 < S := Finset.sum_pos (fun i _ => mul_pos (hpos i) (hq i)) Finset.univ_nonempty
  set β : ι → ℝ := fun i => α i * qv T i / S with hβdef
  have hβ : MatrixAnalytic.Stability.IsStationaryC
      (MatrixAnalytic.Stability.matA (A0 T) (A1 T) (A2 T D)) β := by
    refine ⟨fun i => div_nonneg (mul_pos (hpos i) (hq i)).le hS.le, ?_, fun j => ?_⟩
    · convert hasSum_fintype β using 1
      rw [hβdef]; simp only; rw [← Finset.sum_div, div_self hS.ne']
    · convert hasSum_fintype (fun i => β i * MatrixAnalytic.Stability.matA (A0 T) (A1 T) (A2 T D) i j)
        using 1
      have e : ∀ i, β i * MatrixAnalytic.Stability.matA (A0 T) (A1 T) (A2 T D) i j =
          α i * ((∑ k : ι, T.A k i j) + T.C i j + D i j) / S + if i = j then β j else 0 := by
        intro i
        unfold MatrixAnalytic.Stability.matA A0 A2 As
        rw [A1_eq T hT]
        have := (hq i).ne'
        split_ifs with h
        · subst h; simp only [hβdef]; field_simp; ring
        · simp only [hβdef]; field_simp; ring
      simp_rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        ← Finset.sum_div, hα j, zero_div, zero_add]
  have hdrift : MatrixAnalytic.Stability.meanDrift (A0 T) (A2 T D) β =
      ((∑ i : ι, α i * ∑ j : ι, ∑ k : ι, T.A k i j) - ∑ i : ι, α i * ∑ j : ι, D i j) / S := by
    unfold MatrixAnalytic.Stability.meanDrift
    rw [sub_div, Finset.sum_div, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      unfold A0 As
      have := (hq i).ne'
      rw [← Finset.sum_div]; simp only [hβdef]; field_simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      unfold A2
      have := (hq i).ne'
      rw [← Finset.sum_div]; simp only [hβdef]; field_simp
  refine (positive_recurrent_iff_sp_lt_one T hT).trans ((spec_equiv T hT D hD).trans ?_)
  refine (MatrixAnalytic.Stability.positive_recurrent_iff_sp_lt_one (Bm T) (A0 T) (A1 T)
    (A2 T D) (PQ_stoch T hT D hD) (PQ_irr T hT D hD)).symm.trans ?_
  refine (MatrixAnalytic.Stability.drift_criterion (Bm T) (A0 T) (A1 T) (A2 T D)
    (PQ_stoch T hT D hD) (PQ_irr T hT D hD) (matA_irr T hT D hD hirr) β hβ).1.trans ?_
  rw [hdrift, div_lt_iff₀ hS, zero_mul, sub_neg]
end Final

end S203LD

open MatrixAnalytic.Tree

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (D : ι → ι → ℝ) (hD : ∀ i : ι, T.D i = D)
    (hirr : IsIrreducibleGen (fun i j : ι => (∑ k : ι, T.A k i j) + T.C i j + D i j))
    (α : ι → ℝ)
    (hα : ∀ j : ι, ∑ i : ι, α i * ((∑ k : ι, T.A k i j) + T.C i j + D i j) = 0)
    (hα1 : ∑ i : ι, α i = 1) :
    IsPositiveRecurrentProcess (gen T) ↔
      ∑ i : ι, α i * ∑ j : ι, ∑ k : ι, T.A k i j < ∑ i : ι, α i * ∑ j : ι, D i j :=
  S203LD.main T hT D hD hirr α hα hα1

