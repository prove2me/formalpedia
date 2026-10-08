-- Prove2me | solution 1 for NestedLogitVariants.Competitive.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:01:13.195059+00:00
-- url     : https://prove2.me/submissions/c9cb01ed-1062-4d9e-8ab7-d95933857cd7

import Definitions.Def_NestedLogitVariants_Competitive_Model

open NestedLogitVariants.Competitive

private lemma v_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (A : Finset (Fin n)) : 0 ≤ V I i A := by
  exact add_nonneg (hI.vnp_nonneg i) (Finset.sum_nonneg fun j _ => (hI.v_pos i j).le)

private lemma v_pos {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (A : Finset (Fin n)) (hA : A.Nonempty) : 0 < V I i A := by
  exact add_pos_of_nonneg_of_pos (hI.vnp_nonneg i)
    (Finset.sum_pos (fun j _ => hI.v_pos i j) hA)

private lemma w_nonneg {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (A : Finset (Fin n)) : 0 ≤ nestWeight I i A :=
  Real.rpow_nonneg (v_nonneg I hI i A) _

private lemma w_pos {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (A : Finset (Fin n)) (hA : A.Nonempty) : 0 < nestWeight I i A :=
  Real.rpow_pos_of_pos (v_pos I hI i A hA) _

private lemma w_empty {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hfc : ∀ i, I.vnp i = 0) (i : ι) : nestWeight I i ∅ = 0 := by
  simp [nestWeight, V, hfc, Real.zero_rpow (hI.γ_pos i).ne']

private lemma d_pos {ι : Type*} [Fintype ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hv0 : 0 < I.v0) (S : ι → Finset (Fin n)) :
    0 < I.v0 + ∑ i, nestWeight I i (S i) :=
  add_pos_of_pos_of_nonneg hv0 (Finset.sum_nonneg fun i _ => w_nonneg I hI i (S i))

private lemma sum_update_delta {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    (f : ι → α → ℝ) (S : ι → α) (i : ι) (A : α) :
    (∑ l, f l (Function.update S i A l)) = (∑ l, f l (S l)) + f i A - f i (S i) := by
  classical
  have hu : (fun l => f l (Function.update S i A l)) =
      Function.update (fun l => f l (S l)) i (f i A) := by
    funext l
    by_cases h : l = i <;> simp [h]
  rw [hu, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs := Finset.sum_erase_add Finset.univ (fun l => f l (S l)) (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  linarith

private lemma revenue_update_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : Instance ι n) (hI : I.Standing) (hv0 : 0 < I.v0)
    (S : ι → Finset (Fin n)) (i : ι) (A : Finset (Fin n)) :
    revenue I S ≤ revenue I (Function.update S i A) ↔
    nestWeight I i (S i) * (R I i (S i) - revenue I S) ≤
      nestWeight I i A * (R I i A - revenue I S) := by
  have heq : revenue I S * (I.v0 + ∑ l, nestWeight I l (S l)) =
      ∑ l, nestWeight I l (S l) * R I l (S l) :=
    div_mul_cancel₀ _ (d_pos I hI hv0 S).ne'
  change _ ≤ (∑ l, nestWeight I l (Function.update S i A l) *
      R I l (Function.update S i A l)) / (I.v0 + ∑ l, nestWeight I l (Function.update S i A l)) ↔ _
  rw [le_div_iff₀ (d_pos I hI hv0 _)]
  rw [sum_update_delta (fun l B => nestWeight I l B * R I l B),
    sum_update_delta (fun l B => nestWeight I l B)]
  constructor <;> intro h <;> nlinarith

private lemma revenue_update_lt {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : Instance ι n) (hI : I.Standing) (hv0 : 0 < I.v0)
    (S : ι → Finset (Fin n)) (i : ι) (A : Finset (Fin n)) :
    revenue I S < revenue I (Function.update S i A) ↔
    nestWeight I i (S i) * (R I i (S i) - revenue I S) <
      nestWeight I i A * (R I i A - revenue I S) := by
  have heq : revenue I S * (I.v0 + ∑ l, nestWeight I l (S l)) =
      ∑ l, nestWeight I l (S l) * R I l (S l) :=
    div_mul_cancel₀ _ (d_pos I hI hv0 S).ne'
  change _ < (∑ l, nestWeight I l (Function.update S i A l) *
      R I l (Function.update S i A l)) / (I.v0 + ∑ l, nestWeight I l (Function.update S i A l)) ↔ _
  rw [lt_div_iff₀ (d_pos I hI hv0 _)]
  rw [sum_update_delta (fun l B => nestWeight I l B * R I l B),
    sum_update_delta (fun l B => nestWeight I l B)]
  constructor <;> intro h <;> nlinarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal I Sstar)
    (i : ι) (hne : (Sstar i).Nonempty) :
    revenue I Sstar ≤ R I i (Sstar i) := by
  by_contra h
  have hr : R I i (Sstar i) < revenue I Sstar := lt_of_not_ge h
  have hi := (revenue_update_lt I hI hv0 Sstar i ∅).2 (by
    rw [w_empty I hI hfc i, zero_mul]
    exact mul_neg_of_pos_of_neg (w_pos I hI i (Sstar i) hne) (sub_neg.mpr hr))
  exact (not_lt_of_ge (hopt _)) hi

#print axioms solution
