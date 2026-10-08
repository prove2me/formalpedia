-- Prove2me | solution 1 for NestedLogitVariants.Competitive.optimal_of_v0_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:01:10.175909+00:00
-- url     : https://prove2.me/submissions/b5a46579-0e7c-4c7b-a06e-c752c5897bd0

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
    (hfc : ∀ i, I.vnp i = 0) (hv0 : I.v0 = 0) (hn : 0 < n) (i : ι)
    (hi : ∀ l, I.r l ⟨0, hn⟩ ≤ I.r i ⟨0, hn⟩) :
    IsOptimal I (fun l => if l = i then nbr n 1 else ∅) := by
  classical
  let j0 : Fin n := ⟨0, hn⟩
  have hc : 0 ≤ I.r i j0 := hI.r_nonneg i j0
  have hR : ∀ l (A : Finset (Fin n)), R I l A ≤ I.r i j0 := by
    intro l A
    by_cases hA : A.Nonempty
    · rw [R, div_le_iff₀ (v_pos I hI l A hA), V, hfc, zero_add, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
        ((hI.r_antitone l (show j0 ≤ j by exact Nat.zero_le _)).trans (hi l)) (hI.v_pos l j).le
    · simp only [Finset.not_nonempty_iff_eq_empty] at hA
      simp [hA, R, hc]
  have hbound : ∀ S : ι → Finset (Fin n), revenue I S ≤ I.r i j0 := by
    intro S
    have hd : 0 ≤ ∑ l, nestWeight I l (S l) :=
      Finset.sum_nonneg fun l _ => w_nonneg I hI l (S l)
    by_cases hz : (∑ l, nestWeight I l (S l)) = 0
    · simpa [revenue, hv0, hz] using hc
    · rw [revenue, hv0, zero_add, div_le_iff₀ (lt_of_le_of_ne hd (Ne.symm hz)), Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hR l (S l)) (w_nonneg I hI l (S l))
  have hnbr : nbr n 1 = {j0} := by
    ext j
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; apply Fin.ext; change j.val = 0; omega
    · rintro rfl; simp [j0]
  let S : ι → Finset (Fin n) := fun l => if l = i then {j0} else ∅
  have hden : (∑ l, nestWeight I l (S l)) = nestWeight I i {j0} := by
    rw [Finset.sum_eq_single i]
    · simp [S]
    · intro l _ hli
      simp [S, hli, w_empty I hI hfc]
    · simp
  have hnum : (∑ l, nestWeight I l (S l) * R I l (S l)) =
      nestWeight I i {j0} * R I i {j0} := by
    rw [Finset.sum_eq_single i]
    · simp [S]
    · intro l _ hli
      simp [S, hli, w_empty I hI hfc]
    · simp
  have hsingle : R I i {j0} = I.r i j0 := by
    simp [R, V, hfc, (hI.v_pos i j0).ne']
  have hrev : revenue I S = I.r i j0 := by
    rw [revenue, hv0, zero_add, hnum, hden, hsingle]
    exact mul_div_cancel_left₀ _ (w_pos I hI i {j0} (Finset.singleton_nonempty _)).ne'
  intro S'
  rw [hnbr]
  change revenue I S' ≤ revenue I S
  rw [hrev]
  exact hbound S'

#print axioms solution
