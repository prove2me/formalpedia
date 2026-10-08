-- Prove2me | solution 1 for NestedLogitVariants.Competitive.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:01:16.252863+00:00
-- url     : https://prove2.me/submissions/eb6c4464-e8ad-4d30-969b-3291a733daf7

import Definitions.Def_NestedLogitVariants_Competitive_Model
import Theorems.Thm_NestedLogitVariants_Competitive_g_le_gamma

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
    (S : ι → Finset (Fin n)) (i : ι) (j : Fin n) (hj : j ∈ S i)
    (hr : I.r i j < I.γ i * revenue I S + (1 - I.γ i) * R I i (S i))
    (hR : revenue I S ≤ R I i (S i)) :
    revenue I S < revenue I (Function.update S i ((S i).erase j)) := by
  have hSj : (S i).Nonempty := ⟨j, hj⟩
  have hB : ((S i).erase j).Nonempty := by
    by_contra h
    have he : (S i).erase j = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hs : S i = {j} := by
      apply Finset.Subset.antisymm
      · intro k hk
        have hkj : k = j := by
          by_contra hkj
          have hm := Finset.mem_erase.mpr ⟨hkj, hk⟩
          rw [he] at hm
          exact Finset.notMem_empty _ hm
        simp [hkj]
      · exact Finset.singleton_subset_iff.mpr hj
    have hrj : R I i (S i) = I.r i j := by
      simp [hs, R, V, hfc, (hI.v_pos i j).ne']
    rw [hrj] at hr hR
    nlinarith [mul_nonneg (hI.γ_pos i).le (sub_nonneg.mpr hR)]
  let a : ℝ := V I i ((S i).erase j) / V I i (S i)
  have hV : 0 < V I i (S i) := v_pos I hI i _ hSj
  have hW : 0 < V I i ((S i).erase j) := v_pos I hI i _ hB
  have hsum : V I i ((S i).erase j) + I.v i j = V I i (S i) := by
    simp only [V, hfc, zero_add]
    exact Finset.sum_erase_add _ _ hj
  have ha0 : 0 < a := div_pos hW hV
  have ha1 : a < 1 := (div_lt_one hV).2 (by linarith [hI.v_pos i j])
  have haV : a * V I i (S i) = V I i ((S i).erase j) := div_mul_cancel₀ _ hV.ne'
  have hrOld : R I i (S i) * V I i (S i) = ∑ k ∈ S i, I.r i k * I.v i k :=
    div_mul_cancel₀ _ hV.ne'
  have hrNew : R I i ((S i).erase j) * V I i ((S i).erase j) =
      ∑ k ∈ (S i).erase j, I.r i k * I.v i k := div_mul_cancel₀ _ hW.ne'
  have hnum := Finset.sum_erase_add (S i) (fun k => I.r i k * I.v i k) hj
  have hrel : a * R I i ((S i).erase j) = R I i (S i) - (1 - a) * I.r i j := by
    apply (mul_right_cancel₀ hV.ne')
    linear_combination (R I i ((S i).erase j) - I.r i j) * haV +
      hrNew + hnum - hrOld - I.r i j * hsum
  have hpow : nestWeight I i ((S i).erase j) = a ^ I.γ i * nestWeight I i (S i) := by
    dsimp [a, nestWeight]
    rw [Real.div_rpow hW.le hV.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hV _).ne']
  have hp : 0 < a ^ I.γ i := Real.rpow_pos_of_pos ha0 _
  have hpdiv : a ^ (I.γ i - 1) = a ^ I.γ i / a := Real.rpow_sub_one ha0.ne' _
  have hd : 0 < a ^ (I.γ i - 1) - a ^ I.γ i := by
    rw [hpdiv, sub_pos, lt_div_iff₀ ha0]
    nlinarith
  let g : ℝ := (1 - a ^ I.γ i) / (a ^ (I.γ i - 1) - a ^ I.γ i)
  have hg : g ≤ I.γ i := NestedLogitVariants.Competitive.g_le_gamma _ _ (hI.γ_pos i) (hγ i) ha0 ha1
  have hmix : I.γ i * revenue I S + (1 - I.γ i) * R I i (S i) ≤
      g * revenue I S + (1 - g) * R I i (S i) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hg) (sub_nonneg.mpr hR)]
  have hrg := hr.trans_le hmix
  have hgden : g * (a ^ (I.γ i - 1) - a ^ I.γ i) = 1 - a ^ I.γ i :=
    div_mul_cancel₀ _ hd.ne'
  have hpowrel : a * (a ^ (I.γ i - 1) - a ^ I.γ i) = a ^ I.γ i * (1 - a) := by
    rw [hpdiv]
    field_simp
    <;> ring
  have hscaled := mul_lt_mul_of_pos_right hrg hd
  have hmain : R I i (S i) - revenue I S <
      a ^ I.γ i * (R I i ((S i).erase j) - revenue I S) := by
    have heq : a ^ (I.γ i - 1) * a = a ^ I.γ i := by rw [hpdiv]; exact div_mul_cancel₀ _ ha0.ne'
    have hh := congrArg (fun x : ℝ => a ^ (I.γ i - 1) * x) hrel
    have hid : R I i (S i) - revenue I S -
        a ^ I.γ i * (R I i ((S i).erase j) - revenue I S) =
        (a ^ (I.γ i - 1) - a ^ I.γ i) *
          (I.r i j - (g * revenue I S + (1 - g) * R I i (S i))) := by
      linear_combination -hh + (R I i ((S i).erase j) - I.r i j) * heq +
        (revenue I S - R I i (S i)) * hgden
    nlinarith only [hscaled, hid]
  apply (revenue_update_lt I hI hv0 S i _).2
  rw [hpow]
  have hh := mul_lt_mul_of_pos_left hmain (w_pos I hI i _ hSj)
  nlinarith

#print axioms solution
