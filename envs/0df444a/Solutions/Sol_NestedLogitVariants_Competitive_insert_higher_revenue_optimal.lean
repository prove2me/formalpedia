-- Prove2me | solution 1 for NestedLogitVariants.Competitive.insert_higher_revenue_optimal
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:04:58.783768+00:00
-- url     : https://prove2.me/submissions/0f6af84f-6ec5-4443-ba3e-c209d912a7a2

import Definitions.Def_NestedLogitVariants_Competitive_Model
import Theorems.Thm_NestedLogitVariants_Competitive_proposition_2
import Theorems.Thm_NestedLogitVariants_Competitive_revenue_threshold_of_optimal
import Theorems.Thm_NestedLogitVariants_Competitive_gamma_le_h

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
    (i : ι) (j k : Fin n) (hj : j ∈ Sstar i) (hk : k ∉ Sstar i) (hkj : k < j) :
    IsOptimal I (Function.update Sstar i (insert k (Sstar i))) := by
  have hSj : (Sstar i).Nonempty := ⟨j, hj⟩
  have hR := NestedLogitVariants.Competitive.proposition_2 I hI hγ hfc hv0 Sstar hopt i hSj
  have hr := (NestedLogitVariants.Competitive.revenue_threshold_of_optimal
    I hI hγ hfc hv0 Sstar hopt i j hj).trans (hI.r_antitone i hkj.le)
  let A := insert k (Sstar i)
  let a : ℝ := V I i (Sstar i) / V I i A
  have hV : 0 < V I i (Sstar i) := v_pos I hI i _ hSj
  have hW : 0 < V I i A := v_pos I hI i _ (Finset.insert_nonempty _ _)
  have hsum : V I i (Sstar i) + I.v i k = V I i A := by
    simp [A, V, Finset.sum_insert hk]; ring
  have ha0 : 0 < a := div_pos hV hW
  have ha1 : a < 1 := (div_lt_one hW).2 (by linarith [hI.v_pos i k])
  have haV : a * V I i A = V I i (Sstar i) := div_mul_cancel₀ _ hW.ne'
  have hrOld : R I i (Sstar i) * V I i (Sstar i) = ∑ l ∈ Sstar i, I.r i l * I.v i l :=
    div_mul_cancel₀ _ hV.ne'
  have hrNew : R I i A * V I i A = ∑ l ∈ A, I.r i l * I.v i l := div_mul_cancel₀ _ hW.ne'
  have hnum : (∑ l ∈ A, I.r i l * I.v i l) =
      I.r i k * I.v i k + ∑ l ∈ Sstar i, I.r i l * I.v i l := Finset.sum_insert hk
  have hrel : R I i A = a * R I i (Sstar i) + (1 - a) * I.r i k := by
    apply (mul_right_cancel₀ hW.ne')
    linear_combination hrNew + hnum - hrOld -
      (R I i (Sstar i) - I.r i k) * haV + I.r i k * hsum
  have hpow : nestWeight I i (Sstar i) = a ^ I.γ i * nestWeight I i A := by
    dsimp [a, nestWeight]
    rw [Real.div_rpow hV.le hW.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hW _).ne']
  let h : ℝ := (1 - a ^ I.γ i) / (1 - a)
  have hh : I.γ i ≤ h := NestedLogitVariants.Competitive.gamma_le_h _ _ (hI.γ_pos i) (hγ i) ha0 ha1
  have hden : h * (1 - a) = 1 - a ^ I.γ i := div_mul_cancel₀ _ (by linarith)
  have hmix : h * revenue I Sstar + (1 - h) * R I i (Sstar i) ≤ I.r i k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hR)]
  have hscaled := mul_le_mul_of_nonneg_right hmix (show 0 ≤ 1 - a by linarith)
  have hid : R I i A - revenue I Sstar - a ^ I.γ i * (R I i (Sstar i) - revenue I Sstar) =
      (1 - a) * (I.r i k - (h * revenue I Sstar + (1 - h) * R I i (Sstar i))) := by
    linear_combination hrel + (revenue I Sstar - R I i (Sstar i)) * hden
  have hmain : a ^ I.γ i * (R I i (Sstar i) - revenue I Sstar) ≤ R I i A - revenue I Sstar := by
    nlinarith only [hid, hscaled]
  have himp : revenue I Sstar ≤ revenue I (Function.update Sstar i A) := by
    apply (revenue_update_le I hI hv0 Sstar i A).2
    rw [hpow]
    have hh := mul_le_mul_of_nonneg_left hmain (w_nonneg I hI i A)
    nlinarith only [hh]
  exact fun S' => (hopt S').trans himp

#print axioms solution
