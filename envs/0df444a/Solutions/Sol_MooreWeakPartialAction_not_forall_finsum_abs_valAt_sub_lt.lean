-- Prove2me | solution 1 for MooreWeakPartialAction.not_forall_finsum_abs_valAt_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-01T23:00:32.954987+00:00
-- url     : https://prove2.me/submissions/ad24efd2-e83e-42e1-9264-d137635ff8e8

import Definitions.Def_MooreFoelner
import Mathlib

section
namespace MooreWeakPartialAction

open MooreFoelner

/-- The counterexample: `x · g = x + toAdd g` when `|toAdd g| ≤ 1` (i.e. `g ∈ {1, a, a⁻¹}`),
undefined otherwise. -/
def wAct (x : ℤ) (g : Multiplicative ℤ) : Option ℤ :=
  if |Multiplicative.toAdd g| ≤ 1 then some (x + Multiplicative.toAdd g) else none

theorem wAct_eq_some {x y : ℤ} {g : Multiplicative ℤ} :
    wAct x g = some y ↔ |Multiplicative.toAdd g| ≤ 1 ∧ x + Multiplicative.toAdd g = y := by
  unfold wAct; split_ifs with h <;> simp [h]

theorem wAct_one (x : ℤ) : wAct x 1 = some x := by
  simp [wAct]

theorem wAct_inv (g : Multiplicative ℤ) (x y : ℤ) :
    wAct x g = some y ↔ wAct y g⁻¹ = some x := by
  simp only [wAct_eq_some, toAdd_inv, abs_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem wAct_mul (g h : Multiplicative ℤ) (x y z w : ℤ) :
    wAct x g = some y → wAct y h = some z → wAct x (g * h) = some w → w = z := by
  simp only [wAct_eq_some, toAdd_mul]
  rintro ⟨-, h1⟩ ⟨-, h2⟩ ⟨-, h3⟩
  omega

/-- The generator `a = ofAdd 1`. -/
def gA : Multiplicative ℤ := Multiplicative.ofAdd 1

/-- `Γ = {a, a⁻¹}`. -/
def gam : Finset (Multiplicative ℤ) := {gA, gA⁻¹}

theorem gam_symm : ∀ γ ∈ gam, γ⁻¹ ∈ gam := by
  intro γ hγ
  simp only [gam, Finset.mem_insert, Finset.mem_singleton] at hγ ⊢
  rcases hγ with rfl | rfl <;> simp

theorem gam_closure : Subgroup.closure (gam : Set (Multiplicative ℤ)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  have hA : gA ∈ Subgroup.closure (gam : Set (Multiplicative ℤ)) :=
    Subgroup.subset_closure (by simp [gam])
  have : g = gA ^ (Multiplicative.toAdd g) := by
    rw [gA, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  rw [this]
  exact Subgroup.zpow_mem _ hA _

theorem gA_ne_inv : gA ≠ gA⁻¹ := by
  intro h
  have := congrArg Multiplicative.toAdd h
  simp [gA] at this

/-- `μ_N`, the indicator of `{1, …, N}`. -/
noncomputable def mu (N : ℕ) : ℤ →₀ ℝ := indicator (Finset.Icc (1 : ℤ) N)

theorem mu_apply' (N : ℕ) (t : ℤ) : mu N t = if t ∈ Finset.Icc (1 : ℤ) N then 1 else 0 := by
  simp [mu, indicator, Finsupp.onFinset_apply]

theorem mu_apply (N : ℕ) (t : ℤ) : mu N t = if 1 ≤ t ∧ t ≤ N then 1 else 0 := by
  simp only [mu_apply', Finset.mem_Icc]

theorem mu_nonneg (N : ℕ) (t : ℤ) : 0 ≤ mu N t := by
  rw [mu_apply]; split_ifs <;> norm_num

theorem finsum_ite_mem (T : Finset ℤ) : ∑ᶠ s, (if s ∈ T then (1:ℝ) else 0) = T.card := by
  rw [finsum_eq_sum_of_support_subset _ (s := T) ?_]
  · simp
  · intro s hs
    rw [Function.mem_support] at hs
    by_contra h
    exact hs (if_neg (by simpa using h))

theorem mass_univ_eq_finsum (μ : ℤ →₀ ℝ) : mass μ Set.univ = ∑ᶠ s, μ s := by
  rw [finsum_eq_sum_of_support_subset μ (s := μ.support) (by simp [Finsupp.fun_support_eq])]
  simp [mass]

theorem mass_mu (N : ℕ) : mass (mu N) Set.univ = N := by
  rw [mass_univ_eq_finsum]
  simp_rw [mu_apply']
  rw [finsum_ite_mem]
  simp

theorem valAt_wAct (μ : ℤ →₀ ℝ) (s : ℤ) (g : Multiplicative ℤ) :
    valAt wAct μ s g =
      if |Multiplicative.toAdd g| ≤ 1 then μ (s + Multiplicative.toAdd g) else 0 := by
  unfold valAt wAct; split_ifs <;> rfl

theorem sum_a (N : ℕ) (hN : 1 ≤ N) : ∑ᶠ s, |valAt wAct (mu N) s gA - mu N s| = 2 := by
  have key : ∀ s, |valAt wAct (mu N) s gA - mu N s| =
      if s ∈ ({0, (N:ℤ)} : Finset ℤ) then 1 else 0 := by
    intro s
    simp only [valAt_wAct, gA, toAdd_ofAdd, abs_one, le_refl, if_true, mu_apply,
      Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> first | omega | norm_num
  simp_rw [key]
  rw [finsum_ite_mem, Finset.card_pair (by omega)]
  norm_num

theorem sum_ainv (N : ℕ) (hN : 1 ≤ N) : ∑ᶠ s, |valAt wAct (mu N) s gA⁻¹ - mu N s| = 2 := by
  have key : ∀ s, |valAt wAct (mu N) s gA⁻¹ - mu N s| =
      if s ∈ ({1, (N:ℤ) + 1} : Finset ℤ) then 1 else 0 := by
    intro s
    simp only [valAt_wAct, gA, toAdd_inv, toAdd_ofAdd, abs_neg, abs_one, le_refl, if_true,
      mu_apply, Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> first | omega | norm_num
  simp_rw [key]
  rw [finsum_ite_mem, Finset.card_pair (by omega)]
  norm_num

theorem folner_sum (N : ℕ) (hN : 1 ≤ N) :
    ∑ γ ∈ gam, ∑ᶠ s, |valAt wAct (mu N) s γ - mu N s| = 4 := by
  rw [gam, Finset.sum_pair gA_ne_inv, sum_a N hN, sum_ainv N hN]
  norm_num

theorem mu_folner (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (h : 4 < ε * N) :
    IsWeightedFolner wAct gam (mu N) ε :=
  ⟨mu_nonneg N, by rw [folner_sum N hN, mass_mu]; exact h⟩

/-- `a² = ofAdd 2`, which acts nowhere. -/
def g2 : Multiplicative ℤ := Multiplicative.ofAdd 2

theorem g2_ne_one : g2 ≠ 1 := by
  intro h
  have := congrArg Multiplicative.toAdd h
  simp [g2] at this

theorem wordLength_g2 : wordLength gam g2 ≤ 2 := by
  apply Nat.sInf_le
  refine ⟨[gA, gA], rfl, ?_, ?_⟩
  · simp [gam]
  · simp only [List.prod_cons, List.prod_nil, mul_one, gA, g2, ← ofAdd_add]
    norm_num

theorem valAt_g2 (μ : ℤ →₀ ℝ) (s : ℤ) : valAt wAct μ s g2 = 0 := by
  rw [valAt_wAct, if_neg]
  simp [g2]

theorem finsum_g2 (μ : ℤ →₀ ℝ) (h : ∀ s, 0 ≤ μ s) :
    ∑ᶠ s, |valAt wAct μ s g2 - μ s| = mass μ Set.univ := by
  rw [mass_univ_eq_finsum]
  refine finsum_congr fun s => ?_
  rw [valAt_g2, zero_sub, abs_neg, abs_of_nonneg (h s)]

end MooreWeakPartialAction
end

open MooreWeakPartialAction in
open MooreFoelner in
theorem solution :
    ¬ ∀ (act : ℤ → Multiplicative ℤ → Option ℤ),
      (∀ x, act x 1 = some x) →
      (∀ (g : Multiplicative ℤ) (x y : ℤ), act x g = some y ↔ act y g⁻¹ = some x) →
      (∀ (g h : Multiplicative ℤ) (x y z w : ℤ),
        act x g = some y → act y h = some z → act x (g * h) = some w → w = z) →
      ∀ (Γ : Finset (Multiplicative ℤ)), (∀ γ ∈ Γ, γ⁻¹ ∈ Γ) →
      Subgroup.closure (Γ : Set (Multiplicative ℤ)) = ⊤ →
      ∀ (ε : ℝ), 0 < ε → ∀ (μ : ℤ →₀ ℝ), MooreFoelner.IsWeightedFolner act Γ μ ε →
      ∀ (g : Multiplicative ℤ), g ≠ 1 →
      ∑ᶠ s, |MooreFoelner.valAt act μ s g - μ s| < 2 * ε * MooreFoelner.wordLength Γ g * MooreFoelner.mass μ Set.univ := by
  intro h
  have := h wAct wAct_one wAct_inv wAct_mul gam gam_symm gam_closure (1 / 8) (by norm_num)
    (mu 40) (mu_folner 40 (by norm_num) (1 / 8) (by norm_num)) g2 g2_ne_one
  rw [finsum_g2 _ (mu_nonneg 40), mass_mu] at this
  have hd : (wordLength gam g2 : ℝ) ≤ 2 := by exact_mod_cast wordLength_g2
  push_cast at this
  linarith
