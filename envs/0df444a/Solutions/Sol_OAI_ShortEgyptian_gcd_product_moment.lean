-- Prove2me | solution 1 for OAI.ShortEgyptian.gcd_product_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:35:07.410878+00:00
-- url     : https://prove2.me/submissions/511e43de-29af-45c9-aac2-ba12f2d8abbf

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeProducts.lean:L146-L184
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.gcd_product_moment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeProducts ----
namespace OAI

universe uJ uA uB uE uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma expect_prod_pi {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] (f : J → A → ℝ) :
    (𝔼 x : J → A, ∏ j, f j (x j)) = ∏ j, 𝔼 a : A, f j a := by
  simp only [Fintype.expect_eq_sum_div_card,prod_div_distrib,prod_const,card_univ,
    Fintype.card_fun,Nat.cast_pow]
  congr 1
  simpa using (prod_univ_sum (fun _ : J => (univ : Finset A)) f).symm

lemma gcd_prod_le_hits {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (f : J → A) (u : ℕ) :
    Nat.gcd (∏ j, p (f j)) u ≤ ∏ j, if p (f j) ∣ u then p (f j) else 1 := by
  have hd : Nat.gcd (∏ j, p (f j)) u ∣ ∏ j, Nat.gcd (p (f j)) u := by
    have aux (T : Finset J) : Nat.gcd u (∏ j ∈ T, p (f j)) ∣ ∏ j ∈ T, Nat.gcd u (p (f j)) := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert a T ha ih =>
        rw [prod_insert ha,prod_insert ha]
        exact (gcd_mul_dvd_mul_gcd u (p (f a)) _).trans (Nat.mul_dvd_mul_left _ ih)
    simpa only [Nat.gcd_comm] using aux univ
  have heq : ∀ j, Nat.gcd (p (f j)) u = if p (f j) ∣ u then p (f j) else 1 := by
    intro j
    split_ifs with h
    · exact Nat.gcd_eq_left h
    · exact (hp (f j)).coprime_iff_not_dvd.mpr h
  simp_rw [heq] at hd
  exact Nat.le_of_dvd (prod_pos (fun j _ => by split_ifs; exact (hp _).pos; omega)) hd

lemma gcd_product_moment {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (u : ℕ)
    (H h a : ℝ) (hH : 0 ≤ H) (ha : 0 ≤ a) (hprob : 0 ≤ h)
    (hmax : ∀ x, (p x:ℝ) ≤ H)
    (hhit : (𝔼 x, if p x ∣ u then (1:ℝ) else 0) ≤ h) :
    (𝔼 f : J → A, (Nat.gcd (∏ j, p (f j)) u : ℝ)^a) ≤
      Real.exp ((Fintype.card J:ℝ)*h*H^a) := by
  let w (x : A) : ℝ := if p x ∣ u then (p x:ℝ)^a else 1
  have hw : ∀ x, 0 ≤ w x := by intro x; unfold w; split_ifs <;> positivity
  have hpoint (f : J → A) : (Nat.gcd (∏ j, p (f j)) u : ℝ)^a ≤ ∏ j, w (f j) := by
    have hg : (Nat.gcd (∏ j, p (f j)) u:ℝ) ≤ ∏ j, if p (f j) ∣ u then (p (f j):ℝ) else 1 := by
      exact_mod_cast gcd_prod_le_hits p hp f u
    apply (Real.rpow_le_rpow (by positivity) hg ha).trans_eq
    rw [← Real.finsetProd_rpow _ _ (fun _ _ => by split_ifs <;> positivity)]
    apply prod_congr rfl
    intro j _
    dsimp [w]
    split_ifs <;> simp
  have he : (𝔼 x, w x) ≤ 1+h*H^a := by
    calc
      _ ≤ 𝔼 x, (1+(if p x ∣ u then (1:ℝ) else 0)*H^a) := by
        apply expect_le_expect
        intro x _
        dsimp [w]
        split_ifs
        · have ht := Real.rpow_le_rpow (Nat.cast_nonneg (p x)) (hmax x) ha
          simpa only [one_mul] using ht.trans (by linarith : H^a ≤ 1+H^a)
        · simp
      _ = 1+(𝔼 x, if p x ∣ u then (1:ℝ) else 0)*H^a := by
        rw [expect_add_distrib,Fintype.expect_const,← expect_mul]
      _ ≤ _ := by gcongr
  calc
    _ ≤ 𝔼 f : J → A, ∏ j, w (f j) := expect_le_expect (fun f _ => hpoint f)
    _ = (𝔼 x, w x)^(Fintype.card J) := by rw [expect_prod_pi]; simp
    _ ≤ (1+h*H^a)^(Fintype.card J) := pow_le_pow_left₀ (expect_nonneg (fun x _ => hw x)) he _
    _ ≤ Real.exp (h*H^a)^(Fintype.card J) := by
      apply pow_le_pow_left₀ (by positivity) _
      linarith [Real.add_one_le_exp (h*H^a)]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.gcd_product_moment.{uJ,uA} := @_root_.OAI.ShortEgyptian.gcd_product_moment.{uJ,uA}
