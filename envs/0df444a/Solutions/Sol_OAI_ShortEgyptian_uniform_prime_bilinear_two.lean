-- Prove2me | solution 1 for OAI.ShortEgyptian.uniform_prime_bilinear_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:39:34.993297+00:00
-- url     : https://prove2.me/submissions/882bcb39-2fc7-4bd0-ab32-508148ee0eb2

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/SamplePartitions.lean:L97-L122
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.uniform_prime_bilinear_two. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Theorems.Thm_OAI_ShortEgyptian_finite_parseval

-- ---- from OAI.NumberTheory.ShortEgyptian.FiniteFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uG

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem bilinear_character_sq_bound {q : ℕ} [NeZero q]
    (α β : ZMod q → ℂ) :
    ‖∑ x : ZMod q, ∑ y : ZMod q, α x * β y * ZMod.stdAddChar (x * y)‖ ^ 2 ≤
      (q : ℝ) * (∑ x : ZMod q, ‖α x‖ ^ 2) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  let F (x : ZMod q) := ∑ y : ZMod q, β y * ZMod.stdAddChar (x * y)
  have heq : (∑ x : ZMod q, ∑ y : ZMod q, α x * β y * ZMod.stdAddChar (x * y)) =
      ∑ x : ZMod q, α x * F x := by simp [F, Finset.mul_sum, mul_assoc]
  rw [heq]
  have hn : ‖∑ x : ZMod q, α x * F x‖ ≤ ∑ x : ZMod q, ‖α x‖ * ‖F x‖ := by
    simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset (ZMod q)) (fun x => α x * F x)
  have hn0 : 0 ≤ ∑ x : ZMod q, ‖α x‖ * ‖F x‖ := Finset.sum_nonneg (by intros; positivity)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun x => ‖α x‖) (fun x => ‖F x‖)
  have hP : (∑ x : ZMod q, ‖F x‖ ^ 2) = q * ∑ y : ZMod q, ‖β y‖ ^ 2 := finite_parseval β
  rw [hP] at hc
  have hh : ‖∑ x : ZMod q, α x * F x‖ ^ 2 ≤
      (∑ x : ZMod q, ‖α x‖ * ‖F x‖) ^ 2 := sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn
  exact hh.trans (by simpa only [mul_left_comm, mul_assoc] using hc)

theorem bilinear_character_unit_sq_bound {q : ℕ} [NeZero q]
    (c : (ZMod q)ˣ) (α β : ZMod q → ℂ) :
    ‖∑ x : ZMod q, ∑ y : ZMod q, α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ^ 2 ≤
      (q : ℝ) * (∑ x : ZMod q, ‖α x‖ ^ 2) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  let α' (x : ZMod q) := α ((↑c⁻¹ : ZMod q) * x)
  have heq : (∑ x : ZMod q, ∑ y : ZMod q, α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)) =
      ∑ x : ZMod q, ∑ y : ZMod q, α' x * β y * ZMod.stdAddChar (x * y) := by
    apply Fintype.sum_equiv (Units.mulLeft c)
    intro x
    simp [α', Units.mulLeft_apply, ← mul_assoc]
  have hmass : (∑ x : ZMod q, ‖α' x‖ ^ 2) = ∑ x : ZMod q, ‖α x‖ ^ 2 := by
    apply Fintype.sum_equiv (Units.mulLeft c⁻¹)
    intro x
    rfl
  rw [heq]
  simpa only [hmass] using bilinear_character_sq_bound α' β

theorem real_probability_energy_bound {ι : Type uι} [Fintype ι]
    (α : ι → ℝ) (A : ℝ) (hpos : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1)
    (hatom : ∀ i, α i ≤ A) : (∑ i, ‖(α i : ℂ)‖ ^ 2) ≤ A := by
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _)]
  calc
    ∑ i, α i ^ 2 ≤ ∑ i, A * α i := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_le_mul_of_nonneg_right (hatom i) (hpos i)]
    _ = A := by rw [← Finset.mul_sum, hsum, mul_one]

theorem bilinear_probability_bound {q : ℕ} [NeZero q]
    (c : (ZMod q)ˣ) (α β : ZMod q → ℝ) (A B : ℝ)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x)
    (hsα : ∑ x, α x = 1) (hsβ : ∑ x, β x = 1)
    (haα : ∀ x, α x ≤ A) (haβ : ∀ x, β x ≤ B) :
    ‖∑ x : ZMod q, ∑ y : ZMod q,
      (α x : ℂ) * (β y : ℂ) * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ≤
      Real.sqrt ((q : ℝ) * A * B) := by
  have hA : 0 ≤ A := le_trans (hα 0) (haα 0)
  have hB : 0 ≤ B := le_trans (hβ 0) (haβ 0)
  have hα2 := real_probability_energy_bound α A hα hsα haα
  have hβ2 := real_probability_energy_bound β B hβ hsβ haβ
  have hh := bilinear_character_unit_sq_bound c (fun x => (α x : ℂ)) (fun y => (β y : ℂ))
  have hsα0 : 0 ≤ ∑ x : ZMod q, ‖(α x : ℂ)‖ ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hsβ0 : 0 ≤ ∑ y : ZMod q, ‖(β y : ℂ)‖ ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hh' : (q : ℝ) * (∑ x : ZMod q, ‖(α x : ℂ)‖ ^ 2) * ∑ y : ZMod q, ‖(β y : ℂ)‖ ^ 2 ≤
      q * A * B := by gcongr
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr (hh.trans hh')

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeProducts ----
namespace OAI

universe uJ uA uB uE uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem prime_product_fiber_card {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p) (n : ℕ) :
    Nat.card {f : J → A // ∏ j, p (f j) = n} ≤ (Fintype.card J)^(Fintype.card J) := by
  classical
  by_cases h : Nonempty {f : J → A // ∏ j, p (f j) = n}
  · let f₀ := Classical.choice h
    let T : Finset A := univ.image f₀.val
    have hmem (f : {f : J → A // ∏ j, p (f j) = n}) (j : J) : f.val j ∈ T := by
      have hd : p (f.val j) ∣ ∏ k, p (f₀.val k) := by
        exact (dvd_prod_of_mem (fun k => p (f.val k)) (mem_univ j)).trans (dvd_of_eq (f.property.trans f₀.property.symm))
      rcases (hp (f.val j)).prime.exists_mem_finset_dvd hd with ⟨k,_,hk⟩
      have heq : p (f.val j) = p (f₀.val k) := (Nat.prime_dvd_prime_iff_eq (hp (f.val j)) (hp (f₀.val k))).mp hk
      exact mem_image.mpr ⟨k,mem_univ _,hinj heq.symm⟩
    let F (f : {f : J → A // ∏ j, p (f j) = n}) : J → T := fun j => ⟨f.val j,hmem f j⟩
    have hF : Function.Injective F := by
      intro f g hfg
      apply Subtype.ext
      funext j
      exact congrArg Subtype.val (congrFun hfg j)
    calc
      _ ≤ Fintype.card (J → T) := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_le_of_injective F hF
      _ = T.card ^ Fintype.card J := by simp
      _ ≤ _ := Nat.pow_le_pow_left (by simpa [T] using card_image_le (s := (univ : Finset J)) (f := f₀.val)) _
  · have : IsEmpty {f : J → A // ∏ j, p (f j) = n} := not_nonempty_iff.mp h
    simp

lemma finiteMass_nonneg {A : Type uA} {B : Type uB} [Fintype A] (f : A → B) (b : B) :
    0 ≤ finiteMass f b := by unfold finiteMass; positivity

lemma finiteMass_sum {A : Type uA} {B : Type uB} [Fintype A] [Nonempty A] [Fintype B] (f : A → B) :
    ∑ b, finiteMass f b = 1 := by
  classical
  simp only [finiteMass,← sum_div]
  have hc : (∑ b : B, Nat.card {a : A // f a = b}) = Fintype.card A := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [← Nat.cast_sum,hc,div_self]
  exact_mod_cast Fintype.card_ne_zero

lemma finiteMass_expect {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] (f : A → B) (g : B → ℂ) :
    (𝔼 a, g (f a)) = ∑ b, (finiteMass f b : ℂ)*g b := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  have heq : ∑ a : A, g (f a) = ∑ b : B, (Nat.card {a : A // f a = b}:ℂ)*g b := by
    simpa only [Nat.card_eq_fintype_card,Fintype.sum_sigma, sum_const, card_univ, nsmul_eq_mul] using (Fintype.sum_equiv (Equiv.sigmaFiberEquiv f) (fun x => g x.1) (fun a => g (f a)) (by intro x; exact congrArg g x.2.property.symm)).symm
  rw [heq,sum_div]
  apply sum_congr rfl
  intro b _
  simp only [finiteMass,Complex.ofReal_div,Complex.ofReal_natCast]
  ring

lemma prime_product_atom {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p) (n : ℕ) :
    finiteMass (fun f : J → A => ∏ j, p (f j)) n ≤
      (Fintype.card J :ℝ)^(Fintype.card J) / (Fintype.card A:ℝ)^(Fintype.card J) := by
  unfold finiteMass
  rw [Fintype.card_fun,Nat.cast_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast prime_product_fiber_card (J := J) p hp hinj n

lemma prime_product_mod_atom {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hprod : ∀ f : J → A, ∏ j, p (f j) < q) (b : ZMod q) :
    finiteMass (fun f : J → A => ((∏ j, p (f j) : ℕ) : ZMod q)) b ≤
      (Fintype.card J :ℝ)^(Fintype.card J) / (Fintype.card A:ℝ)^(Fintype.card J) := by
  have heq : ∀ f : J → A, ((∏ j, p (f j) : ℕ) : ZMod q) = b ↔ ∏ j, p (f j) = b.val := by
    intro f
    rw [← (ZMod.val_injective q).eq_iff, ZMod.val_natCast_of_lt (hprod f)]
  have hh : finiteMass (fun f : J → A => ((∏ j, p (f j) : ℕ) : ZMod q)) b =
      finiteMass (fun f : J → A => ∏ j, p (f j)) b.val := by
    unfold finiteMass
    congr 2
    exact Nat.card_congr (Equiv.subtypeEquivRight heq)
  rw [hh]
  exact prime_product_atom p hp hinj b.val

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.SamplePartitions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uJ uA uE uM uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma uniform_prime_bilinear_two {J : Type uJ} {K : Type uK} {A : Type uA} [Fintype J] [Fintype K] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hprod : ∀ f : J → A, ∏ j, p (f j) < q)
    (hprodK : ∀ f : K → A, ∏ j, p (f j) < q) (hcard : Fintype.card K = Fintype.card J) (c : (ZMod q)ˣ) :
    ‖𝔼 f : J → A, 𝔼 g : K → A,
      ZMod.stdAddChar ((c:ZMod q)*((∏ j, p (f j) : ℕ):ZMod q)*((∏ j, p (g j) : ℕ):ZMod q))‖ ≤
      Real.sqrt ((q:ℝ)*((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)^2) := by
  let F (f : J → A) : ZMod q := (∏ j, p (f j) : ℕ)
  let G (f : K → A) : ZMod q := (∏ j, p (f j) : ℕ)
  let α := finiteMass F
  let β := finiteMass G
  have heq : (𝔼 f : J → A, 𝔼 g : K → A, ZMod.stdAddChar ((c:ZMod q)*F f*G g)) =
      ∑ x : ZMod q, ∑ y : ZMod q, (α x:ℂ)*(β y:ℂ)*ZMod.stdAddChar ((c:ZMod q)*x*y) := by
    rw [finiteMass_expect F (fun x => 𝔼 g, ZMod.stdAddChar ((c:ZMod q)*x*G g))]
    apply sum_congr rfl
    intro x _
    rw [finiteMass_expect G (fun y => ZMod.stdAddChar ((c:ZMod q)*x*y))]
    simp only [α,β,mul_sum,mul_assoc]
  change ‖𝔼 f : J → A, 𝔼 g : K → A, ZMod.stdAddChar ((c:ZMod q)*F f*G g)‖ ≤ _
  rw [heq]
  simpa only [pow_two,mul_assoc] using bilinear_probability_bound c α β
    ((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)
    ((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)
    (finiteMass_nonneg F) (finiteMass_nonneg G) (finiteMass_sum F) (finiteMass_sum G)
    (prime_product_mod_atom p hp hinj q hprod)
    (by simpa only [hcard] using prime_product_mod_atom (J := K) p hp hinj q hprodK)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{uJ,uA,uK} : type_of% @_root_.OAI.ShortEgyptian.uniform_prime_bilinear_two.{uJ,uA,uK} := @_root_.OAI.ShortEgyptian.uniform_prime_bilinear_two.{uJ,uA,uK}
