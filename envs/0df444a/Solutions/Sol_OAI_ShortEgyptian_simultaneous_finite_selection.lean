-- Prove2me | solution 1 for OAI.ShortEgyptian.simultaneous_finite_selection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:05:39.019001+00:00
-- url     : https://prove2.me/submissions/154506d1-e9cd-42dc-a584-f6b53b45384e

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean:L157-L201
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.simultaneous_finite_selection. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection

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

lemma expect_pi_split {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A]
    [AddCommMonoid E] [Module ℚ≥0 E] (P : J → Prop) (F : (J → A) → E) :
    (𝔼 f : J → A, F f) =
      𝔼 g : {j // P j} → A, 𝔼 h : {j // ¬P j} → A,
        F (fun j => if hj : P j then g ⟨j,hj⟩ else h ⟨j,hj⟩) := by
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => A)
  calc
    _ = 𝔼 gh : ({j // P j} → A) × ({j // ¬P j} → A), F (e.symm gh) := by
      exact Fintype.expect_equiv e _ _ (fun f => by simp)
    _ = _ := by
      rw [show (univ : Finset (({j // P j} → A) × ({j // ¬P j} → A))) = univ ×ˢ univ by simp]
      rw [expect_product]
      rfl

lemma expect_restrict_subtype {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A] [Nonempty A]
    [AddCommMonoid E] [Module ℚ≥0 E] (P : J → Prop) (F : ({j // P j} → A) → E) :
    (𝔼 f : J → A, F (fun j => f j)) = 𝔼 g : {j // P j} → A, F g := by
  rw [expect_pi_split P]
  apply expect_congr rfl
  intro g _
  have heq (h : {j // ¬P j} → A) :
      (fun j : {j // P j} => if hj : P j.val then g ⟨j.val,hj⟩ else h ⟨j.val,hj⟩) = g := by
    funext j
    simp [j.property]
  simp only [heq,Fintype.expect_const]

lemma expect_restrict_injective {J : Type uJ} {K : Type uK} {A : Type uA} {E : Type uE} [Fintype J] [Fintype K] [Fintype A] [Nonempty A]
    [AddCommMonoid E] [Module ℚ≥0 E] (i : J → K) (hi : Function.Injective i) (F : (J → A) → E) :
    (𝔼 f : K → A, F (fun j => f (i j))) = 𝔼 g : J → A, F g := by
  let e : J ≃ Set.range i := Equiv.ofInjective i hi
  have hh := expect_restrict_subtype (fun k => k ∈ Set.range i)
    (fun g : Set.range i → A => F (fun j => g (e j)))
  change (𝔼 f : K → A, F (fun j => f (i j))) = _ at hh
  rw [hh]
  have ht := Fintype.expect_equiv (Equiv.arrowCongr e.symm (Equiv.refl A))
    (fun g : Set.range i → A => F (fun j => g (e j))) F (fun g => rfl)
  convert ht using 1
  exact expect_congr (by ext; simp) (fun _ _ => rfl)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ListSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uΩ uJ uA uE uD uU

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma expect_eval_function {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A] [Nonempty A]
    [AddCommMonoid E] [Module ℚ≥0 E] (j : J) (f : A → E) :
    (𝔼 g : J → A, f (g j)) = 𝔼 a : A, f a := by
  have hh := expect_restrict_injective (fun _ : Unit => j)
    (fun _ _ _ => Subsingleton.elim _ _) (fun g => f (g ()))
  change (𝔼 g : J → A, f (g j)) = _ at hh
  rw [hh]
  let e : (Unit → A) ≃ A := Equiv.funUnique Unit A
  convert Fintype.expect_equiv e (fun g => f (g ())) f (fun _ => rfl) using 1
  exact expect_congr (by ext; simp) (fun _ _ => rfl)

lemma simultaneous_finite_selection {Ω : Type uΩ} {J : Type uJ} {D : Type uD} {U : Type uU}
    [Fintype Ω] [Nonempty Ω] [Fintype J] [Fintype D] [Fintype U]
    (j₀ : J) (B : D → Ω → ℝ) (c ε : D → ℝ) (P : U → Ω → Prop) (r : U → ℝ)
    (hB : ∀ d ω, 0 ≤ B d ω) (hc : ∀ d, 0 < c d)
    (hmean : ∀ d, (𝔼 ω, B d ω) ≤ c d*ε d)
    (hprob : ∀ u, (𝔼 ω, if P u ω then (1:ℝ) else 0) ≤ r u)
    (hsmall : (∑ d, ε d)+(∑ u, r u^Fintype.card J) < 1) :
    ∃ f : J → Ω, (∀ d, B d (f j₀) < c d) ∧ (∀ u, ∃ j, ¬P u (f j)) := by
  classical
  let cost (f : J → Ω) :=
    (∑ d, B d (f j₀)/c d)+(∑ u, ∏ j, if P u (f j) then (1:ℝ) else 0)
  have hcost : (𝔼 f, cost f) < 1 := by
    apply lt_of_le_of_lt (b := (∑ d, ε d)+(∑ u, r u^Fintype.card J)) _ hsmall
    dsimp [cost]
    rw [expect_add_distrib, expect_sum_comm, expect_sum_comm]
    apply add_le_add
    · apply sum_le_sum
      intro d _
      rw [←expect_div, expect_eval_function]
      exact (div_le_iff₀ (hc d)).mpr (by simpa [mul_comm] using hmean d)
    · apply sum_le_sum
      intro u _
      have heq := expect_prod_pi (fun _j : J => fun ω : Ω => if P u ω then (1:ℝ) else 0)
      rw [heq]
      calc
        _ ≤ ∏ _j : J, r u := prod_le_prod (fun _ _ => expect_nonneg (fun _ _ => by positivity)) (fun _ _ => hprob u)
        _ = _ := by simp
  obtain ⟨f,_,hf⟩ := exists_lt_of_expect_lt univ_nonempty hcost
  have hfirst (d : D) : B d (f j₀)/c d ≤ cost f := by
    exact (single_le_sum (fun e _ => div_nonneg (hB e _) (hc e).le) (mem_univ d)).trans
      (le_add_of_nonneg_right (sum_nonneg (fun _ _ => prod_nonneg (fun _ _ => by positivity))))
  refine ⟨f, ?_, ?_⟩
  · intro d
    exact (div_lt_iff₀ (hc d)).mp ((hfirst d).trans_lt hf) |>.trans_eq (one_mul _)
  · intro u
    by_contra hbad
    push Not at hbad
    have h1 : (1:ℝ) ≤ cost f := by
      have hp : (∏ j, if P u (f j) then (1:ℝ) else 0) = 1 := by simp [hbad]
      rw [←hp]
      have hn (v : U) : 0 ≤ ∏ j : J, if P v (f j) then (1:ℝ) else 0 :=
        prod_nonneg (fun _ _ => by positivity)
      exact (single_le_sum (fun v _ => hn v) (mem_univ u)).trans
        (le_add_of_nonneg_left (sum_nonneg (fun d _ => div_nonneg (hB d (f j₀)) (hc d).le)))
    linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uΩ,uJ,uD,uU} : type_of% @_root_.OAI.ShortEgyptian.simultaneous_finite_selection.{uΩ,uJ,uD,uU} := @_root_.OAI.ShortEgyptian.simultaneous_finite_selection.{uΩ,uJ,uD,uU}
