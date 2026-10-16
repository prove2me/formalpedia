-- Prove2me | solution 1 for OAI.ShortEgyptian.choose_random_lists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:10:28.608222+00:00
-- url     : https://prove2.me/submissions/d0f01d93-d5ee-41dd-a5c7-d3277f903c7f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/LevelSelection.lean:L105-L157
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.choose_random_lists. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Theorems.Thm_OAI_ShortEgyptian_random_fourier_failure
import Theorems.Thm_OAI_ShortEgyptian_simultaneous_finite_selection
import Theorems.Thm_OAI_ShortEgyptian_terminal_tail_subset

-- ---- from OAI.NumberTheory.ShortEgyptian.LevelSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uΩ uJ uA uD

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma scaleInterval_mem {X δ : ℝ} (hX : 0 ≤ X) {u : ℕ} (hu : u ∈ scaleInterval X δ) :
    0 < u ∧ X*δ < (u:ℝ) ∧ (u:ℝ) ≤ X := by
  obtain ⟨hl,hh⟩ := mem_Icc.mp hu
  refine ⟨by omega,?_,?_⟩
  · exact Nat.lt_of_floor_lt (by omega)
  · exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hX)

lemma scaleInterval_card (X δ : ℝ) (hX : 0 ≤ X) :
    ((scaleInterval X δ).card:ℝ) ≤ X := by
  apply le_trans (b := (⌊X⌋₊:ℝ)) _ (Nat.floor_le hX)
  dsimp [scaleInterval]
  rw [Nat.card_Icc]
  exact_mod_cast (show ⌊X⌋₊+1-(⌊X*δ⌋₊+1) ≤ ⌊X⌋₊ by omega)

lemma expected_badLevel {I : Type uI} {Ω : Type uΩ} [Fintype I] [Fintype Ω]
    (t : Ω → I → ℕ) (Q : ℕ) (X δ E : ℝ) (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hprob : ∀ u ∈ scaleInterval X δ,
      (𝔼 ω, if FourierBad (t ω) Q u δ then (1:ℝ) else 0) ≤ E) :
    (𝔼 ω, ((badLevel (t ω) Q X δ).card:ℝ)) ≤ X*E := by
  have heq (ω : Ω) : ((badLevel (t ω) Q X δ).card:ℝ) =
      ∑ u ∈ scaleInterval X δ, if FourierBad (t ω) Q u δ then (1:ℝ) else 0 := by
    rw [sum_boole]
    rfl
  simp_rw [heq]
  rw [expect_sum_comm]
  calc
    _ ≤ ∑ _u ∈ scaleInterval X δ, E := sum_le_sum hprob
    _ = ((scaleInterval X δ).card:ℝ)*E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (scaleInterval_card X δ hX) hE

lemma middle_interval_log (S : ℝ) (m : ℕ) (X : ℝ)
    (hXlo : Real.exp m ≤ X) (hXhi : X ≤ Real.exp S)
    (u : ℕ) (hu : u ∈ scaleInterval X (Real.exp (-(1/10000:ℝ)*m))) :
    0 < u ∧ (99/100:ℝ)*m ≤ Real.log u ∧ Real.log u ≤ S := by
  have hmem := scaleInterval_mem (Real.exp_nonneg _ |>.trans hXlo) hu
  have huR : 0 < (u:ℝ) := by exact_mod_cast hmem.1
  refine ⟨hmem.1,?_,(Real.log_le_iff_le_exp huR).mpr (hmem.2.2.trans hXhi)⟩
  apply (Real.le_log_iff_exp_le huR).mpr
  calc
    _ ≤ Real.exp ((9999/10000:ℝ)*m) := Real.exp_le_exp.mpr (by have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _; nlinarith)
    _ = Real.exp m*Real.exp (-(1/10000:ℝ)*m) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ X*Real.exp (-(1/10000:ℝ)*m) := mul_le_mul_of_nonneg_right hXlo (Real.exp_nonneg _)
    _ ≤ _ := hmem.2.1.le

lemma random_middle_bad {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S X : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊)
    (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (hm : 100000*Real.log S ≤ (99/100:ℝ)*(⌊S/Real.log S⌋₊:ℝ))
    (hXlo : Real.exp (⌊S/Real.log S⌋₊:ℝ) ≤ X) (hXhi : X ≤ Real.exp S) :
    (𝔼 f : (J × Bool) → A,
      ((badLevel (fun I => sampleProduct p I f) 1 X
        (Real.exp (-(1/10000:ℝ)*(⌊S/Real.log S⌋₊:ℝ)))).card:ℝ)) ≤
      X*Real.exp (-(1/200:ℝ)*(⌊S/Real.log S⌋₊:ℝ)) := by
  apply expected_badLevel _ _ _ _ _ (Real.exp_nonneg _ |>.trans hXlo) (Real.exp_nonneg _)
  intro u hu
  have hU := middle_interval_log S _ X hXlo hXhi u hu
  apply random_fourier_failure S (⌊S/Real.log S⌋₊:ℝ) hcard hlog hS p hp hinj hmax hP u hU.1
    (hm.trans hU.2.1) hU.2.2 (by positivity)
  apply le_min _ hU.2.1
  have hm0 : (0:ℝ) ≤ ⌊S/Real.log S⌋₊ := Nat.cast_nonneg _
  nlinarith

theorem choose_random_lists {J : Type uJ} {A : Type uA} {D : Type uD} [Fintype J] [Fintype A] [Nonempty A] [Fintype D]
    (S : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊)
    (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (hm : 100000*Real.log S ≤ (99/100:ℝ)*(⌊S/Real.log S⌋₊:ℝ))
    (hmS : (⌊S/Real.log S⌋₊:ℝ) ≤ S)
    (X : D → ℝ) (hX : ∀ d, Real.exp (⌊S/Real.log S⌋₊:ℝ) ≤ X d ∧ X d ≤ Real.exp S)
    (U : Finset ℕ) (hU : ∀ u ∈ U, 3 ≤ u ∧ 100000*Real.log S ≤ Real.log u ∧ Real.log u ≤ (⌊S/Real.log S⌋₊:ℝ))
    (hsmall : (Fintype.card D:ℝ)*Real.exp (-(1/250:ℝ)*(⌊S/Real.log S⌋₊:ℝ)) < 1/2) :
    ∃ f : Fin 1000 → (J × Bool) → A,
      (∀ d, ((badLevel (fun I => sampleProduct p I (f 0)) 1 (X d)
        (Real.exp (-(1/10000:ℝ)*(⌊S/Real.log S⌋₊:ℝ)))).card:ℝ) ≤
          X d*Real.exp (-(1/1000:ℝ)*(⌊S/Real.log S⌋₊:ℝ))) ∧
      (∀ u ∈ U, ∃ i, ¬FourierBad (fun I => sampleProduct p I (f i)) 1 u
        (Real.exp (-(1/10000:ℝ)*Real.log u))) := by
  let m := ⌊S/Real.log S⌋₊
  let B (d : D) (ω : (J × Bool) → A) :=
    ((badLevel (fun I => sampleProduct p I ω) 1 (X d) (Real.exp (-(1/10000:ℝ)*m))).card:ℝ)
  let c (d : D) := X d*Real.exp (-(1/1000:ℝ)*m)
  let ε (_d : D) := Real.exp (-(1/250:ℝ)*m)
  let P (u : U) (ω : (J × Bool) → A) :=
    FourierBad (fun I => sampleProduct p I ω) 1 u (Real.exp (-(1/10000:ℝ)*Real.log u))
  let r (u : U) := Real.exp (-(1/200:ℝ)*Real.log u)
  have hmean (d : D) : (𝔼 ω, B d ω) ≤ c d*ε d := by
    have hh := random_middle_bad S (X d) hcard hlog hS p hp hinj hmax hP hm (hX d).1 (hX d).2
    convert hh using 1
    dsimp [c,ε,m]
    rw [mul_assoc,←Real.exp_add]
    congr 2
    ring
  have hprob (u : U) : (𝔼 ω, if P u ω then (1:ℝ) else 0) ≤ r u := by
    have hUu := hU u u.property
    have hu : 0 < u.val := by omega
    have hV : 0 ≤ Real.log u.val := Real.log_nonneg (by exact_mod_cast (show 1 ≤ u.val by omega))
    apply random_fourier_failure S (Real.log u.val) hcard hlog hS p hp hinj hmax hP u hu hUu.2.1
      (hUu.2.2.trans hmS) hV
    rw [min_eq_right hUu.2.2]
    nlinarith
  have hsmall' : (∑ d, ε d)+(∑ u : U, r u^Fintype.card (Fin 1000)) < 1 := by
    have ht := terminal_tail_subset U (fun u hu => (hU u hu).1)
    rw [Fintype.card_fin]
    change (∑ _d : D, Real.exp (-(1/250:ℝ)*m)) +
      (∑ u : U, Real.exp (-(1/200:ℝ)*Real.log u.val)^1000) < 1
    rw [sum_coe_sort U (fun u : ℕ => Real.exp (-(1/200:ℝ)*Real.log u)^1000), sum_const,card_univ,nsmul_eq_mul]
    dsimp [m] at *
    linarith
  obtain ⟨f,hf,hu⟩ := simultaneous_finite_selection (0 : Fin 1000) B c ε P r
    (fun _ _ => Nat.cast_nonneg _) (fun d => mul_pos ((Real.exp_pos _).trans_le (hX d).1) (Real.exp_pos _))
    hmean hprob hsmall'
  refine ⟨f,fun d => (hf d).le,?_⟩
  intro u huU
  exact hu ⟨u,huU⟩

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uJ,uA,uD} : type_of% @_root_.OAI.ShortEgyptian.choose_random_lists.{uJ,uA,uD} := @_root_.OAI.ShortEgyptian.choose_random_lists.{uJ,uA,uD}
