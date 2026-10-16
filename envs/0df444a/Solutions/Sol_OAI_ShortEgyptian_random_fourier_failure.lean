-- Prove2me | solution 1 for OAI.ShortEgyptian.random_fourier_failure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:03:45.170336+00:00
-- url     : https://prove2.me/submissions/1b040a04-81fe-42b7-bae5-8476ac475179

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean:L109-L144
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.random_fourier_failure. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_frequency_bad_probability
import Theorems.Thm_OAI_ShortEgyptian_random_product_second_moment

-- ---- from OAI.NumberTheory.ShortEgyptian.ResidueDiscrepancy ----
namespace OAI

universe uα

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem stdAddChar_nat_phase {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = phase ((n : ℝ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold phase
  congr 1
  push_cast
  ring

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ListSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uI uΩ uJ uA uE uD uU

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma fourierBad_probability {I : Type uI} {Ω : Type uΩ} [Fintype I] [Fintype Ω]
    (t : Ω → I → ℕ) (Q u : ℕ) (δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊,
      (𝔼 ω, ‖phaseAverage (t ω) Q u l‖^2) ≤ E) :
    (𝔼 ω, if FourierBad (t ω) Q u δ then (1:ℝ) else 0) ≤ E/δ^10 :=
by
  have hh := frequency_bad_probability (fun ω l => phaseAverage (t ω) Q u l) δ E hδ hE hmoment
  apply le_trans _ hh
  apply expect_le_expect
  intro ω _
  by_cases h : FourierBad (t ω) Q u δ
  · have h' : ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage (t ω) Q u l‖ := h
    simp only [ite_eq_left h,ite_eq_left h',le_refl]
  · have h' : ¬∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage (t ω) Q u l‖ := h
    simp only [ite_eq_right h,ite_eq_right h',le_refl]

lemma phaseAverage_sample {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A]
    (p : A → ℕ) (f : (J × Bool) → A) (u l : ℕ) [NeZero u] :
    phaseAverage (fun I => sampleProduct p I f) 1 u l =
      𝔼 I : J → Bool, ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u) := by
  rw [Fintype.expect_eq_sum_div_card]
  unfold phaseAverage
  congr 1
  apply sum_congr rfl
  intro I _
  rw [stdAddChar_nat_phase]
  push_cast
  simp

lemma random_fourier_failure {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S v : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊)
    (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u : ℕ) (hu : 0 < u) (hV : 100000*Real.log S ≤ Real.log u) (hVS : Real.log u ≤ S)
    (hv : 0 ≤ v) (hvw : (99/100:ℝ)*v ≤ min (⌊S/Real.log S⌋₊:ℝ) (Real.log u)) :
    (𝔼 f : (J × Bool) → A,
      if FourierBad (fun I => sampleProduct p I f) 1 u (Real.exp (-(1/10000:ℝ)*v)) then (1:ℝ) else 0) ≤
        Real.exp (-(1/200:ℝ)*v) := by
  let : NeZero u := ⟨hu.ne'⟩
  let δ := Real.exp (-(1/10000:ℝ)*v)
  let w := min (⌊S/Real.log S⌋₊:ℝ) (Real.log u)
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : 1/δ^4 = Real.exp ((1/2500:ℝ)*v) := by
    dsimp [δ]
    rw [←Real.exp_nat_mul,one_div,←Real.exp_neg]
    congr 1
    norm_num
    ring
  have hh := fourierBad_probability (fun f : (J × Bool) → A => fun I : J → Bool => sampleProduct p I f) 1 u δ
    (Real.exp (-(1/100:ℝ)*w)) hδ (Real.exp_nonneg _) (by
      intro l hl
      simp_rw [phaseAverage_sample]
      apply random_product_second_moment S hcard hlog hS p hp hinj hmax hP u l hu (mem_Icc.mp hl).1
        hV hVS
      have hlf : (l:ℝ) ≤ 1/δ^4 :=
        (Nat.cast_le.mpr (mem_Icc.mp hl).2).trans (Nat.floor_le (by positivity))
      rw [hinv] at hlf
      exact hlf.trans (Real.exp_le_exp.mpr (by nlinarith)))
  apply hh.trans
  dsimp [δ,w]
  rw [←Real.exp_nat_mul,←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  norm_num
  nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.random_fourier_failure.{uJ,uA} := @_root_.OAI.ShortEgyptian.random_fourier_failure.{uJ,uA}
