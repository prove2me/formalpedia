-- Prove2me | solution 1 for OAI.TuringRigidity.main_of_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:22:09.510322+00:00
-- url     : https://prove2.me/submissions/9ffcf1be-8a8f-42a5-bca1-20493fd6842e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section
-- module Solutions.OAIQ064_DR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_Degrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem order_rigidity_of_inverse_le {α : Type*} [PartialOrder α]
    (h : ∀ π : α ≃o α, ∀ a, π.symm a ≤ a) :
    ∀ π : α ≃o α, ∀ a, π a = a := by
  intro π a
  apply le_antisymm
  · simpa using h π.symm a
  · simpa using π.monotone (h π a)

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleCode
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix _root_.OAI.TuringRigidity.instOrderBotDegree _root_.OAI.TuringRigidity.instSemilatticeSupDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem countable_degree_fiber (a : Degree) : {A : Oracle | degree A = a}.Countable := by
  obtain ⟨B, rfl⟩ := degree_surjective a
  apply (countable_reduces B).mono
  intro A hA
  exact ((degree_eq_iff A B).mp hA).1

theorem countable_lift_fiber {X : Type*} (C : X → Oracle) (hC : Function.Injective C)
    (π : Degree → Degree) (hπ : Function.Injective π)
    (F : X → Oracle) (hF : ∀ x, degree (F x) = π (degree (C x))) (B : Oracle) :
    {x : X | F x = B}.Countable := by
  by_cases hne : ∃ x, F x = B
  · obtain ⟨x₀, hx₀⟩ := hne
    apply ((countable_degree_fiber (degree (C x₀))).preimage hC).mono
    intro x hx
    apply hπ
    rw [← hF x, ← hF x₀, hx, hx₀]
  · have hempty : {x : X | F x = B} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hne ⟨x,h⟩
    rw [hempty]
    exact Set.countable_empty

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_Recurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem state_eq_sum (test : ℝ → Bool) (δ t : ℝ) (n : ℕ) :
    state test δ t n = δ * ((n : ℝ) * t - ∑ k ∈ Finset.range n, branch test δ t k) := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    simp only [state, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    change state test δ t n + δ * (t - branch test δ t n) = _
    rw [ih]
    ring

theorem frequency_error (test : ℝ → Bool) (δ t : ℝ) (n : ℕ)
    (hδ : 0 < δ) (hn : 0 < n) (hs : |state test δ t n| < 1) :
    |t - (∑ k ∈ Finset.range n, branch test δ t k) / (n : ℝ)| <
      1 / ((n : ℝ) * δ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) * δ := mul_pos hn' hδ
  have heq : t - (∑ k ∈ Finset.range n, branch test δ t k) / (n : ℝ) =
      state test δ t n / ((n : ℝ) * δ) := by
    rw [state_eq_sum]
    field_simp
  rw [heq, abs_div, abs_of_pos hden]
  exact (div_lt_div_iff_of_pos_right hden).mpr hs

theorem rationalSpan_countable (t : ℝ) : (rationalSpan t).Countable := by
  have hr : rationalSpan t = Set.range (fun p : ℚ × ℚ => (p.1 : ℝ) + p.2 * t) := by
    ext s
    simp only [rationalSpan, Set.mem_ofPred_eq, Set.mem_range, Prod.exists]
    exact ⟨fun ⟨a,b,h⟩ => ⟨a,b,h.symm⟩, fun ⟨a,b,h⟩ => ⟨a,b,h.symm⟩⟩
  rw [hr]
  exact Set.countable_range _

theorem state_mem_rationalSpan (test : ℝ → Bool) (δ : ℚ) (t : ℝ) :
    ∀ n, state test (δ : ℝ) t n ∈ rationalSpan t := by
  intro n
  induction n with
  | zero => exact ⟨0,0, by simp [state]⟩
  | succ n ih =>
    rcases ih with ⟨a,b,hab⟩
    cases hb : test (state test (δ : ℝ) t n) with
    | false =>
      refine ⟨a,b+δ, ?_⟩
      simp only [state, choiceBit, hb, Bool.false_eq_true, ↓reduceIte, sub_zero]
      rw [hab]
      push_cast
      ring
    | true =>
      refine ⟨a-δ,b+δ, ?_⟩
      simp only [state, choiceBit, hb, ↓reduceIte]
      rw [hab]
      push_cast
      ring

theorem state_mem_Icc_on_span (test : ℝ → Bool) (δ : ℚ) (t lo hi : ℝ)
    (hδ : (0 : ℝ) < δ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (left : ∀ s ∈ rationalSpan t, s ∈ Set.Icc lo (lo + δ) → test s = false)
    (right : ∀ s ∈ rationalSpan t, s ∈ Set.Icc (hi - δ) hi → test s = true) :
    ∀ n, state test (δ : ℝ) t n ∈ Set.Icc lo hi := by
  intro n
  induction n with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
    rcases ih with ⟨hslo, hshi⟩
    have hdt₀ : 0 < (δ : ℝ) * t := mul_pos hδ ht₀
    have hdt₁ : (δ : ℝ) * t < δ := by nlinarith
    have hneg : (δ : ℝ) * (t - 1) < 0 :=
      mul_neg_of_pos_of_neg hδ (by linarith)
    cases hb : test (state test (δ : ℝ) t n) with
    | false =>
      have hs : state test (δ : ℝ) t n < hi - δ := by
        by_contra h
        have := right _ (state_mem_rationalSpan test δ t n) ⟨le_of_not_gt h, hshi⟩
        simp [hb] at this
      simp only [state, choiceBit, hb, Bool.false_eq_true, ↓reduceIte, sub_zero]
      constructor <;> linarith
    | true =>
      have hs : lo + δ < state test (δ : ℝ) t n := by
        by_contra h
        have := left _ (state_mem_rationalSpan test δ t n) ⟨hslo, le_of_not_gt h⟩
        simp [hb] at this
      simp only [state, choiceBit, hb, ↓reduceIte]
      constructor <;> nlinarith

theorem exists_radius_lt (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ 1 / ((n : ℝ) * δ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (δ * ε))
  have hpos : 0 < 1 / (δ * ε) := one_div_pos.mpr (mul_pos hδ hε)
  have hn' : (0 : ℝ) < n := lt_trans hpos hn
  refine ⟨n, by exact_mod_cast hn', ?_⟩
  have hh : 1 < (n : ℝ) * (δ * ε) := (div_lt_iff₀ (mul_pos hδ hε)).mp hn
  apply (div_lt_iff₀ (mul_pos hn' hδ)).mpr
  nlinarith

theorem comparison_search (t δ : ℝ) (a : ℕ → ℝ) (hδ : 0 < δ)
    (herr : ∀ n : ℕ, 0 < n → |t - a n| < 1 / ((n : ℝ) * δ))
    (q : ℝ) (hqt : q ≠ t) :
    (∃ n : ℕ, 0 < n ∧
      (q < a n - 1 / ((n : ℝ) * δ) ∨ a n + 1 / ((n : ℝ) * δ) < q)) ∧
    (∀ n : ℕ, 0 < n →
      (q < a n - 1 / ((n : ℝ) * δ) → q < t) ∧
      (a n + 1 / ((n : ℝ) * δ) < q → t < q)) := by
  constructor
  · rcases lt_or_gt_of_ne hqt with hlt | hgt
    · obtain ⟨n, hn, hrad⟩ := exists_radius_lt δ ((t-q)/2) hδ (by linarith)
      refine ⟨n, hn, Or.inl ?_⟩
      have he := (abs_lt.mp (herr n hn)).2
      linarith
    · obtain ⟨n, hn, hrad⟩ := exists_radius_lt δ ((q-t)/2) hδ (by linarith)
      refine ⟨n, hn, Or.inr ?_⟩
      have he := (abs_lt.mp (herr n hn)).1
      linarith
  · intro n hn
    rcases abs_lt.mp (herr n hn) with ⟨hl,hu⟩
    constructor <;> intro h <;> linarith

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_Category
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology

namespace TuringRigidity

theorem measurable_continuousOn_residual {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (f : X → Y) (hf : Measurable f) :
    ∃ D : Set X, D ∈ residual X ∧ ContinuousOn f D := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis Y
  have hm : ∀ n : ℕ, MeasurableSet (f ⁻¹' b n) :=
    fun n => hf ((hb.isOpen (mem_range_self n)).measurableSet)
  choose V hVo hVeq using fun n => (hm n).residualEq_isOpen
  let D : Set X := {x | ∀ n : ℕ, f x ∈ b n ↔ x ∈ V n}
  have hD : D ∈ residual X := by
    apply eventually_countable_forall.mpr
    intro n
    exact Filter.eventuallyEq_set.mp (hVeq n)
  refine ⟨D, hD, hb.continuousOn_iff.mpr ?_⟩
  rintro s ⟨n, rfl⟩
  refine ⟨V n, hVo n, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hd⟩
    exact ⟨(hd n).mp hx, hd⟩
  · rintro ⟨hx, hd⟩
    exact ⟨(hd n).mpr hx, hd⟩

theorem goodPairs_residual (t : ℝ) (D : Set ℝ) (E : Set (ℝ × ℝ))
    (hD : D ∈ residual ℝ) (hE : E ∈ residual (ℝ × ℝ)) :
    goodPairs t D E ∈ residual (ℝ × ℝ) := by
  have : Countable (rationalSpan t) := (rationalSpan_countable t).to_subtype
  have hcoord (s : ℝ) : {p : ℝ × ℝ | p.1 + s ∈ D} ∈ residual (ℝ × ℝ) := by
    exact tendsto_residual_of_isOpenMap
      (continuous_fst.add continuous_const)
      ((Homeomorph.addRight s).isOpenMap.comp isOpenMap_fst) hD
  have hforward (s a : ℝ) :
      {p : ℝ × ℝ | (p.1+s,p.2-p.1+a) ∈ E} ∈ residual (ℝ × ℝ) := by
    exact tendsto_residual_of_isOpenMap
      (forwardShift s a).continuous (forwardShift s a).isOpenMap hE
  have hbackward (s : ℝ) :
      {p : ℝ × ℝ | (p.2+s,p.1-p.2) ∈ E} ∈ residual (ℝ × ℝ) := by
    exact tendsto_residual_of_isOpenMap
      (backwardShift s).continuous (backwardShift s).isOpenMap hE
  have h : ∀ᶠ p in residual (ℝ × ℝ), ∀ s : rationalSpan t,
      p.1+s.val ∈ D ∧
      (∀ a : rationalSpan t, (p.1+s.val,p.2-p.1+a.val) ∈ E) ∧
      (p.2+s.val,p.1-p.2) ∈ E := by
    apply eventually_countable_forall.mpr
    intro s
    exact Filter.Eventually.and (hcoord s.val)
      (Filter.Eventually.and (eventually_countable_forall.mpr
        (fun a => hforward s.val a.val)) (hbackward s.val))
  filter_upwards [h] with p hp
  intro s hs
  exact ⟨(hp ⟨s,hs⟩).1, fun a ha => (hp ⟨s,hs⟩).2.1 ⟨a,ha⟩, (hp ⟨s,hs⟩).2.2⟩

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_Cuts
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix _root_.OAI.TuringRigidity.instOrderBotDegree _root_.OAI.TuringRigidity.instSemilatticeSupDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem rationalEnumeration_surjective : Function.Surjective rationalEnumeration := by
  intro q
  refine ⟨Encodable.encode q, ?_⟩
  simp [rationalEnumeration]

theorem cut_injective : Function.Injective cut := by
  intro x y hxy
  apply le_antisymm
  · by_contra h
    have hyx : y < x := lt_of_not_ge h
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hyx
    obtain ⟨n, hn⟩ := rationalEnumeration_surjective q
    have hc : cut x n = true := (cut_eq_true x n).mpr (by simpa [hn] using hqx)
    rw [hxy] at hc
    have hqy := (cut_eq_true y n).mp hc
    rw [hn] at hqy
    exact (not_lt_of_gt hyq) hqy
  · by_contra h
    have hxy' : x < y := lt_of_not_ge h
    obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy'
    obtain ⟨n, hn⟩ := rationalEnumeration_surjective q
    have hc : cut y n = true := (cut_eq_true y n).mpr (by simpa [hn] using hqy)
    rw [← hxy] at hc
    have hqx := (cut_eq_true x n).mp hc
    rw [hn] at hqx
    exact (not_lt_of_gt hxq) hqx

theorem cut_measurable : Measurable cut := by
  apply Measurable.of_eval
  intro n
  have h : MeasurableSet {x : ℝ | (rationalEnumeration n : ℝ) < x} := measurableSet_Ioi
  have hm : Measurable (fun x : ℝ => if (rationalEnumeration n : ℝ) < x then true else false) :=
    Measurable.ite h measurable_const measurable_const
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases hq : (rationalEnumeration n : ℝ) < x <;> simp [cut, hq]

theorem represented_real_map_countable_fibers (π : Degree ≃o Degree) (F : ℝ → Oracle)
    (hF : ∀ x, degree (F x) = π (realDegree x)) :
    ∀ B : Oracle, {x : ℝ | F x = B}.Countable := by
  exact countable_lift_fiber cut cut_injective π π.injective F hF

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BinarySeries
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BinarySeries

theorem numeral_sum (B : Oracle) (n : ℕ) :
    (∑ i ∈ Finset.range n, Real.ofDigitsTerm (digits B) i) =
      (numeral B n : ℝ) / 2^n := by
  induction n with
  | zero => simp [numeral]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [numeral, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Real.ofDigitsTerm, digits, pow_succ]
    field_simp

theorem split_value (B : Oracle) (n : ℕ) :
    value B = (numeral B n : ℝ)/2^n + (2^n : ℝ)⁻¹ * value (fun i => B (i+n)) := by
  exact (Real.ofDigits_eq_sum_add_ofDigits (digits B) n).trans (by rw [numeral_sum]; rfl)

theorem nonneg (B : Oracle) : 0 ≤ value B := Real.ofDigits_nonneg _
theorem le_one (B : Oracle) : value B ≤ 1 := Real.ofDigits_le_one _

theorem positive (B : Oracle) (h : ∃ n, B n = true) : 0 < value B := by
  obtain ⟨n, hn⟩ := h
  have ht : 0 < Real.ofDigitsTerm (digits B) n := by
    simp [Real.ofDigitsTerm, digits, bit, hn]
  exact lt_of_lt_of_le ht (Summable.le_tsum Real.summable_ofDigitsTerm n
    (fun _ _ => Real.ofDigitsTerm_nonneg))

theorem complement (B : Oracle) : value B + value (fun n => !(B n)) = 1 := by
  rw [value, value, Real.ofDigits, Real.ofDigits, ← Summable.tsum_add
    Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm]
  have he : (fun n => Real.ofDigitsTerm (digits B) n +
      Real.ofDigitsTerm (digits (fun n => !(B n))) n) =
      Real.ofDigitsTerm (fun _ => (⟨1, by omega⟩ : Fin 2)) := by
    funext n
    cases h : B n <;> simp [Real.ofDigitsTerm, digits, bit, h]
  rw [he]
  exact Real.ofDigits_const_last_eq_one' (by omega : 1 < 2)

theorem lt_one (B : Oracle) (h : ∃ n, B n = false) : value B < 1 := by
  have hp := positive (fun n => !(B n)) (by obtain ⟨n, hn⟩ := h; exact ⟨n, by simp [hn]⟩)
  have hc := complement B
  linarith

theorem strict_bracket (B : Oracle) (h : Mixed B) (n : ℕ) :
    (numeral B n : ℝ)/2^n < value B ∧ value B < (numeral B n + 1 : ℝ)/2^n := by
  have hp : 0 < value (fun i => B (i+n)) := by
    apply positive
    obtain ⟨k,hk,hb⟩ := (h n).1
    exact ⟨k-n, by simpa [Nat.sub_add_cancel hk] using hb⟩
  have hu : value (fun i => B (i+n)) < 1 := by
    apply lt_one
    obtain ⟨k,hk,hb⟩ := (h n).2
    exact ⟨k-n, by simpa [Nat.sub_add_cancel hk] using hb⟩
  rw [split_value B n]
  have hd : (0 : ℝ) < (2^n : ℝ)⁻¹ := by positivity
  constructor
  · nlinarith
  · rw [add_div]
    simp only [one_div]
    nlinarith

theorem bracket (B : Oracle) (n : ℕ) :
    (numeral B n : ℝ)/2^n ≤ value B ∧ value B ≤ (numeral B n + 1 : ℝ)/2^n := by
  rw [split_value B n]
  have hp := nonneg (fun i => B (i+n))
  have hu := le_one (fun i => B (i+n))
  have hd : (0 : ℝ) < (2^n : ℝ)⁻¹ := by positivity
  constructor
  · nlinarith
  · rw [add_div]; simp only [one_div]; nlinarith

end TuringRigidity.BinarySeries

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RationalCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Encodable

namespace RationalCoding

theorem magnitude_primrec : Primrec magnitude :=
  Primrec.nat_add.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
    (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))

theorem encode_int_nonneg (n : ℕ) : encode (Int.ofNat n) = 2*n := by
  change Nat.bit false n = 2*n
  simp [Nat.bit]

theorem encode_int_neg (n : ℕ) : encode (Int.negSucc n) = 2*n+1 := by
  change Nat.bit true n = 2*n+1
  simp [Nat.bit]

theorem magnitude_encode_int (z : ℤ) : magnitude (encode z) = z.natAbs := by
  cases z with
  | ofNat n =>
    change magnitude (encode (Int.ofNat n)) = n
    rw [encode_int_nonneg]
    simp [magnitude]
  | negSucc n => simp [encode_int_neg,magnitude]; omega

theorem encode_rat (q : ℚ) : encode q = Nat.pair (encode q.num) q.den := rfl

theorem valid_iff (n : ℕ) : valid n ↔ ∃ q : ℚ, encode q = n := by
  constructor
  · rintro ⟨hd,hcop⟩
    let z := Equiv.intEquivNat.symm (Nat.unpair n).1
    have hz : encode z = (Nat.unpair n).1 := Equiv.intEquivNat.apply_symm_apply _
    have hm : z.natAbs = magnitude (Nat.unpair n).1 := by rw [←hz,magnitude_encode_int]
    let q : ℚ := ⟨z,(Nat.unpair n).2,Nat.ne_of_gt hd,hm.symm ▸ hcop⟩
    refine ⟨q,?_⟩
    rw [encode_rat]
    change Nat.pair (encode z) (Nat.unpair n).2 = n
    rw [hz,Nat.pair_unpair]
  · rintro ⟨q,rfl⟩
    simp only [valid,encode_rat,Nat.unpair_pair,magnitude_encode_int]
    exact ⟨q.den_pos,q.reduced⟩

theorem coprime_bounded (a b : ℕ) :
    (0 < b ∧ a.Coprime b) ↔
      (0 < b ∧ ∀ k ∈ List.range (b+1), a%k ≠ 0 ∨ b%k ≠ 0 ∨ k=1) := by
  constructor
  · rintro ⟨hb,hc⟩
    refine ⟨hb,fun k _hk => ?_⟩
    by_cases ha : a%k = 0
    · by_cases hb' : b%k = 0
      · exact Or.inr (Or.inr (Nat.dvd_one.mp (by
          rw [←hc]
          exact Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb'))))
      · exact Or.inr (Or.inl hb')
    · exact Or.inl ha
  · rintro ⟨hb,h⟩
    refine ⟨hb,?_⟩
    have hg : a.gcd b ∈ List.range (b+1) := by
      simp only [List.mem_range,Nat.lt_succ_iff]
      exact Nat.gcd_le_right a hb
    have hh := h (a.gcd b) hg
    simpa [Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b),
      Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)] using hh

theorem coprime_positive_primrec : PrimrecPred (fun p : ℕ × ℕ => 0 < p.2 ∧ p.1.Coprime p.2) := by
  have hr : PrimrecRel (fun k (p : ℕ × ℕ) => p.1%k ≠ 0 ∨ p.2%k ≠ 0 ∨ k=1) :=
    ((Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.const 0)).not).or
    (((Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (Primrec.const 0)).not).or (Primrec.eq.comp Primrec.fst (Primrec.const 1)))
  have hh := (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    (hr.forall_mem_list.comp (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)) Primrec.id)
  exact hh.of_eq (fun p => (coprime_bounded p.1 p.2).symm)

theorem valid_primrec : PrimrecPred valid :=
  coprime_positive_primrec.comp ((magnitude_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair
    (Primrec.snd.comp Primrec.unpair))

theorem canonicalCode_primrec : Primrec canonicalCode :=
  Primrec.ite valid_primrec Primrec.id (Primrec.const (encode (0 : ℚ)))

theorem decode_invalid (n : ℕ) (hv : ¬valid n) : decode (α := ℚ) n = none := by
  let z := Equiv.intEquivNat.symm (Nat.unpair n).1
  have hz : decode (α := ℤ) (Nat.unpair n).1 = some z := rfl
  have henc : encode z = (Nat.unpair n).1 := Equiv.intEquivNat.apply_symm_apply _
  have hbad : ¬(0 < (Nat.unpair n).2 ∧ z.natAbs.Coprime (Nat.unpair n).2) := by
    simpa only [valid, ←henc, magnitude_encode_int] using hv
  have hsub : decode (α := { b : ℕ // 0 < b ∧ z.natAbs.Coprime b }) (Nat.unpair n).2 = none := by
    change Encodable.decodeSubtype (P := fun b => 0 < b ∧ z.natAbs.Coprime b) _ = none
    simp [Encodable.decodeSubtype,hbad]
  have hsigma : decode (α := Σ z : ℤ, { b : ℕ // 0 < b ∧ z.natAbs.Coprime b }) n = none := by
    change Encodable.decodeSigma (γ := fun z : ℤ => { b : ℕ // 0 < b ∧ z.natAbs.Coprime b }) n = none
    simp only [Encodable.decodeSigma]
    rw [hz]
    simp only [Option.bind_some]
    rw [hsub]
    rfl
  simp only [Encodable.decode_ofEquiv,hsigma,Option.map_none]

theorem canonicalCode_eq (n : ℕ) : canonicalCode n = encode (rationalEnumeration n) := by
  by_cases hv : valid n
  · obtain ⟨q,rfl⟩ := (valid_iff n).mp hv
    simp only [canonicalCode,ite_eq_left hv,rationalEnumeration,encodek,Option.getD_some]
  · have hn := decode_invalid n hv
    simp only [canonicalCode,ite_eq_right hv,rationalEnumeration,hn,Option.getD_none]

theorem numeratorCode_primrec : Primrec numeratorCode :=
  (Primrec.fst.comp Primrec.unpair).comp canonicalCode_primrec
theorem numeratorMagnitude_primrec : Primrec numeratorMagnitude :=
  magnitude_primrec.comp numeratorCode_primrec
theorem denominator_primrec : Primrec denominator :=
  (Primrec.snd.comp Primrec.unpair).comp canonicalCode_primrec
theorem negative_primrec : Primrec negative := Primrec.nat_bodd.comp numeratorCode_primrec

theorem numeratorCode_eq (n : ℕ) : numeratorCode n = encode (rationalEnumeration n).num := by
  rw [numeratorCode,canonicalCode_eq,encode_rat,Nat.unpair_pair]
theorem numeratorMagnitude_eq (n : ℕ) : numeratorMagnitude n = (rationalEnumeration n).num.natAbs := by
  rw [numeratorMagnitude,numeratorCode_eq,magnitude_encode_int]
theorem denominator_eq (n : ℕ) : denominator n = (rationalEnumeration n).den := by
  rw [denominator,canonicalCode_eq,encode_rat,Nat.unpair_pair]
theorem denominator_pos (n : ℕ) : 0 < denominator n := by
  rw [denominator_eq]
  exact (rationalEnumeration n).den_pos

theorem query_value (n : ℕ) : (rationalEnumeration n : ℝ) =
    if negative n then -(numeratorMagnitude n : ℝ)/(denominator n : ℝ)
    else (numeratorMagnitude n : ℝ)/(denominator n : ℝ) := by
  rw [negative,numeratorCode_eq,numeratorMagnitude_eq,denominator_eq,Rat.cast_def]
  cases hz : (rationalEnumeration n).num with
  | ofNat k =>
    rw [encode_int_nonneg]
    simp [Nat.bodd_mul]
  | negSucc k => simp [encode_int_neg,Nat.bodd_mul]

end RationalCoding
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Computable

namespace BranchMachine

theorem stage_approximates (p q : OracleCode) (j h : ℕ)
    {g : ℕ →. ℕ} {gs : ℕ → ℕ →. ℕ}
    (hg : ∀ k, Approximates (g k) (fun m => gs m k)) :
    ∀ n k, Approximates (stage p q j h g n k)
      (fun m => stage p q j h (gs m) n k) := by
  intro n
  induction n with
  | zero => intro k; exact hg _
  | succ n ih =>
    intro k
    apply (ih j).bind
    intro b
    apply OracleCode.eval_approximates _ q k
    intro x
    apply partialJoin_approximates
    · exact OracleCode.eval_approximates
        (fun x => partialJoin_approximates ih (fun k => hg _) x) p
    · intro x; exact hg _

variable {α : Type*} [Primcodable α]

theorem increment_index_computable (h : ℕ) :
    Computable₂ (fun b k : ℕ => if b = h then 2*k+1 else 4*k+2) := by
  apply (Computable.cond ((Primrec.beq.comp Primrec.fst (Primrec.const h)).to_comp)
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      (Primrec.const 1)).to_comp)
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd)
      (Primrec.const 2)).to_comp)).of_eq
  intro z
  by_cases hh : z.1 = h
  · simp [hh]
  · have he : (z.1 == h) = false := Bool.eq_false_iff.mpr (fun he => hh (beq_iff_eq.mp he))
    simp [hh,he]

theorem step_partrec (p q : OracleCode) (j h : ℕ)
    {g old : α → ℕ →. ℕ} (hg : Partrec₂ g) (ho : Partrec₂ old) :
    Partrec₂ (fun a k => step p q j h (g a) (old a) k) := by
  change Partrec (fun z : α × ℕ => (old z.1 j).bind _)
  apply Partrec.bind (ho.comp fst (Computable.const j))
  let β := (α × ℕ) × ℕ
  have hleft : Partrec₂ (fun z : β => old z.1.1) :=
    ho.comp (fst.comp (fst.comp fst)) snd
  have hinc : Partrec₂ (fun z : β => increment (g z.1.1) h z.2) :=
    hg.comp (fst.comp (fst.comp fst))
      ((increment_index_computable h).comp (snd.comp fst) snd)
  have hforward := OracleCode.eval_partrec (partialJoin_partrec hleft hinc) p
  have hanchor : Partrec₂ (fun z : β => anchor (g z.1.1)) :=
    hg.comp (fst.comp (fst.comp fst))
      ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.snd)
        (Primrec.const 4)).to_comp)
  exact (OracleCode.eval_partrec (partialJoin_partrec hforward hanchor) q).comp
    Computable.id (snd.comp fst)

theorem stage_finite_partrec (p q : OracleCode) (j h : ℕ) :
    Partrec (fun z : List ℕ × ℕ × ℕ => stage p q j h (lookup z.1) z.2.1 z.2.2) := by
  let α := List ℕ × ℕ × ℕ
  let body (c : Nat.Partrec.Code) (z : α) : Part ℕ :=
    if z.2.1 == 0 then initial (lookup z.1) z.2.2 else
      step p q j h (lookup z.1)
        (fun k => c.eval (Encodable.encode (z.1, z.2.1-1, k))) z.2.2
  have hb : Partrec₂ body := by
    apply partrec_cond ((Primrec.beq.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)).to_comp)
    · exact lookup_partrec.comp (fst.comp snd)
        ((Primrec.nat_mul.comp (Primrec.const 8)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp)
    · have hg : Partrec₂ (fun z : Nat.Partrec.Code × α => lookup z.2.1) :=
        lookup_partrec.comp (fst.comp (snd.comp fst)) snd
      have ho : Partrec₂ (fun z : Nat.Partrec.Code × α =>
          fun k => z.1.eval (Encodable.encode (z.2.1,z.2.2.1-1,k))) :=
        Nat.Partrec.Code.eval_part.comp (fst.comp fst)
          ((Computable.encode (α := List ℕ × ℕ × ℕ)).comp ((fst.comp (snd.comp fst)).pair
            ((Computable.pred.comp (fst.comp (snd.comp (snd.comp fst)))).pair snd)))
      exact (step_partrec p q j h hg ho).comp Computable.id (snd.comp (snd.comp snd))
  obtain ⟨c,hc⟩ := partrec_fixed_point hb
  have heq : ∀ n L k, c.eval (Encodable.encode (L,n,k)) = stage p q j h (lookup L) n k := by
    intro n
    induction n with
    | zero => intro L k; rw [hc]; rfl
    | succ n ih =>
      intro L k
      rw [hc]
      have hn0 : (n+1 == 0) = false := rfl
      simp only [body, hn0,
        Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel, stage]
      congr 1
      funext i
      exact ih L i
  exact (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.encode).of_eq
    (fun z => heq z.2.1 z.1 z.2.2)

end BranchMachine
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Encodable

namespace UniformOracle
variable {O : Set (ℕ →. ℕ)}

private theorem flag_primrec : Primrec flag := by
  apply (Primrec.cond (Primrec.option_isSome.comp (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases hh : ((decode (α := Option ℕ) n).getD none).isSome <;> simp only [flag,hh] <;> rfl
private theorem answer_primrec : Primrec answer :=
  Primrec.option_getD_default.comp (Primrec.option_getD_default.comp Primrec.decode)

theorem total_search {E : ℕ → ℕ → Option ℕ}
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (f : ℕ → ℕ) (hsound : ∀ n m a, a ∈ E n m → a = f n)
    (hcomplete : ∀ n, ∃ m a, a ∈ E n m) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) := by
  have hflag := total_comp (total_primrec flag_primrec) hE
  have hfind := Nat.RecursiveIn.rfind hflag
  have hpair := Nat.RecursiveIn.pair (total_primrec Primrec.id) hfind
  have hrun := Nat.RecursiveIn.comp (total_primrec answer_primrec)
    (Nat.RecursiveIn.comp hE hpair)
  apply hrun.of_eq_tot
  intro n
  have hex : ∃ m, (E n m).isSome = true := by
    obtain ⟨m,a,ha⟩ := hcomplete n
    exact ⟨m, Option.isSome_iff_exists.mpr ⟨a,ha⟩⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hm
  have hval : a = f n := hsound n m a ha
  have hmem : m ∈ Nat.rfind (fun k =>
      (fun v : ℕ => decide (v=0)) <$> Part.some (flag (encode (E n k)))) := by
    apply Nat.mem_rfind.mpr
    constructor
    · simp [flag, m, hm]
    · intro k hk
      have hk' : (E n k).isSome = false := Bool.eq_false_iff.mpr (Nat.find_min hex hk)
      simp [flag, hk']
  apply Part.mem_bind_iff.mpr
  refine ⟨encode (E n m), ?_, ?_⟩
  · apply Part.mem_bind_iff.mpr
    refine ⟨Nat.pair n m, ?_, ?_⟩
    · simp only [Seq.seq]
      apply Part.mem_bind_iff.mpr
      refine ⟨Nat.pair n, (Part.mem_map_iff _).mpr ⟨n,Part.mem_some _,rfl⟩, ?_⟩
      exact (Part.mem_map_iff _).mpr ⟨m,by simpa only [Nat.unpair_pair] using hmem,rfl⟩
    · simp
  · have hea : E n m = some a := Option.mem_def.mp ha
    apply Part.mem_some_iff.mpr
    rw [hea]
    simpa only [answer, Encodable.encodek, Option.getD_some] using hval.symm

theorem trial_recursive (g : ℕ → ℕ) (c : Nat.Partrec.Code) :
    Nat.RecursiveIn {fun n => Part.some (g n)}
      (fun z => Part.some (encode (trial g c (Nat.unpair z).1 (Nat.unpair z).2))) := by
  have hm := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hk := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hn := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp Primrec.unpair)
  have hp := total_comp (prefix_recursive g) hm
  have he := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.encode.comp
    (Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.unpair).pair (Primrec.const c)).pair
        (Primrec.snd.comp Primrec.unpair))))
  exact (total_comp he (total_pair hk (total_pair hp hn))).of_eq (fun z => by
    simp [trial])

theorem compute_of_finite (g f : ℕ → ℕ) (c : Nat.Partrec.Code)
    (ha : ∀ n, Approximates (Part.some (f n))
      (fun m => c.eval (Nat.pair (encode (oraclePrefix g m)) n))) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (f n)) := by
  apply total_search (trial_recursive g c) f
  · intro n z a h
    exact Part.mem_some_iff.mp ((ha n).1 (Nat.unpair z).1 a
      (Nat.Partrec.Code.evaln_sound h))
  · intro n
    obtain ⟨M,hM⟩ := (ha n).2 (f n) (Part.mem_some _)
    obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp (hM M le_rfl)
    exact ⟨Nat.pair M k,f n,by simpa [trial] using hk⟩

theorem stage_recursive (p q : OracleCode) (j h : ℕ) (g f : ℕ → ℕ)
    (hf : ∀ n k, BranchMachine.stage p q j h (fun x => Part.some (g x)) n k =
      Part.some (f (Nat.pair n k))) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (f n)) := by
  obtain ⟨c,hc⟩ := partrec_code (BranchMachine.stage_finite_partrec p q j h)
  have hc' (L : List ℕ) (z : ℕ) :
      c.eval (Nat.pair (encode L) z) =
        BranchMachine.stage p q j h (BranchMachine.lookup L) (Nat.unpair z).1 (Nat.unpair z).2 := by
    have hh := hc (L,(Nat.unpair z).1,(Nat.unpair z).2)
    change c.eval (Nat.pair (encode L) (Nat.pair (Nat.unpair z).1 (Nat.unpair z).2)) = _ at hh
    simpa only [Nat.pair_unpair] using hh
  apply compute_of_finite g f c
  intro z
  have hh := BranchMachine.stage_approximates p q j h (prefix_approximates g)
    (Nat.unpair z).1 (Nat.unpair z).2
  simpa only [← hc', hf, Nat.pair_unpair] using hh

end UniformOracle
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RationalCut
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace RationalCoding

theorem positiveNumerator_primrec : Primrec positiveNumerator :=
  Primrec.ite (Primrec.eq.comp negative_primrec (Primrec.const true)) (Primrec.const 0)
    numeratorMagnitude_primrec

theorem negativeNumerator_primrec : Primrec negativeNumerator :=
  Primrec.ite (Primrec.eq.comp negative_primrec (Primrec.const true)) numeratorMagnitude_primrec
    (Primrec.const 0)

theorem signed_query_value (n : ℕ) : (rationalEnumeration n : ℝ) =
    ((positiveNumerator n : ℝ)-(negativeNumerator n : ℝ))/(denominator n : ℝ) := by
  rw [query_value]
  cases hn : negative n <;> simp [positiveNumerator,negativeNumerator,hn]

theorem ltCode_primrec : PrimrecRel ltCode :=
  Primrec.nat_lt.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (positiveNumerator_primrec.comp Primrec.fst)
        (denominator_primrec.comp Primrec.snd))
      (Primrec.nat_mul.comp (negativeNumerator_primrec.comp Primrec.snd)
        (denominator_primrec.comp Primrec.fst)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (positiveNumerator_primrec.comp Primrec.snd)
        (denominator_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp (negativeNumerator_primrec.comp Primrec.fst)
        (denominator_primrec.comp Primrec.snd)))

theorem ltCode_iff (i j : ℕ) :
    ltCode i j ↔ (rationalEnumeration i : ℝ) < (rationalEnumeration j : ℝ) := by
  have hi : (0 : ℝ) < denominator i := by exact_mod_cast denominator_pos i
  have hj : (0 : ℝ) < denominator j := by exact_mod_cast denominator_pos j
  rw [signed_query_value,signed_query_value,div_lt_div_iff₀ hi hj]
  constructor
  · intro h
    have hh : (positiveNumerator i : ℝ)*denominator j + negativeNumerator j*denominator i <
        (positiveNumerator j : ℝ)*denominator i + negativeNumerator i*denominator j := by
      exact_mod_cast h
    nlinarith
  · intro h
    change positiveNumerator i*denominator j + negativeNumerator j*denominator i <
      positiveNumerator j*denominator i + negativeNumerator i*denominator j
    have hh : (positiveNumerator i : ℝ)*denominator j + negativeNumerator j*denominator i <
        (positiveNumerator j : ℝ)*denominator i + negativeNumerator i*denominator j := by nlinarith
    exact_mod_cast hh
end RationalCoding

theorem rational_cut_computable (q : ℚ) :
    Primrec (fun n => if cut (q : ℝ) n then (1 : ℕ) else 0) := by
  have hp := Primrec.ite
    (RationalCoding.ltCode_primrec.comp Primrec.id (Primrec.const (Encodable.encode q)))
    (Primrec.const 1) (Primrec.const 0)
  apply hp.of_eq
  intro n
  have hq : rationalEnumeration (Encodable.encode q) = q := by simp [rationalEnumeration]
  have he : RationalCoding.ltCode n (Encodable.encode q) ↔ (rationalEnumeration n : ℝ) < q := by
    rw [RationalCoding.ltCode_iff,hq]
  by_cases h : (rationalEnumeration n : ℝ) < q
  · simp [he,h,cut]
  · simp [he,h,cut]

theorem rational_cut_reduces (q : ℚ) (A : Oracle) : Reduces (cut (q : ℝ)) A := by
  exact RecursiveIn.iff_nat.mpr (UniformOracle.total_primrec (rational_cut_computable q))

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BinaryMachine
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle RationalCoding Encodable

theorem eventually_constant_reduces (B A : Oracle) (b : Bool) (N : ℕ)
    (h : ∀ n, N ≤ n → B n = b) : Reduces B A := by
  let L := (List.range N).map (bit B)
  let d : ℕ := if b then 1 else 0
  have hp : Primrec (fun n => L.getD n d) := (Primrec.list_getD d).comp (Primrec.const L) Primrec.id
  have he (n : ℕ) : L.getD n d = bit B n := by
    by_cases hn : n < N
    · simp [L, List.getD, List.getElem?_map, List.getElem?_range hn]
    · have hb := h n (by omega)
      have hz : (List.range N)[n]? = none := List.getElem?_eq_none (by simp; omega)
      simp [L, List.getD, hz, bit, hb, d]
  apply RecursiveIn.iff_nat.mpr
  exact _root_.OAI.TuringRigidity.UniformOracle.total_primrec (hp.of_eq he)

theorem mixed_of_noncomputable (B : Oracle) (h : ¬ Reduces B (fun _ => false)) : Mixed B := by
  intro N
  constructor
  · by_contra hn
    push Not at hn
    apply h
    exact eventually_constant_reduces B _ false N (fun n hN => Bool.eq_false_iff.mpr (hn n hN))
  · by_contra hn
    push Not at hn
    apply h
    exact eventually_constant_reduces B _ true N (fun n hN => Bool.eq_true_of_not_eq_false (hn n hN))

theorem foldNumeral_primrec : Primrec foldNumeral :=
  Primrec.list_foldl Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) Primrec.snd).comp Primrec.snd).to₂

theorem foldNumeral_prefix (B : Oracle) (n : ℕ) :
    foldNumeral (oraclePrefix (bit B) n) = numeral B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [foldNumeral, oraclePrefix, List.range_succ, List.foldl_append, numeral] using
      congrArg (fun a => 2*a+bit B n) ih

theorem numeral_recursive (B : Oracle) :
    Nat.RecursiveIn {oracleFunction B} (fun n => Part.some (numeral B n)) := by
  have hf := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (foldNumeral_primrec.comp
      (Primrec.option_getD_default.comp Primrec.decode))) (prefix_recursive (bit B))
  exact hf.of_eq (fun n => by simp only [encodek, Option.getD_some, foldNumeral_prefix])

theorem powTwo_primrec : Primrec (fun n : ℕ => 2^n) := by
  have hp : Primrec (fun n : ℕ => (List.range n).foldl (fun a _ => 2*a) 1) :=
    Primrec.list_foldl Primrec.list_range (Primrec.const 1)
      ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst).comp Primrec.snd).to₂
  apply hp.of_eq
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih, pow_succ, Nat.mul_comm]

theorem fracLeft_primrec : Primrec fracLeft := Primrec.nat_mul.comp
  (positiveNumerator_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
theorem fracRight_primrec : Primrec fracRight := Primrec.nat_add.comp
  (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (denominator_primrec.comp Primrec.fst))
  (Primrec.nat_mul.comp (negativeNumerator_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem frac_lt_iff (q k D : ℕ) (hD : 0 < D) :
    fracLeft (q,k,D) < fracRight (q,k,D) ↔ (rationalEnumeration q : ℝ) < (k : ℝ)/D := by
  rw [signed_query_value, div_lt_div_iff₀ (by exact_mod_cast denominator_pos q) (by exact_mod_cast hD)]
  unfold fracLeft fracRight
  constructor <;> intro h
  · have hh : (positiveNumerator q : ℝ)*D < k*denominator q + negativeNumerator q*D := by exact_mod_cast h
    nlinarith
  · have hh : (positiveNumerator q : ℝ)*D < k*denominator q + negativeNumerator q*D := by nlinarith
    exact_mod_cast hh

theorem lt_frac_iff (q k D : ℕ) (hD : 0 < D) :
    fracRight (q,k,D) < fracLeft (q,k,D) ↔ (k : ℝ)/D < (rationalEnumeration q : ℝ) := by
  rw [signed_query_value, div_lt_div_iff₀ (by exact_mod_cast hD) (by exact_mod_cast denominator_pos q)]
  unfold fracLeft fracRight
  constructor <;> intro h
  · have hh : k* (denominator q : ℝ) + negativeNumerator q*D < positiveNumerator q*D := by exact_mod_cast h
    nlinarith
  · have hh : k* (denominator q : ℝ) + negativeNumerator q*D < positiveNumerator q*D := by nlinarith
    exact_mod_cast hh

theorem frac_eq_iff (q k D : ℕ) (hD : 0 < D) :
    fracLeft (q,k,D) = fracRight (q,k,D) ↔ (rationalEnumeration q : ℝ) = (k : ℝ)/D := by
  constructor
  · intro he
    apply le_antisymm
    · exact le_of_not_gt (fun h => by have := (lt_frac_iff q k D hD).mpr h; omega)
    · exact le_of_not_gt (fun h => by have := (frac_lt_iff q k D hD).mpr h; omega)
  · intro he
    apply Nat.le_antisymm
    · exact Nat.le_of_not_gt (fun h => by have := (lt_frac_iff q k D hD).mp h; linarith)
    · exact Nat.le_of_not_gt (fun h => by have := (frac_lt_iff q k D hD).mp h; linarith)

end TuringRigidity.BinarySeries

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BinaryCut
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle RationalCoding Encodable Filter

theorem approxDecision_primrec : Primrec approxDecision := by
  have hD : Primrec (fun z : ℕ × ℕ × ℕ => 2^z.2.1) := powTwo_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hlo := Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair hD)
  have hhi := Primrec.fst.pair ((Primrec.succ.comp (Primrec.snd.comp Primrec.snd)).pair hD)
  exact Primrec.ite (Primrec.nat_lt.comp (fracLeft_primrec.comp hlo) (fracRight_primrec.comp hlo))
    (Primrec.const (some 1))
    (Primrec.ite (Primrec.nat_lt.comp (fracRight_primrec.comp hhi) (fracLeft_primrec.comp hhi))
      (Primrec.const (some 0)) (Primrec.const none))

theorem approxTrial_recursive (B : Oracle) :
    Nat.RecursiveIn {oracleFunction B}
      (fun z => Part.some (encode (approxTrial B (Nat.unpair z).1 (Nat.unpair z).2))) := by
  have hq := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction B}) (Primrec.fst.comp Primrec.unpair)
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction B}) (Primrec.snd.comp Primrec.unpair)
  have hk := _root_.OAI.TuringRigidity.UniformOracle.total_comp (numeral_recursive B) hn
  have hdec := Primrec.encode.comp (approxDecision_primrec.comp
    ((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hdec) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hq (_root_.OAI.TuringRigidity.UniformOracle.total_pair hn hk))).of_eq
    (fun z => by simp [approxTrial])

theorem approxTrial_sound (B : Oracle) (q n a : ℕ) (ha : a ∈ approxTrial B q n) :
    a = if cut (value B) q then 1 else 0 := by
  have hb := bracket B n
  unfold approxTrial approxDecision at ha
  split at ha
  · rename_i h
    have hq := (frac_lt_iff q (numeral B n) (2^n) (by positivity)).mp h
    have hc : cut (value B) q = true := (cut_eq_true _ _).mpr (lt_of_lt_of_le (by simpa using hq) hb.1)
    simpa [hc] using (Option.mem_def.mp ha).symm
  · split at ha
    · rename_i h
      have hq := (lt_frac_iff q (numeral B n+1) (2^n) (by positivity)).mp h
      have hc : cut (value B) q = false := Bool.eq_false_iff.mpr (fun hc => by
        have hh := (cut_eq_true _ _).mp hc
        push_cast at hq
        linarith)
      simpa [hc] using (Option.mem_def.mp ha).symm
    · simp at ha

theorem small_width (ε : ℝ) (hε : 0 < ε) : ∃ n : ℕ, (2^n : ℝ)⁻¹ < ε := by
  have ht : Tendsto (fun n : ℕ => (2^n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(2:ℝ)⁻¹| < 1))
  exact (ht.eventually (eventually_lt_nhds hε)).exists

theorem approxTrial_complete (B : Oracle) (hi : Irrational (value B)) (q : ℕ) :
    ∃ n a, a ∈ approxTrial B q n := by
  have hne : (rationalEnumeration q : ℝ) ≠ value B := fun h => hi ⟨_,h⟩
  rcases lt_or_gt_of_ne hne with hq | hq
  · obtain ⟨n,hn⟩ := small_width (value B - rationalEnumeration q) (by linarith)
    have hb := bracket B n
    have hl : (rationalEnumeration q : ℝ) < (numeral B n : ℝ)/(2^n : ℕ) := by
      push_cast
      rw [add_div] at hb
      simp only [one_div] at hb
      linarith
    have hd := (frac_lt_iff q (numeral B n) (2^n) (by positivity)).mpr hl
    exact ⟨n,1,by simp [approxTrial,approxDecision,hd]⟩
  · obtain ⟨n,hn⟩ := small_width (rationalEnumeration q - value B) (by linarith)
    have hb := bracket B n
    have hu : ((numeral B n+1 : ℕ) : ℝ)/(2^n : ℕ) < rationalEnumeration q := by
      push_cast
      rw [add_div]
      simp only [one_div]
      linarith
    have hd := (lt_frac_iff q (numeral B n+1) (2^n) (by positivity)).mpr hu
    have hl : ¬ fracLeft (q,numeral B n,2^n) < fracRight (q,numeral B n,2^n) := by
      intro hh
      have hh' := (frac_lt_iff q (numeral B n) (2^n) (by positivity)).mp hh
      push_cast at hh'
      linarith [hb.1]
    exact ⟨n,0,by simp [approxTrial,approxDecision,hl,hd]⟩

theorem cut_reduces (B : Oracle) (hi : Irrational (value B)) : Reduces (cut (value B)) B := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (approxTrial_recursive B) _ (approxTrial_sound B) (approxTrial_complete B hi)

end TuringRigidity.BinarySeries

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BinaryRecovery
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle RationalCoding Encodable

theorem recoverGuard_primrec : PrimrecPred recoverGuard := by
  have hn : Primrec (fun z : ℕ × ℕ × ℕ × ℕ => 2^(z.1+1)) :=
    powTwo_primrec.comp (Primrec.succ.comp Primrec.fst)
  have hk : Primrec (fun z : ℕ × ℕ × ℕ × ℕ => z.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.eq.comp (fracLeft_primrec.comp (hi.pair (hk.pair hn)))
    (fracRight_primrec.comp (hi.pair (hk.pair hn)))).and
    (Primrec.eq.comp (fracLeft_primrec.comp (hj.pair ((Primrec.succ.comp hk).pair hn)))
      (fracRight_primrec.comp (hj.pair ((Primrec.succ.comp hk).pair hn))))

theorem recoverDecision_primrec : Primrec recoverDecision :=
  Primrec.ite ((recoverGuard_primrec.comp Primrec.fst).and
    ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).and
      (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))))
    (Primrec.option_some.comp (Primrec.nat_mod.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 2))) (Primrec.const none)

theorem recoverTrial_recursive (B : Oracle) :
    Nat.RecursiveIn {oracleFunction (cut (value B))}
      (fun z => Part.some (encode (recoverTrial B (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction (cut (value B))}
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hm := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.snd.comp Primrec.unpair)
  have hk := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.fst.comp Primrec.unpair)) hm
  have hi := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))) hm
  have hj := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))) hm
  have hg : Nat.RecursiveIn O (oracleFunction (cut (value B))) := .oracle _ (Set.mem_singleton _)
  have hmeta := _root_.OAI.TuringRigidity.UniformOracle.total_pair hn (_root_.OAI.TuringRigidity.UniformOracle.total_pair hk (_root_.OAI.TuringRigidity.UniformOracle.total_pair hi hj))
  have hbits := _root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_comp hg hi) (_root_.OAI.TuringRigidity.UniformOracle.total_comp hg hj)
  have hdecode : Primrec (fun z : ℕ =>
      (((Nat.unpair (Nat.unpair z).1).1,
        (Nat.unpair (Nat.unpair (Nat.unpair z).1).2).1,
        Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair z).1).2).2),Nat.unpair (Nat.unpair z).2)) := by
    exact (((Primrec.fst.comp Primrec.unpair).pair
      (((Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).comp
        (Primrec.snd.comp Primrec.unpair))).comp (Primrec.fst.comp Primrec.unpair)).pair
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.encode.comp (recoverDecision_primrec.comp hdecode)))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair hmeta hbits)).of_eq (fun z => by simp [recoverTrial,bit])

theorem recoverTrial_sound (B : Oracle) (hB : Mixed B) (n m a : ℕ)
    (ha : a ∈ recoverTrial B n m) : a = bit B n := by
  let k := (Nat.unpair m).1
  let i := (Nat.unpair (Nat.unpair m).2).1
  let j := (Nat.unpair (Nat.unpair m).2).2
  change a ∈ recoverDecision ((n,k,i,j),(bit (cut (value B)) i,bit (cut (value B)) j)) at ha
  unfold recoverDecision at ha
  split at ha
  · rename_i h
    have hai : a=k%2 := by simpa using (Option.mem_def.mp ha).symm
    have hi := (frac_eq_iff i k (2^(n+1)) (by positivity)).mp h.1.1
    have hj := (frac_eq_iff j (k+1) (2^(n+1)) (by positivity)).mp h.1.2
    have hci : cut (value B) i=true := by cases hh : cut (value B) i <;> simp_all [bit]
    have hcj : cut (value B) j=false := by cases hh : cut (value B) j <;> simp_all [bit]
    have hlo := (cut_eq_true _ _).mp hci
    have hup : value B ≤ (rationalEnumeration j : ℝ) := le_of_not_gt (fun hh => by
      have := (cut_eq_true _ _).mpr hh; simp_all)
    rw [hi] at hlo
    rw [hj] at hup
    have hb := strict_bracket B hB (n+1)
    have hD : (0 : ℝ) < (2^(n+1) : ℝ) := by positivity
    have hk1 : (k : ℝ) < numeral B (n+1)+1 := by
      have hh := lt_trans hlo hb.2
      push_cast at hh
      exact (div_lt_div_iff_of_pos_right hD).mp hh
    have hk2 : (numeral B (n+1) : ℝ) < k+1 := by
      have hh := lt_of_lt_of_le hb.1 hup
      push_cast at hh
      exact (div_lt_div_iff_of_pos_right hD).mp hh
    have hk : k = numeral B (n+1) := by
      have h1 : k < numeral B (n+1)+1 := by exact_mod_cast hk1
      have h2 : numeral B (n+1) < k+1 := by exact_mod_cast hk2
      omega
    rw [hai,hk,numeral]
    unfold bit
    split <;> omega
  · simp at ha

theorem recoverTrial_complete (B : Oracle) (hB : Mixed B) (n : ℕ) :
    ∃ m a, a ∈ recoverTrial B n m := by
  let k := numeral B (n+1)
  let i := encode ((k : ℚ)/2^(n+1))
  let j := encode (((k+1 : ℕ) : ℚ)/2^(n+1))
  have hi : (rationalEnumeration i : ℝ) = (k : ℝ)/(2^(n+1) : ℕ) := by simp [i,rationalEnumeration]
  have hj : (rationalEnumeration j : ℝ) = ((k+1 : ℕ) : ℝ)/(2^(n+1) : ℕ) := by simp [j,rationalEnumeration]
  have hg : recoverGuard (n,k,i,j) := ⟨(frac_eq_iff _ _ _ (by positivity)).mpr hi,
    (frac_eq_iff _ _ _ (by positivity)).mpr hj⟩
  have hb := strict_bracket B hB (n+1)
  have hci : cut (value B) i=true := (cut_eq_true _ _).mpr (by simpa [hi,k] using hb.1)
  have hcj : cut (value B) j=false := Bool.eq_false_iff.mpr (fun hh => by
    have hh' := (cut_eq_true _ _).mp hh
    rw [hj] at hh'
    push_cast at hh'
    dsimp only [k] at hh'
    linarith [hb.2])
  exact ⟨Nat.pair k (Nat.pair i j),k%2,by simp [recoverTrial,recoverDecision,bit,hci,hcj,hg]⟩

theorem set_reduces_cut (B : Oracle) (hB : Mixed B) : Reduces B (cut (value B)) := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (recoverTrial_recursive B) _ (recoverTrial_sound B hB) (recoverTrial_complete B hB)

end TuringRigidity.BinarySeries

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_ProgramTopology
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

namespace OpenFiber
variable {X : Type*} {α β : Type} [TopologicalSpace X]

theorem const (p : Part α) : OpenFiber (fun _ : X => p) := by
  intro a
  by_cases h : a ∈ p <;> simp [h]

theorem map {f : X → Part α} (hf : OpenFiber f) (g : α → β) :
    OpenFiber (fun x => (f x).map g) := by
  intro b
  have heq : {x | b ∈ (f x).map g} =
      ⋃ a : α, {x : X | g a = b} ∩ {x | a ∈ f x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Part.mem_map_iff]
    exact ⟨fun ⟨a,ha,hg⟩ => ⟨a,hg,ha⟩, fun ⟨a,hg,ha⟩ => ⟨a,ha,hg⟩⟩
  rw [heq]
  apply isOpen_iUnion
  intro a
  have hg : IsOpen {x : X | g a = b} := by by_cases h : g a = b <;> simp [h]
  exact hg.inter (hf a)

theorem bind {f : X → Part α} {g : X → α → Part β}
    (hf : OpenFiber f) (hg : ∀ a, OpenFiber (fun x => g x a)) :
    OpenFiber (fun x => (f x).bind (g x)) := by
  intro b
  have heq : {x | b ∈ (f x).bind (g x)} =
      ⋃ a : α, {x | a ∈ f x} ∩ {x | b ∈ g x a} := by
    ext x
    simp [Part.mem_bind_iff]
  rw [heq]
  exact isOpen_iUnion (fun a => (hf a).inter (hg a b))

theorem seq {f : X → Part (α → β)} {g : X → Part α}
    (hf : OpenFiber f) (hg : OpenFiber g) :
    OpenFiber (fun x => f x <*> g x) := by
  exact hf.bind (fun k => hg.map k)

theorem some [TopologicalSpace α] [DiscreteTopology α] {f : X → α} (hf : Continuous f) :
    OpenFiber (fun x => Part.some (f x)) := by
  intro a
  simpa [Set.preimage, Part.mem_some_iff, eq_comm] using
    (isOpen_discrete ({a} : Set α)).preimage hf

theorem rfind {p : X → ℕ → Part Bool} (hp : ∀ n, OpenFiber (fun x => p x n)) :
    OpenFiber (fun x => Nat.rfind (p x)) := by
  intro n
  have heq : {x | n ∈ Nat.rfind (p x)} =
      {x | true ∈ p x n} ∩ ⋂ k : Fin n, {x | false ∈ p x k.val} := by
    ext x
    constructor
    · intro h
      have hr := Nat.mem_rfind.mp h
      exact ⟨hr.1, Set.mem_iInter.mpr (fun k => hr.2 k.isLt)⟩
    · rintro ⟨h,hmin⟩
      exact Nat.mem_rfind.mpr ⟨h,fun {k} hk => Set.mem_iInter.mp hmin ⟨k,hk⟩⟩
  rw [heq]
  exact (hp n true).inter (isOpen_iInter_of_finite (fun k : Fin n => hp k.val false))
end OpenFiber

namespace OracleCode

theorem eval_openFiber {X : Type*} [TopologicalSpace X] (O : X → ℕ → ℕ)
    (hO : ∀ n, Continuous (fun x => O x n)) (c : OracleCode) :
    ∀ n, OpenFiber (fun x => eval (fun k => Part.some (O x k)) c n) := by
  induction c with
  | zero => intro n; exact OpenFiber.const _
  | succ => intro n; exact OpenFiber.const _
  | left => intro n; exact OpenFiber.const _
  | right => intro n; exact OpenFiber.const _
  | query => intro n; exact OpenFiber.some (hO n)
  | pair c d hc hd => intro n; exact (OpenFiber.map (hc n) Nat.pair).seq (hd n)
  | comp c d hc hd => intro n; exact (hd n).bind (fun k => hc k)
  | prec c d hc hd =>
      intro p
      have hrec : ∀ k : ℕ, OpenFiber (fun x =>
          Nat.rec (eval (fun j => Part.some (O x j)) c (Nat.unpair p).1)
            (fun y ih => ih.bind (fun i =>
              eval (fun j => Part.some (O x j)) d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k) := by
        intro k
        induction k with
        | zero => exact hc _
        | succ k ih => exact ih.bind (fun i => hd _)
      exact hrec (Nat.unpair p).2
  | find c hc =>
      intro n
      exact OpenFiber.rfind (fun k => (hc (Nat.pair n k)).map (fun m => decide (m=0)))

theorem halting_set_open (c : OracleCode) (n m : ℕ) :
    IsOpen {A : Oracle | m ∈ eval (oracleFunction A) c n} := by
  have hO : ∀ n : ℕ, Continuous (fun A : Oracle => if A n then (1 : ℕ) else 0) := by
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      (continuous_apply n)
  exact eval_openFiber _ hO c n m

theorem eval_eq_oracle_iff (c : OracleCode) (A B : Oracle) :
    eval (oracleFunction A) c = oracleFunction B ↔
      ∀ n, (if B n then 1 else 0) ∈ eval (oracleFunction A) c n := by
  constructor
  · intro h n
    rw [h]
    exact Part.mem_some _
  · intro h
    funext n
    exact Part.eq_some_iff.mpr (h n)

theorem success_measurable {X : Type*} [MeasurableSpace X]
    (c : OracleCode) (A B : X → Oracle) (hA : Measurable A) (hB : Measurable B) :
    MeasurableSet {x | eval (oracleFunction (A x)) c = oracleFunction (B x)} := by
  have hv : ∀ n, Measurable (fun x => if B x n then (1 : ℕ) else 0) := by
    intro n
    exact (measurable_of_countable (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      ((measurable_pi_apply n).comp hB)
  have hh (n m : ℕ) : MeasurableSet {x | m ∈ eval (oracleFunction (A x)) c n} :=
    (halting_set_open c n m).measurableSet.preimage hA
  simp_rw [eval_eq_oracle_iff]
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  have heq : {x | (if B x n then 1 else 0) ∈ eval (oracleFunction (A x)) c n} =
      ⋃ m : ℕ, {x | (if B x n then 1 else 0) = m} ∩
        {x | m ∈ eval (oracleFunction (A x)) c n} := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun m => (measurableSet_eq_fun (hv n) measurable_const).inter (hh n m))
end OracleCode

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_ProgramSelection
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem leastSuccess_spec {X : Type*} (R : X → ℕ → Prop) (hex : ∀ x, ∃ n, R x n)
    (x : X) : R x (leastSuccess R hex x) := by
  classical
  exact Nat.find_spec (hex x)

theorem leastSuccess_eq_iff {X : Type*} (R : X → ℕ → Prop) (hex : ∀ x, ∃ n, R x n)
    (x : X) (n : ℕ) : leastSuccess R hex x = n ↔ R x n ∧ ∀ k < n, ¬ R x k := by
  classical
  exact Nat.find_eq_iff (hex x)

theorem leastSuccess_measurable {X : Type*} [MeasurableSpace X] (R : X → ℕ → Prop)
    (hex : ∀ x, ∃ n, R x n) (hR : ∀ n, MeasurableSet {x | R x n}) :
    Measurable (leastSuccess R hex) := by
  apply measurable_to_countable'
  intro n
  have heq : (leastSuccess R hex) ⁻¹' {n} =
      {x | R x n} ∩ ⋂ k : Fin n, {x | ¬ R x k.val} := by
    ext x
    constructor
    · intro h
      have hr := (leastSuccess_eq_iff R hex x n).mp h
      exact ⟨hr.1, Set.mem_iInter.mpr (fun k => hr.2 k.val k.isLt)⟩
    · rintro ⟨h,hmin⟩
      exact (leastSuccess_eq_iff R hex x n).mpr ⟨h,fun k hk => Set.mem_iInter.mp hmin ⟨k,hk⟩⟩
  rw [heq]
  exact (hR n).inter (MeasurableSet.iInter (fun k : Fin n => (hR k.val).compl))

theorem codeEnumeration_surjective : Function.Surjective codeEnumeration := by
  intro c
  refine ⟨Encodable.encode c, ?_⟩
  simp [codeEnumeration]

theorem join_measurable {X : Type*} [MeasurableSpace X] (A B : X → Oracle)
    (hA : Measurable A) (hB : Measurable B) : Measurable (fun x => join (A x) (B x)) := by
  apply Measurable.of_eval
  intro n
  by_cases hn : n.bodd = true
  · simpa [join, hn, Function.comp_def] using (measurable_pi_apply (n/2)).comp hB
  · simpa [join, hn, Function.comp_def] using (measurable_pi_apply (n/2)).comp hA

theorem addition_program_selection (F : ℝ → Oracle) (hF : Measurable F)
    (hadd : ∀ x y, Reduces (F (x+y)) (join (F x) (F y))) :
    ∃ e : ℝ × ℝ → ℕ, Measurable e ∧ ∀ x y,
      OracleCode.eval (oracleFunction (join (F x) (F y))) (codeEnumeration (e (x,y))) =
        oracleFunction (F (x+y)) := by
  let R : (ℝ × ℝ) → ℕ → Prop := fun p n =>
    OracleCode.eval (oracleFunction (join (F p.1) (F p.2))) (codeEnumeration n) =
      oracleFunction (F (p.1+p.2))
  have hR : ∀ n, MeasurableSet {p | R p n} := by
    intro n
    exact OracleCode.success_measurable (codeEnumeration n)
      (fun p : ℝ × ℝ => join (F p.1) (F p.2)) (fun p : ℝ × ℝ => F (p.1+p.2))
      (join_measurable _ _ (hF.comp measurable_fst) (hF.comp measurable_snd))
      (hF.comp ((continuous_fst.add continuous_snd).measurable))
  have hex : ∀ p, ∃ n, R p n := by
    intro p
    obtain ⟨c,hc⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp (hadd p.1 p.2)
    obtain ⟨n,hn⟩ := codeEnumeration_surjective c
    refine ⟨n, ?_⟩
    dsimp [R]
    rw [hn]
    exact hc
  exact ⟨leastSuccess R hex, leastSuccess_measurable R hex hR,
    fun x y => leastSuccess_spec R hex (x,y)⟩

theorem addition_program_continuous_restriction (F : ℝ → Oracle) (hF : Measurable F)
    (hadd : ∀ x y, Reduces (F (x+y)) (join (F x) (F y))) :
    ∃ (e : ℝ × ℝ → ℕ) (E : Set (ℝ × ℝ)), E ∈ residual (ℝ × ℝ) ∧
      ContinuousOn e E ∧ ∀ x y,
      OracleCode.eval (oracleFunction (join (F x) (F y))) (codeEnumeration (e (x,y))) =
        oracleFunction (F (x+y)) := by
  obtain ⟨e, he, hs⟩ := addition_program_selection F hF hadd
  obtain ⟨E,hE,hcont⟩ := measurable_continuousOn_residual e he
  exact ⟨e,E,hE,hcont,hs⟩

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalPrograms
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem locally_constant_on_restriction {X Y : Type*} [PseudoMetricSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] (f : X → Y) (D : Set X)
    (hf : ContinuousOn f D) (x : X) (hx : x ∈ D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ D, dist y x < ε → f y = f x := by
  have hpre : f ⁻¹' {f x} ∈ nhdsWithin x D :=
    (hf x hx) ((isOpen_discrete ({f x} : Set Y)).mem_nhds (by simp))
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  exact ⟨ε,hε,fun y hy hdist => hsub ⟨hdist,hy⟩⟩

theorem fixed_local_indices (t u v : ℝ) (D : Set ℝ) (E : Set (ℝ × ℝ))
    (e : ℝ × ℝ → ℕ) (he : ContinuousOn e E)
    (hgood : (u,v) ∈ goodPairs t D E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      (∀ s ∈ rationalSpan t, ∀ a ∈ rationalSpan t, |s| < ρ → |a| < ρ →
        e (u+s,v-u+a) = e (u,v-u)) ∧
      (∀ s ∈ rationalSpan t, |s| < ρ → e (v+s,u-v) = e (v,u-v)) := by
  have hz : (0 : ℝ) ∈ rationalSpan t := ⟨0,0,by simp⟩
  have hp : (u,v-u) ∈ E := by simpa using (hgood 0 hz).2.1 0 hz
  have hq : (v,u-v) ∈ E := by simpa using (hgood 0 hz).2.2
  obtain ⟨εp,hεp,hpconst⟩ := locally_constant_on_restriction e E he (u,v-u) hp
  obtain ⟨εq,hεq,hqconst⟩ := locally_constant_on_restriction e E he (v,u-v) hq
  let ρ : ℝ := min 1 (min εp εq) / 2
  have hmin : 0 < min 1 (min εp εq) := lt_min (by norm_num) (lt_min hεp hεq)
  have hρ : 0 < ρ := div_pos hmin (by norm_num)
  have hρmin : ρ < min 1 (min εp εq) := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := hρmin.trans_le (min_le_left _ _)
  have hρp : ρ ≤ εp := le_trans hρmin.le ((min_le_right _ _).trans (min_le_left _ _))
  have hρq : ρ ≤ εq := le_trans hρmin.le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ρ,hρ,hρ1,?_,?_⟩
  · intro s hs a ha hsr har
    apply hpconst _ ((hgood s hs).2.1 a ha)
    rw [Prod.dist_eq]
    apply max_lt
    · simpa [Real.dist_eq, add_sub_cancel_left] using hsr.trans_le hρp
    · simpa only [Real.dist_eq, add_sub_cancel_left] using har.trans_le hρp
  · intro s hs hsr
    apply hqconst _ ((hgood s hs).2.2)
    rw [Prod.dist_eq]
    apply max_lt
    · simpa [Real.dist_eq, add_sub_cancel_left] using hsr.trans_le hρq
    · simpa using hεq

theorem fixed_local_programs (F : ℝ → Oracle) (t u v : ℝ)
    (D : Set ℝ) (E : Set (ℝ × ℝ)) (e : ℝ × ℝ → ℕ)
    (he : ContinuousOn e E) (hgood : (u,v) ∈ goodPairs t D E)
    (hspec : ∀ x y, OracleCode.eval (oracleFunction (join (F x) (F y)))
      (codeEnumeration (e (x,y))) = oracleFunction (F (x+y))) :
    ∃ (p q : ℕ) (ρ : ℝ), 0 < ρ ∧ ρ < 1 ∧
      (∀ s ∈ rationalSpan t, ∀ a ∈ rationalSpan t, |s| < ρ → |a| < ρ →
        OracleCode.eval (oracleFunction (join (F (u+s)) (F (v-u+a))))
          (codeEnumeration p) = oracleFunction (F (v+s+a))) ∧
      (∀ s ∈ rationalSpan t, |s| < ρ →
        OracleCode.eval (oracleFunction (join (F (v+s)) (F (u-v))))
          (codeEnumeration q) = oracleFunction (F (u+s))) := by
  obtain ⟨ρ,hρ,hρ1,hp,hq⟩ := fixed_local_indices t u v D E e he hgood
  refine ⟨e (u,v-u),e (v,u-v),ρ,hρ,hρ1,?_,?_⟩
  · intro s hs a ha hsr har
    have heq := hspec (u+s) (v-u+a)
    have hsum : (u+s)+(v-u+a) = v+s+a := by ring
    rw [hp s hs a ha hsr har, hsum] at heq
    exact heq
  · intro s hs hsr
    have heq := hspec (v+s) (u-v)
    have hsum : (v+s)+(u-v) = u+s := by ring
    rw [hq s hs hsr, hsum] at heq
    exact heq

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_Endpoints
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem countable_real_meagre (s : Set ℝ) (hs : s.Countable) : IsMeagre s := by
  have hsingle : ∀ x : ℝ, IsMeagre ({x} : Set ℝ) := by
    intro x
    apply IsNowhereDense.isMeagre
    simp [IsNowhereDense]
  have h := isMeagre_biUnion hs (fun x _ => hsingle x)
  simpa using h

theorem exists_separating_endpoints (F : ℝ → Oracle)
    (hfiber : ∀ B, {x | F x = B}.Countable) (D : Set ℝ) (hD : D ∈ residual ℝ)
    (u ρ : ℝ) (hρ : 0 < ρ) :
    ∃ lo hi : ℝ, -ρ < lo ∧ lo < 0 ∧ 0 < hi ∧ hi < ρ ∧
      u+lo ∈ D ∧ u+hi ∈ D ∧ F (u+lo) ≠ F (u+hi) := by
  have hleft : (D ∩ Ioo (u-ρ) u).Nonempty := by
    obtain ⟨x,hx,hxD⟩ := (dense_of_mem_residual hD).inter_open_nonempty
      (Ioo (u-ρ) u) isOpen_Ioo (nonempty_Ioo.mpr (by linarith))
    exact ⟨x,hxD,hx⟩
  obtain ⟨xm,hxmD,hxmlo,hxmhi⟩ := hleft
  have hfib : IsMeagre {x | F x = F xm} := countable_real_meagre _ (hfiber (F xm))
  have hres : D ∩ {x | F x = F xm}ᶜ ∈ residual ℝ := inter_mem hD hfib
  have hright : ((D ∩ {x | F x = F xm}ᶜ) ∩ Ioo u (u+ρ)).Nonempty := by
    obtain ⟨x,hx,hxD⟩ := (dense_of_mem_residual hres).inter_open_nonempty
      (Ioo u (u+ρ)) isOpen_Ioo (nonempty_Ioo.mpr (by linarith))
    exact ⟨x,hxD,hx⟩
  obtain ⟨xp,⟨hxpD,hxpF⟩,hxplo,hxphi⟩ := hright
  refine ⟨xm-u,xp-u,by linarith,by linarith,by linarith,by linarith,?_,?_,?_⟩
  · simpa using hxmD
  · simpa using hxpD
  · simpa [ne_comm] using hxpF

theorem exists_endpoint_bands (F : ℝ → Oracle)
    (hfiber : ∀ B, {x | F x = B}.Countable) (D : Set ℝ) (hD : D ∈ residual ℝ)
    (hcont : ContinuousOn F D) (t u ρ : ℝ) (hρ : 0 < ρ)
    (hshift : ∀ s ∈ rationalSpan t, u+s ∈ D) :
    ∃ (lo hi : ℝ) (j : ℕ) (δ : ℚ),
      -ρ < lo ∧ lo < 0 ∧ 0 < hi ∧ hi < ρ ∧
      0 < δ ∧ (δ : ℝ) < ρ ∧ 3*(δ : ℝ) < hi-lo ∧
      (∀ s ∈ rationalSpan t, s ∈ Icc lo (lo+(δ : ℝ)) → F (u+s) j ≠ F (u+hi) j) ∧
      (∀ s ∈ rationalSpan t, s ∈ Icc (hi-(δ : ℝ)) hi → F (u+s) j = F (u+hi) j) := by
  obtain ⟨lo,hi,hloρ,hlo,hhi,hhiρ,hloD,hhiD,hne⟩ :=
    exists_separating_endpoints F hfiber D hD u ρ hρ
  have hbit : ∃ j : ℕ, F (u+lo) j ≠ F (u+hi) j := by
    by_contra h
    apply hne
    funext j
    exact not_ne_iff.mp (fun hj => h ⟨j,hj⟩)
  obtain ⟨j,hj⟩ := hbit
  have hc : ContinuousOn (fun x => F x j) D := (continuous_apply j).comp_continuousOn hcont
  obtain ⟨εl,hεl,hlconst⟩ := locally_constant_on_restriction (fun x => F x j) D hc (u+lo) hloD
  obtain ⟨εr,hεr,hrconst⟩ := locally_constant_on_restriction (fun x => F x j) D hc (u+hi) hhiD
  let b : ℝ := min ρ (min εl (min εr ((hi-lo)/3)))
  have hb : 0 < b := lt_min hρ (lt_min hεl (lt_min hεr (by linarith)))
  obtain ⟨δ,hδ0,hδb⟩ := exists_rat_btwn hb
  have hδρ : (δ : ℝ) < ρ := hδb.trans_le (min_le_left _ _)
  have hδl : (δ : ℝ) < εl := hδb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : (δ : ℝ) < εr := hδb.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδgap : (δ : ℝ) < (hi-lo)/3 := hδb.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨lo,hi,j,δ,hloρ,hlo,hhi,hhiρ,by exact_mod_cast hδ0,hδρ,by linarith,?_,?_⟩
  · intro s hs hband
    have hdist : dist (u+s) (u+lo) < εl := by
      rw [Real.dist_eq]
      have heq : u+s-(u+lo) = s-lo := by ring
      rw [heq, abs_of_nonneg (sub_nonneg.mpr hband.1)]
      linarith [hband.2]
    rw [hlconst _ (hshift s hs) hdist]
    exact hj
  · intro s hs hband
    have hdist : dist (u+s) (u+hi) < εr := by
      rw [Real.dist_eq]
      have heq : u+s-(u+hi) = s-hi := by ring
      rw [heq, abs_of_nonpos (sub_nonpos.mpr hband.2)]
      linarith [hband.1]
    exact hrconst _ (hshift s hs) hdist

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RecoverySetup
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem recovery_data_exists (F : ℝ → Oracle) (hF : Measurable F)
    (hfiber : ∀ B, {x | F x = B}.Countable)
    (hadd : ∀ x y, Reduces (F (x+y)) (join (F x) (F y))) (t : ℝ) :
    ∃ G : Set (ℝ × ℝ), G ∈ residual (ℝ × ℝ) ∧
      ∀ p ∈ G, Nonempty (RecoveryData F t p.1 p.2) := by
  obtain ⟨D,hD,hFD⟩ := measurable_continuousOn_residual F hF
  obtain ⟨e,E,hE,he,hspec⟩ := addition_program_continuous_restriction F hF hadd
  refine ⟨goodPairs t D E,goodPairs_residual t D E hD hE,?_⟩
  rintro ⟨u,v⟩ hgood
  obtain ⟨p,q,ρ,hρ,hρ1,hp,hq⟩ := fixed_local_programs F t u v D E e he hgood hspec
  obtain ⟨lo,hi,j,δ,hloρ,hlo,hhi,hhiρ,hδ,hδρ,hgap,hleft,hright⟩ :=
    exists_endpoint_bands F hfiber D hD hFD t u ρ hρ (fun s hs => (hgood s hs).1)
  exact ⟨{
    radius := ρ, radius_pos := hρ, radius_lt_one := hρ1,
    lo := lo, hi := hi, lo_gt := hloρ, lo_neg := hlo, hi_pos := hhi, hi_lt := hhiρ,
    delta := δ, delta_pos := hδ, delta_lt := hδρ, delta_gap := hgap,
    bit := j, forward := p, backward := q,
    left := hleft, right := hright, forward_correct := hp, backward_correct := hq }⟩

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

theorem bounded (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    state d.test (d.delta : ℝ) t n ∈ Icc d.lo d.hi := by
  apply state_mem_Icc_on_span d.test d.delta t d.lo d.hi
    (by exact_mod_cast d.delta_pos) ht0 ht1 d.lo_neg.le d.hi_pos.le
  · intro s hs hb
    simp [test, d.left s hs hb]
  · intro s hs hb
    simp [test, d.right s hs hb]

theorem abs_state_lt (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    |state d.test (d.delta : ℝ) t n| < d.radius := by
  obtain ⟨hl,hu⟩ := d.bounded ht0 ht1 n
  exact abs_lt.mpr ⟨d.lo_gt.trans_le hl, hu.trans_lt d.hi_lt⟩

theorem frequency_bound (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1)
    (n : ℕ) (hn : 0 < n) :
    |t - (∑ k ∈ Finset.range n, branch d.test (d.delta : ℝ) t k) / (n : ℝ)| <
      1 / ((n : ℝ) * (d.delta : ℝ)) := by
  exact frequency_error d.test (d.delta : ℝ) t n
    (by exact_mod_cast d.delta_pos) hn ((d.abs_state_lt ht0 ht1 n).trans d.radius_lt_one)

end RecoveryData

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_Assembly
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem lift_of_representation (hrep : BorelRepresentation) (harith : CutArithmetic)
    (π : Degree ≃o Degree) :
    ∃ F : ℝ → Oracle, Measurable F ∧
      (∀ B, {x | F x = B}.Countable) ∧
      (∀ x, degree (F x) = π (realDegree x)) ∧
      (∀ x y, Reduces (F (x+y)) (join (F x) (F y))) := by
  obtain ⟨F₀, hmeas, hF₀⟩ := hrep π
  let F : ℝ → Oracle := fun x => F₀ (cut x)
  have hF : ∀ x, degree (F x) = π (realDegree x) := fun x => hF₀ (cut x)
  refine ⟨F, hmeas.comp cut_measurable, represented_real_map_countable_fibers π F hF, hF, ?_⟩
  intro x y
  change degree (F (x+y)) ≤ degree (F x) ⊔ degree (F y)
  rw [hF, hF, hF, ← π.map_sup]
  exact π.monotone (harith.add x y)

theorem fourTuple_bound (harith : CutArithmetic) (π : Degree ≃o Degree)
    (F : ℝ → Oracle) (hF : ∀ x, degree (F x) = π (realDegree x))
    (t u v : ℝ) (δ : ℚ) :
    degree (fourTuple F t u v δ) ≤ π (realDegree t ⊔ realDegree u ⊔ realDegree v) := by
  let b := realDegree t ⊔ realDegree u ⊔ realDegree v
  have ht : realDegree t ≤ b := le_trans le_sup_left le_sup_left
  have hu : realDegree u ≤ b := le_trans le_sup_right le_sup_left
  have hv : realDegree v ≤ b := le_sup_right
  have huv : realDegree (u-v) ≤ b := (harith.sub u v).trans (sup_le hu hv)
  have hvu : realDegree (v-u) ≤ b := (harith.sub v u).trans (sup_le hv hu)
  have hδt : realDegree ((δ : ℝ)*t) ≤ b := (harith.smul δ t).trans ht
  have ht1 : realDegree (t-1) ≤ realDegree t := by
    simpa [sub_eq_add_neg] using harith.translate t (-1)
  have hδt1 : realDegree ((δ : ℝ)*(t-1)) ≤ b :=
    (harith.smul δ (t-1)).trans (ht1.trans ht)
  have h3 : realDegree (v-u+(δ : ℝ)*t) ≤ b :=
    (harith.add _ _).trans (sup_le hvu hδt)
  have h4 : realDegree (v-u+(δ : ℝ)*(t-1)) ≤ b :=
    (harith.add _ _).trans (sup_le hvu hδt1)
  have hvalue : ∀ x : ℝ, realDegree x ≤ b → degree (F x) ≤ π b := by
    intro x hx
    rw [hF]
    exact π.monotone hx
  change ((degree (F u) ⊔ degree (F (u-v))) ⊔ degree (F (v-u+(δ : ℝ)*t))) ⊔
    degree (F (v-u+(δ : ℝ)*(t-1))) ≤ π b
  exact sup_le (sup_le (sup_le (hvalue _ hu) (hvalue _ huv)) (hvalue _ h3)) (hvalue _ h4)

theorem inverse_le_realDegree_of_obligations
    (hrep : BorelRepresentation) (harith : CutArithmetic)
    (hrec : FourValueRecovery) (havoid : CategoryAvoidance)
    (π : Degree ≃o Degree) (t : ℝ) (ht : Irrational t) (ht0 : 0 < t) (ht1 : t < 1) :
    π.symm (realDegree t) ≤ realDegree t := by
  obtain ⟨F, hmeas, hfiber, hF, hadd⟩ := lift_of_representation hrep harith π
  obtain ⟨G, hG, hrecovery⟩ := hrec F hmeas hfiber hadd t ht ht0 ht1
  have hgeneric : ∀ p ∈ G,
      π.symm (realDegree t) ≤ realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2 := by
    intro p hp
    obtain ⟨δ, _, _, hδ⟩ := hrecovery p hp
    have hle : realDegree t ≤ π (realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2) :=
      le_trans hδ (fourTuple_bound harith π F hF t p.1 p.2 δ)
    simpa using π.symm.monotone hle
  by_contra hnle
  obtain ⟨Y, hY⟩ := degree_surjective (π.symm (realDegree t))
  have hnred : ¬ Reduces Y (cut t) := by
    intro h
    apply hnle
    rw [← hY]
    exact h
  have hmeager := havoid (cut t) Y hnred
  have hp : ∃ p : ℝ × ℝ, p ∈ G ∧
      ¬ Reduces Y (join (join (cut t) (cut p.1)) (cut p.2)) :=
    (dense_of_mem_residual (inter_mem hG hmeager)).nonempty
  obtain ⟨p, hpG, hpnot⟩ := hp
  apply hpnot
  change degree Y ≤ realDegree t ⊔ realDegree p.1 ⊔ realDegree p.2
  rw [hY]
  exact hgeneric p hpG

theorem main_of_obligations (hrep : BorelRepresentation) (harith : CutArithmetic)
    (hcover : IrrationalDegreeCoverage) (hrec : FourValueRecovery)
    (havoid : CategoryAvoidance) : MainTheorem := by
  apply order_rigidity_of_inverse_le
  intro π a
  by_cases ha : a = ⊥
  · subst a
    simp
  · obtain ⟨t, ht, ht0, ht1, rfl⟩ := hcover a ha
    exact inverse_le_realDegree_of_obligations hrep harith hrec havoid π t ht ht0 ht1

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchRecovery
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

private theorem tuple_initial (d : RecoveryData F t u v) :
    BranchMachine.initial (oracleFunction (fourTuple F t u v d.delta)) = oracleFunction (F u) := by
  funext k
  change oracleFunction (fourTuple F t u v d.delta) (8*k) = _
  rw [show 8*k = 2*(2*(2*k)) by omega]
  simp [oracleFunction, fourTuple]

private theorem tuple_anchor (d : RecoveryData F t u v) :
    BranchMachine.anchor (oracleFunction (fourTuple F t u v d.delta)) = oracleFunction (F (u-v)) := by
  funext k
  change oracleFunction (fourTuple F t u v d.delta) (8*k+4) = _
  rw [show 8*k+4 = 2*(2*(2*k+1)) by omega]
  simp [oracleFunction, fourTuple]

private theorem tuple_increment (d : RecoveryData F t u v) (s : ℝ) :
    BranchMachine.increment (oracleFunction (fourTuple F t u v d.delta)) d.highBit
      (if F (u+s) d.bit then 1 else 0) =
    oracleFunction (F (v-u+(d.delta : ℝ)*(t-choiceBit d.test s))) := by
  funext k
  have h3 : oracleFunction (fourTuple F t u v d.delta) (4*k+2) =
      oracleFunction (F (v-u+(d.delta : ℝ)*t)) k := by
    rw [show 4*k+2 = 2*(2*k+1) by omega]
    simp [oracleFunction, fourTuple]
  have h4 : oracleFunction (fourTuple F t u v d.delta) (2*k+1) =
      oracleFunction (F (v-u+(d.delta : ℝ)*(t-1))) k := by
    simp [oracleFunction, fourTuple]
  cases hb : F (u+s) d.bit <;> cases hh : F (u+d.hi) d.bit <;>
    simp [BranchMachine.increment, highBit, choiceBit, test, hb, hh, h3, h4]

private theorem increment_span (d : RecoveryData F t u v) (s : ℝ) :
    (d.delta : ℝ)*(t-choiceBit d.test s) ∈ rationalSpan t := by
  cases hb : d.test s
  · exact ⟨0,d.delta,by simp [choiceBit,hb]⟩
  · refine ⟨-d.delta,d.delta,?_⟩
    simp only [choiceBit,hb,↓reduceIte,Rat.cast_neg]
    ring

private theorem increment_abs (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℝ) : |(d.delta : ℝ)*(t-choiceBit d.test s)| < d.radius := by
  have hd : (0 : ℝ) < d.delta := by exact_mod_cast d.delta_pos
  have hδ := d.delta_lt
  apply abs_lt.mpr
  cases hb : d.test s <;> simp only [choiceBit,hb,Bool.false_eq_true,↓reduceIte,sub_zero] <;>
    constructor <;> nlinarith

theorem stage_correct (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ n, BranchMachine.stage (codeEnumeration d.forward) (codeEnumeration d.backward)
      d.bit d.highBit (oracleFunction (fourTuple F t u v d.delta)) n =
        oracleFunction (F (u+state d.test (d.delta : ℝ) t n)) := by
  intro n
  induction n with
  | zero =>
    funext input
    simpa [BranchMachine.stage,state] using congrFun (tuple_initial d) input
  | succ n ih =>
    let s := state d.test (d.delta : ℝ) t n
    let a := (d.delta : ℝ)*(t-choiceBit d.test s)
    have hsa : s+a = state d.test (d.delta : ℝ) t (n+1) := rfl
    have hp := d.forward_correct s (state_mem_rationalSpan d.test d.delta t n)
      a (increment_span d s) (d.abs_state_lt ht0 ht1 n) (increment_abs d ht0 ht1 s)
    have hq := d.backward_correct (s+a) (by rw [hsa]; exact state_mem_rationalSpan _ _ _ _)
      (by rw [hsa]; exact d.abs_state_lt ht0 ht1 (n+1))
    funext k
    simp only [BranchMachine.stage,BranchMachine.step,ih,oracleFunction]
    change (Part.some _).bind _ = _
    rw [Part.bind_some]
    change OracleCode.eval
      (partialJoin (OracleCode.eval
        (partialJoin (oracleFunction (F (u+s)))
          (BranchMachine.increment (oracleFunction (fourTuple F t u v d.delta)) d.highBit
            (if F (u+s) d.bit then 1 else 0))) (codeEnumeration d.forward))
        (BranchMachine.anchor (oracleFunction (fourTuple F t u v d.delta))))
      (codeEnumeration d.backward) k = _
    rw [tuple_increment,tuple_anchor,partialJoin_oracle,hp]
    rw [show v+s+a = v+(s+a) by ring,partialJoin_oracle,hq]
    rfl

theorem stage_single_program (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ c : OracleCode, ∀ n k,
      OracleCode.eval (oracleFunction (fourTuple F t u v d.delta)) c (Nat.pair n k) =
        oracleFunction (F (u+state d.test (d.delta : ℝ) t n)) k := by
  let T := fourTuple F t u v d.delta
  let g : ℕ → ℕ := fun k => if T k then 1 else 0
  let f : ℕ → ℕ := fun z => if F (u+state d.test (d.delta : ℝ) t (Nat.unpair z).1)
      (Nat.unpair z).2 then 1 else 0
  have hg : (fun x => Part.some (g x)) = oracleFunction (fourTuple F t u v d.delta) := rfl
  have hf := UniformOracle.stage_recursive (codeEnumeration d.forward) (codeEnumeration d.backward)
    d.bit d.highBit g f (by
      intro n k
      rw [hg]
      have hs := congrFun (d.stage_correct ht0 ht1 n) k
      apply hs.trans
      simp only [f,Nat.unpair_pair]
      rfl)
  obtain ⟨c,hc⟩ := OracleCode.exists_code hf
  rw [hg] at hc
  refine ⟨c,fun n k => (congrFun hc (Nat.pair n k)).trans ?_⟩
  simp only [f,Nat.unpair_pair]
  rfl

theorem branch_reduces (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    Reduces d.branchOracle (fourTuple F t u v d.delta) := by
  obtain ⟨c,hc⟩ := d.stage_single_program ht0 ht1
  have he := OracleCode.eval_recursiveIn (oracleFunction (fourTuple F t u v d.delta)) c
  have hp := UniformOracle.total_primrec (O := {oracleFunction (fourTuple F t u v d.delta)})
    (Primrec₂.natPair.comp Primrec.id (Primrec.const d.bit))
  have hbits : Nat.RecursiveIn {oracleFunction (fourTuple F t u v d.delta)}
      (fun input => oracleFunction (F (u+state d.test (d.delta : ℝ) t input)) d.bit) :=
    (Nat.RecursiveIn.comp he hp).of_eq (fun n => by
    change (Part.some (Nat.pair n d.bit)).bind
      (fun input => OracleCode.eval (oracleFunction (fourTuple F t u v d.delta)) c input) = _
    rw [Part.bind_some,hc])
  have hcmp : Primrec (fun b : ℕ => if b = d.highBit then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const d.highBit))
      (Primrec.const 1) (Primrec.const 0)
  apply RecursiveIn.iff_nat.mpr
  apply (Nat.RecursiveIn.comp (UniformOracle.total_primrec hcmp) hbits).of_eq
  intro n
  simp only [oracleFunction]
  change (Part.some _).bind _ = _
  rw [Part.bind_some]
  cases hb : F (u+state d.test (d.delta : ℝ) t n) d.bit <;>
    cases hh : F (u+d.hi) d.bit <;>
    simp [branchOracle,test,highBit,hb,hh]

end RecoveryData
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchFrequency
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace UniformOracle

theorem runningSum_recursive {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n))) :
    Nat.RecursiveIn O (fun n => Part.some (runningSum f n)) := by
  have hy := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp (total_primrec (Primrec.nat_add.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hf hy))
  have hp := Nat.RecursiveIn.prec (total_primrec (Primrec.const 0)) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    change (Part.some (runningSum f n)).bind _ = _
    rw [Part.bind_some]
    rfl
end UniformOracle

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

theorem count_eq_sum (d : RecoveryData F t u v) (n : ℕ) :
    (d.count n : ℝ) = ∑ k ∈ Finset.range n, branch d.test (d.delta : ℝ) t k := by
  induction n with
  | zero => simp [count,UniformOracle.runningSum]
  | succ n ih =>
    simp only [count,UniformOracle.runningSum,Finset.sum_range_succ,Nat.cast_add]
    rw [show (UniformOracle.runningSum (fun n => if d.branchOracle n then 1 else 0) n : ℝ) =
      ∑ k ∈ Finset.range n, branch d.test (d.delta : ℝ) t k from ih]
    congr 1
    cases hb : d.branchOracle n <;> simp [branch,choiceBit,branchOracle] at hb ⊢ <;> simp [hb]

theorem count_recursive (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    Nat.RecursiveIn {oracleFunction (fourTuple F t u v d.delta)}
      (fun n => Part.some (d.count n)) := by
  exact UniformOracle.runningSum_recursive (RecursiveIn.iff_nat.mp (d.branch_reduces ht0 ht1))

theorem count_frequency_bound (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1)
    (n : ℕ) (hn : 0 < n) :
    |t - (d.count n : ℝ)/(n : ℝ)| < 1/((n : ℝ)*(d.delta : ℝ)) := by
  rw [count_eq_sum]
  exact d.frequency_bound ht0 ht1 n hn

end RecoveryData
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_SumComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RationalCoding

private theorem polynomial_primrec {p a b : ℕ → ℕ} (hp : Primrec p)
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun z : ℕ × ℕ × ℕ =>
      p z.1*denominator z.2.1*denominator z.2.2 +
      a z.2.1*denominator z.1*denominator z.2.2 +
      b z.2.2*denominator z.1*denominator z.2.1) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (hp.comp Primrec.fst)
      (denominator_primrec.comp (Primrec.fst.comp Primrec.snd)))
      (denominator_primrec.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (ha.comp (Primrec.fst.comp Primrec.snd))
      (denominator_primrec.comp Primrec.fst))
      (denominator_primrec.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (hb.comp (Primrec.snd.comp Primrec.snd))
      (denominator_primrec.comp Primrec.fst))
      (denominator_primrec.comp (Primrec.fst.comp Primrec.snd)))

theorem sumLeft_primrec : Primrec sumLeft :=
  polynomial_primrec positiveNumerator_primrec negativeNumerator_primrec negativeNumerator_primrec

theorem sumRight_primrec : Primrec sumRight :=
  polynomial_primrec negativeNumerator_primrec positiveNumerator_primrec positiveNumerator_primrec

theorem sum_difference (i j k : ℕ) :
    ((rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ)-(rationalEnumeration i : ℝ))*
      ((denominator i : ℝ)*denominator j*denominator k) =
        (sumRight (i,j,k) : ℝ)-(sumLeft (i,j,k) : ℝ) := by
  have hi : (denominator i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos i))
  have hj : (denominator j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos j))
  have hk : (denominator k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos k))
  rw [signed_query_value,signed_query_value,signed_query_value]
  simp only [sumLeft,sumRight,Nat.cast_add,Nat.cast_mul]
  field_simp
  ring

theorem lt_sum_iff (i j k : ℕ) :
    sumLeft (i,j,k) < sumRight (i,j,k) ↔
      (rationalEnumeration i : ℝ) < (rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ) := by
  have hd : (0 : ℝ) < (denominator i : ℝ)*denominator j*denominator k := by
    exact mul_pos (mul_pos (by exact_mod_cast denominator_pos i)
      (by exact_mod_cast denominator_pos j)) (by exact_mod_cast denominator_pos k)
  constructor
  · intro h
    have hh : (sumLeft (i,j,k) : ℝ) < (sumRight (i,j,k) : ℝ) := by exact_mod_cast h
    have hp : 0 < ((rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ)-(rationalEnumeration i : ℝ))*
        ((denominator i : ℝ)*denominator j*denominator k) := by
      rw [sum_difference]; exact sub_pos.mpr hh
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hd).mp hp)
  · intro h
    have hh := mul_pos (sub_pos.mpr h) hd
    rw [sum_difference] at hh
    exact_mod_cast sub_pos.mp hh

theorem sum_lt_iff (i j k : ℕ) :
    sumRight (i,j,k) < sumLeft (i,j,k) ↔
      (rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ) < (rationalEnumeration i : ℝ) := by
  have hd : (0 : ℝ) < (denominator i : ℝ)*denominator j*denominator k := by
    exact mul_pos (mul_pos (by exact_mod_cast denominator_pos i)
      (by exact_mod_cast denominator_pos j)) (by exact_mod_cast denominator_pos k)
  constructor
  · intro h
    have hh : (sumRight (i,j,k) : ℝ) < (sumLeft (i,j,k) : ℝ) := by exact_mod_cast h
    have hp : ((rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ)-(rationalEnumeration i : ℝ))*
        ((denominator i : ℝ)*denominator j*denominator k) < 0 := by
      rw [sum_difference]; exact sub_neg.mpr hh
    have hh' : (rationalEnumeration j : ℝ)+(rationalEnumeration k : ℝ)-(rationalEnumeration i : ℝ)<0 := by
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hn) hd.le)) hp
    exact sub_neg.mp hh'
  · intro h
    have hh := mul_neg_of_neg_of_pos (sub_neg.mpr h) hd
    rw [sum_difference] at hh
    exact_mod_cast sub_neg.mp hh

end TuringRigidity.RationalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_CutAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace CutAddition
open RationalCoding UniformOracle

theorem decision_primrec : Primrec decision := by
  let hargs := Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
    (α := ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  let hfirst := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    (α := ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  let hsecond := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    (α := ℕ × (ℕ × ℕ) × (ℕ × ℕ))
  exact Primrec.ite ((Primrec.eq.comp hfirst (Primrec.const 1)).and
    ((Primrec.eq.comp hsecond (Primrec.const 1)).and
      (Primrec.nat_lt.comp (sumLeft_primrec.comp hargs) (sumRight_primrec.comp hargs))))
    (Primrec.const (some 1))
    (Primrec.ite ((Primrec.eq.comp hfirst (Primrec.const 0)).and
      ((Primrec.eq.comp hsecond (Primrec.const 0)).and
        (Primrec.nat_lt.comp (sumRight_primrec.comp hargs) (sumLeft_primrec.comp hargs))))
      (Primrec.const (some 0)) (Primrec.const none))

theorem trial_recursive (x y : ℝ) :
    Nat.RecursiveIn {oracleFunction (join (cut x) (cut y))}
      (fun z => Part.some (Encodable.encode (trial x y (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction (join (cut x) (cut y))}
  have hq := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hi := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hj := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hg : Nat.RecursiveIn O (oracleFunction (join (cut x) (cut y))) := .oracle _ (Set.mem_singleton _)
  have hbi := _root_.OAI.TuringRigidity.UniformOracle.total_comp hg (_root_.OAI.TuringRigidity.UniformOracle.total_comp
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)) hi)
  have hbj := _root_.OAI.TuringRigidity.UniformOracle.total_comp hg (_root_.OAI.TuringRigidity.UniformOracle.total_comp
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1))) hj)
  have hdec : Primrec (fun z : ℕ => Encodable.encode (decision
      ((Nat.unpair z).1,Nat.unpair (Nat.unpair (Nat.unpair z).2).1,
        Nat.unpair (Nat.unpair (Nat.unpair z).2).2))) :=
    Primrec.encode.comp (decision_primrec.comp
      ((Primrec.fst.comp Primrec.unpair).pair
        ((Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).pair
          (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hdec)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair hq (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_pair hi hj) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hbi hbj)))).of_eq
      (fun z => by simp [trial])

private theorem bit_one (b : Bool) (h : (if b then (1 : ℕ) else 0)=1) : b=true := by
  cases b <;> simp_all
private theorem bit_zero (b : Bool) (h : (if b then (1 : ℕ) else 0)=0) : b=false := by
  cases b <;> simp_all

theorem trial_sound (x y : ℝ) (n m r : ℕ) (hr : r ∈ trial x y n m) :
    r = if cut (x+y) n then 1 else 0 := by
  let i := (Nat.unpair m).1
  let j := (Nat.unpair m).2
  change r ∈ decision (n,(i,j),(if cut x i then 1 else 0,if cut y j then 1 else 0)) at hr
  generalize hbi : (if cut x i then (1 : ℕ) else 0) = bi at hr
  generalize hbj : (if cut y j then (1 : ℕ) else 0) = bj at hr
  unfold decision at hr
  split at hr
  · rename_i h
    have hr' : r=1 := by symm; simpa using hr
    subst r
    have hx := (cut_eq_true x i).mp (bit_one _ (hbi.trans h.1))
    have hy := (cut_eq_true y j).mp (bit_one _ (hbj.trans h.2.1))
    have hq := (lt_sum_iff n i j).mp h.2.2
    have hc : cut (x+y) n=true := (cut_eq_true _ _).mpr (by linarith)
    simp [hc]
  · split at hr
    · rename_i h
      have hr' : r=0 := by symm; simpa using hr
      subst r
      have hx : x ≤ (rationalEnumeration i : ℝ) := le_of_not_gt
        (fun hx => Bool.noConfusion ((bit_zero _ (hbi.trans h.1)).symm.trans ((cut_eq_true x i).mpr hx)))
      have hy : y ≤ (rationalEnumeration j : ℝ) := le_of_not_gt
        (fun hy => Bool.noConfusion ((bit_zero _ (hbj.trans h.2.1)).symm.trans ((cut_eq_true y j).mpr hy)))
      have hq := (sum_lt_iff n i j).mp h.2.2
      have hnot : ¬(rationalEnumeration n : ℝ)<x+y := by linarith
      have hc : cut (x+y) n=false := Bool.eq_false_iff.mpr
        (fun hc => hnot ((cut_eq_true _ _).mp hc))
      simp [hc]
    · simp at hr

theorem trial_complete (x y : ℝ) (hxy : Irrational (x+y)) (n : ℕ) :
    ∃ m r, r ∈ trial x y n m := by
  have hne : (rationalEnumeration n : ℝ) ≠ x+y := fun h => hxy ⟨rationalEnumeration n,h⟩
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨a,ha,hax⟩ := exists_rat_btwn (show (rationalEnumeration n : ℝ)-y<x by linarith)
    obtain ⟨b,hb,hby⟩ := exists_rat_btwn (show (rationalEnumeration n : ℝ)-(a : ℝ)<y by linarith)
    obtain ⟨i,hi⟩ := rationalEnumeration_surjective a
    obtain ⟨j,hj⟩ := rationalEnumeration_surjective b
    have hci : cut x i=true := (cut_eq_true x i).mpr (by simpa only [hi] using hax)
    have hcj : cut y j=true := (cut_eq_true y j).mpr (by simpa only [hj] using hby)
    have hl : sumLeft (n,i,j) < sumRight (n,i,j) := (lt_sum_iff n i j).mpr (by rw [hi,hj]; linarith)
    exact ⟨Nat.pair i j,1,by simp [trial,decision,hci,hcj,hl]⟩
  · obtain ⟨a,hxa,ha⟩ := exists_rat_btwn (show x<(rationalEnumeration n : ℝ)-y by linarith)
    obtain ⟨b,hyb,hb⟩ := exists_rat_btwn (show y<(rationalEnumeration n : ℝ)-(a : ℝ) by linarith)
    obtain ⟨i,hi⟩ := rationalEnumeration_surjective a
    obtain ⟨j,hj⟩ := rationalEnumeration_surjective b
    have hci : cut x i=false := Bool.eq_false_iff.mpr (fun hc => by
      have hh := (cut_eq_true x i).mp hc
      rw [hi] at hh
      linarith)
    have hcj : cut y j=false := Bool.eq_false_iff.mpr (fun hc => by
      have hh := (cut_eq_true y j).mp hc
      rw [hj] at hh
      linarith)
    have hu : sumRight (n,i,j) < sumLeft (n,i,j) := (sum_lt_iff n i j).mpr (by rw [hi,hj]; linarith)
    exact ⟨Nat.pair i j,0,by simp [trial,decision,hci,hcj,hu]⟩

theorem irrational_add_reduces (x y : ℝ) (hxy : Irrational (x+y)) :
    Reduces (cut (x+y)) (join (cut x) (cut y)) := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (trial_recursive x y) (fun n => if cut (x+y) n then 1 else 0)
    (trial_sound x y) (trial_complete x y hxy)
end CutAddition

theorem cut_add_reduces (x y : ℝ) : Reduces (cut (x+y)) (join (cut x) (cut y)) := by
  by_cases hxy : Irrational (x+y)
  · exact CutAddition.irrational_add_reduces x y hxy
  · obtain ⟨q,hq⟩ := not_not.mp hxy
    rw [←hq]
    exact rational_cut_reduces q _

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ScalarCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace RationalCoding

private theorem scalarPolynomial_primrec (a b D : ℕ) {p q c : ℕ → ℕ}
    (hp : Primrec p) (hq : Primrec q) (hc : Primrec c) :
    Primrec (fun z : ℕ × ℕ => (a*p z.2+b*q z.2)*denominator z.1+c z.1*D*denominator z.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const a) (hp.comp Primrec.snd))
        (Primrec.nat_mul.comp (Primrec.const b) (hq.comp Primrec.snd)))
      (denominator_primrec.comp Primrec.fst))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (hc.comp Primrec.fst) (Primrec.const D))
      (denominator_primrec.comp Primrec.snd))

theorem scalarLeft_primrec (r : ℕ) : Primrec (scalarLeft r) :=
  scalarPolynomial_primrec _ _ _ positiveNumerator_primrec negativeNumerator_primrec negativeNumerator_primrec

theorem scalarRight_primrec (r : ℕ) : Primrec (scalarRight r) :=
  scalarPolynomial_primrec _ _ _ negativeNumerator_primrec positiveNumerator_primrec positiveNumerator_primrec

theorem scalar_eq_iff (r i j : ℕ) : scalarLeft r (i,j)=scalarRight r (i,j) ↔
    (rationalEnumeration r : ℝ)*(rationalEnumeration j : ℝ)=(rationalEnumeration i : ℝ) := by
  have hr : (denominator r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos r))
  have hi : (denominator i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos i))
  have hj : (denominator j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (denominator_pos j))
  rw [signed_query_value,signed_query_value,signed_query_value]
  have he : ((positiveNumerator r : ℝ)-negativeNumerator r)/denominator r *
      (((positiveNumerator j : ℝ)-negativeNumerator j)/denominator j) =
      ((positiveNumerator i : ℝ)-negativeNumerator i)/denominator i ↔
      (scalarLeft r (i,j) : ℝ)=(scalarRight r (i,j) : ℝ) := by
    simp only [scalarLeft,scalarRight,Nat.cast_add,Nat.cast_mul]
    field_simp
    constructor <;> intro h <;> nlinarith
  rw [he]
  exact Nat.cast_inj.symm

theorem divideIndex_value (r : ℚ) (i : ℕ) :
    rationalEnumeration (divideIndex r i) = rationalEnumeration i/r := by
  simp only [divideIndex,rationalEnumeration,Encodable.encodek,Option.getD_some]

theorem divideIndex_recursive {O : Set (ℕ →. ℕ)} (r : ℚ) (hr : r ≠ 0) :
    Nat.RecursiveIn O (fun i => Part.some (divideIndex r i)) := by
  let ridx := Encodable.encode r
  let E : ℕ → ℕ → Option ℕ := fun i j =>
    if valid j ∧ scalarLeft ridx (i,j)=scalarRight ridx (i,j) then some j else none
  have hE : Primrec (fun z : ℕ => Encodable.encode (E (Nat.unpair z).1 (Nat.unpair z).2)) :=
    Primrec.encode.comp ((Primrec.ite ((valid_primrec.comp Primrec.snd).and
      (Primrec.eq.comp (scalarLeft_primrec ridx) (scalarRight_primrec ridx)))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).comp Primrec.unpair)
  have hridx : rationalEnumeration ridx = r := by simp [ridx,rationalEnumeration]
  apply UniformOracle.total_search (UniformOracle.total_primrec hE) (divideIndex r)
  · intro i j a ha
    dsimp only [E] at ha
    split at ha
    · rename_i h
      have haj : a=j := by symm; simpa using ha
      subst a
      have he := (scalar_eq_iff ridx i j).mp h.2
      rw [hridx] at he
      have heq : r*rationalEnumeration j=rationalEnumeration i := by exact_mod_cast he
      have hval : rationalEnumeration j=rationalEnumeration i/r :=
        (eq_div_iff hr).mpr (by simpa [mul_comm] using heq)
      have hj : canonicalCode j=j := ite_eq_left h.1
      rw [canonicalCode_eq,hval] at hj
      exact hj.symm
    · simp at ha
  · intro i
    let j := divideIndex r i
    have hv : valid j := (valid_iff j).mpr ⟨rationalEnumeration i/r,rfl⟩
    have he : scalarLeft ridx (i,j)=scalarRight ridx (i,j) := by
      apply (scalar_eq_iff ridx i j).mpr
      rw [hridx,show rationalEnumeration j=rationalEnumeration i/r from divideIndex_value r i]
      push_cast
      field_simp
    exact ⟨j,j,by simp [E,hv,he]⟩

end RationalCoding
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_CutArithmetic
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open RationalCoding UniformOracle

theorem cut_smul_reduces (r : ℚ) (x : ℝ) : Reduces (cut ((r : ℝ)*x)) (cut x) := by
  by_cases hr : r=0
  · subst r
    simpa using rational_cut_reduces (0 : ℚ) (cut x)
  by_cases ht : Irrational ((r : ℝ)*x)
  swap
  · obtain ⟨q,hq⟩ := not_not.mp ht
    rw [←hq]
    exact rational_cut_reduces q _
  have hq : Nat.RecursiveIn {oracleFunction (cut x)} (oracleFunction (cut x)) :=
    .oracle _ (Set.mem_singleton _)
  have hread := Nat.RecursiveIn.comp hq (divideIndex_recursive (O := {oracleFunction (cut x)}) r hr)
  apply RecursiveIn.iff_nat.mpr
  by_cases hpos : 0 < r
  · have hpos' : (0 : ℝ) < r := by exact_mod_cast hpos
    apply hread.of_eq
    intro n
    change (Part.some (divideIndex r n)).bind
      (fun input => Part.some (if cut x input then 1 else 0)) =
      oracleFunction (cut ((r : ℝ)*x)) n
    rw [Part.bind_some]
    have hiff : cut x (divideIndex r n)=true ↔ cut ((r : ℝ)*x) n=true := by
      rw [cut_eq_true,cut_eq_true,divideIndex_value,Rat.cast_div]
      simpa only [mul_comm] using (div_lt_iff₀ hpos' :
        (rationalEnumeration n : ℝ)/(r : ℝ)<x ↔ (rationalEnumeration n : ℝ)<x*(r : ℝ))
    have heq : cut x (divideIndex r n)=cut ((r : ℝ)*x) n := Bool.eq_iff_iff.mpr hiff
    simp only [oracleFunction,heq]
  · have hneg : r<0 := (lt_or_gt_of_ne hr).resolve_right hpos
    have hneg' : (r : ℝ)<0 := by exact_mod_cast hneg
    have hc : Primrec (fun b : ℕ => if b=0 then 1 else 0) :=
      Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0)
    apply (Nat.RecursiveIn.comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hc) hread).of_eq
    intro n
    change ((Part.some (divideIndex r n)).bind
      (fun input => Part.some (if cut x input then 1 else 0))).bind
      (fun value => Part.some (if value = 0 then 1 else 0)) =
      oracleFunction (cut ((r : ℝ)*x)) n
    simp only [Part.bind_some]
    have hiff : cut x (divideIndex r n)=true ↔ (r : ℝ)*x<(rationalEnumeration n : ℝ) := by
      rw [cut_eq_true,divideIndex_value,Rat.cast_div]
      simpa only [mul_comm] using (div_lt_iff_of_neg hneg' :
        (rationalEnumeration n : ℝ)/(r : ℝ)<x ↔ x*(r : ℝ)<(rationalEnumeration n : ℝ))
    have hneq : (rationalEnumeration n : ℝ) ≠ (r : ℝ)*x :=
      fun h => ht ⟨rationalEnumeration n,h⟩
    by_cases hin : cut x (divideIndex r n)=true
    · have hout : cut ((r : ℝ)*x) n=false := Bool.eq_false_iff.mpr
        (fun h => (not_lt_of_gt (hiff.mp hin)) ((cut_eq_true _ _).mp h))
      simp [hin,hout,oracleFunction]
    · have hle : (rationalEnumeration n : ℝ) ≤ (r : ℝ)*x :=
        le_of_not_gt (fun h => hin (hiff.mpr h))
      have hout : cut ((r : ℝ)*x) n=true := (cut_eq_true _ _).mpr
        ((lt_or_eq_of_le hle).resolve_right hneq)
      have hin' := Bool.eq_false_iff.mpr hin
      simp [hin',hout,oracleFunction]

theorem cut_sub_reduces (x y : ℝ) : Reduces (cut (x-y)) (join (cut x) (cut y)) := by
  have hy : Reduces (cut (-y)) (cut y) := by simpa using cut_smul_reduces (-1 : ℚ) y
  have h := reduces_trans (cut_add_reduces x (-y)) (join_mono (reduces_refl (cut x)) hy)
  simpa only [sub_eq_add_neg] using h

theorem cut_translate_reduces (x : ℝ) (q : ℚ) : Reduces (cut (x+(q : ℝ))) (cut x) :=
  reduces_trans (cut_add_reduces x q)
    (join_reduces (reduces_refl (cut x)) (rational_cut_reduces q (cut x)))

theorem cut_arithmetic : CutArithmetic where
  add := cut_add_reduces
  sub := cut_sub_reduces
  smul := cut_smul_reduces
  translate := cut_translate_reduces

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteTranscript
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleCode

theorem eval_finite_use (g : ℕ → ℕ) (c : OracleCode) (n a : ℕ)
    (ha : a ∈ eval (fun k => Part.some (g k)) c n) :
    ∃ m, a ∈ eval (BranchMachine.lookup (UniformOracle.oraclePrefix g m)) c n := by
  obtain ⟨m,hm⟩ := (eval_approximates (UniformOracle.prefix_approximates g) c n).2 a ha
  exact ⟨m,hm m le_rfl⟩

theorem eval_prefix_stable (g : ℕ → ℕ) (h : ℕ →. ℕ) (m : ℕ)
    (he : ∀ k, k < m → g k ∈ h k) (c : OracleCode) (n a : ℕ)
    (ha : a ∈ eval (BranchMachine.lookup (UniformOracle.oraclePrefix g m)) c n) :
    a ∈ eval h c n := by
  apply eval_mono (c := c) (n := n) (a := a) ?_ ha
  intro k b hb
  change b ∈ ((UniformOracle.oraclePrefix g m)[k]? : Part ℕ) at hb
  have hk : k < m := by
    by_contra hn
    have hnone : (UniformOracle.oraclePrefix g m)[k]? = none :=
      List.getElem?_eq_none (by simpa [UniformOracle.oraclePrefix] using Nat.le_of_not_gt hn)
    simp [hnone] at hb
  have hv : (UniformOracle.oraclePrefix g m)[k]? = some (g k) := by
    simp [UniformOracle.oraclePrefix, List.getElem?_range hk]
  have heq : b = g k := by simpa [hv] using hb
  subst b
  exact he k hk

theorem eval_total_stable (g : ℕ → ℕ) (c : OracleCode) (n a : ℕ)
    (ha : a ∈ eval (fun k => Part.some (g k)) c n) :
    ∃ m, ∀ h : ℕ → ℕ, (∀ k, k < m → h k = g k) →
      a ∈ eval (fun k => Part.some (h k)) c n := by
  obtain ⟨m,hm⟩ := eval_finite_use g c n a ha
  exact ⟨m,fun h hh => eval_prefix_stable g _ m
    (fun k hk => Part.mem_some_iff.mpr (hh k hk).symm) c n a hm⟩

end TuringRigidity.OracleCode

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_CutTranscript
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

theorem cut_prefix_left (x : ℝ) (m : ℕ) :
    ∃ l : ℝ, l < x ∧ ∀ y, l < y → y ≤ x → ∀ k, k < m → cut y k = cut x k := by
  induction m with
  | zero => exact ⟨x-1, by linarith, by simp⟩
  | succ m ih =>
    obtain ⟨l,hl,he⟩ := ih
    by_cases hq : (rationalEnumeration m : ℝ) < x
    · refine ⟨max l (rationalEnumeration m), max_lt hl hq, ?_⟩
      intro y hy hyx k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact he y ((le_max_left _ _).trans_lt hy) hyx k hk
      · subst k
        have hqy := (le_max_right l (rationalEnumeration m : ℝ)).trans_lt hy
        simp [cut, hq, hqy]
    · refine ⟨l,hl,?_⟩
      intro y hy hyx k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact he y hy hyx k hk
      · subst k
        have hqy : ¬ (rationalEnumeration m : ℝ) < y :=
          not_lt.mpr (hyx.trans (not_lt.mp hq))
        simp [cut,hq,hqy]

namespace CategorySearch

theorem value_prefix (A : Oracle) (p q : ℝ × ℝ) (m : ℕ)
    (h1 : ∀ k, k < m → cut q.1 k = cut p.1 k)
    (h2 : ∀ k, k < m → cut q.2 k = cut p.2 k) :
    ∀ k, k < m → value A q k = value A p k := by
  intro k hk
  apply congrArg (fun b : Bool => if b then (1 : ℕ) else 0)
  have hk2 : k/2 < m := by omega
  have hk4 : k/2/2 < m := by omega
  simp only [pairOracle,join,h1 _ hk4,h2 _ hk2]

theorem halting_left (A : Oracle) (c : OracleCode) (p : ℝ × ℝ) (n a : ℕ)
    (ha : a ∈ OracleCode.eval (oracleFunction (pairOracle A p)) c n) :
    ∃ l : ℝ × ℝ, l.1 < p.1 ∧ l.2 < p.2 ∧
      ∀ q : ℝ × ℝ, l.1 < q.1 → q.1 ≤ p.1 → l.2 < q.2 → q.2 ≤ p.2 →
        a ∈ OracleCode.eval (oracleFunction (pairOracle A q)) c n := by
  obtain ⟨m,hm⟩ := OracleCode.eval_total_stable (value A p) c n a ha
  obtain ⟨l1,h1,he1⟩ := cut_prefix_left p.1 m
  obtain ⟨l2,h2,he2⟩ := cut_prefix_left p.2 m
  refine ⟨(l1,l2),h1,h2,?_⟩
  intro q hq1 hq1' hq2 hq2'
  exact hm (value A q) (value_prefix A p q m (he1 _ hq1 hq1') (he2 _ hq2 hq2'))

theorem dense_sound (A Y : Oracle) (c : OracleCode) (l r : ℚ × ℚ)
    (hd : rectangle l r ⊆ closure (success A Y c)) (p : ℝ × ℝ)
    (hp : p ∈ rectangle l r) (n a : ℕ)
    (ha : a ∈ OracleCode.eval (oracleFunction (pairOracle A p)) c n) :
    a = if Y n then 1 else 0 := by
  obtain ⟨b,hb1,hb2,he⟩ := halting_left A c p n a ha
  let U : Set (ℝ × ℝ) := Ioo (max b.1 (l.1 : ℝ)) p.1 ×ˢ Ioo (max b.2 (l.2 : ℝ)) p.2
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hne : U.Nonempty :=
    (nonempty_Ioo.mpr (max_lt hb1 hp.1.1)).prod (nonempty_Ioo.mpr (max_lt hb2 hp.2.1))
  have hsub : U ⊆ rectangle l r := by
    intro q hq
    exact ⟨⟨(le_max_right _ _).trans_lt hq.1.1,hq.1.2.trans hp.1.2⟩,
      ⟨(le_max_right _ _).trans_lt hq.2.1,hq.2.2.trans hp.2.2⟩⟩
  obtain ⟨q,hq⟩ := hne
  obtain ⟨z,hzU,hzS⟩ := mem_closure_iff.mp (hd (hsub hq)) U hU hq
  have hz := he z ((le_max_left _ _).trans_lt hzU.1.1) hzU.1.2.le
    ((le_max_left _ _).trans_lt hzU.2.1) hzU.2.2.le
  rw [hzS] at hz
  exact Part.mem_some_iff.mp hz

theorem rational_halting (A : Oracle) (c : OracleCode) (l r : ℚ × ℚ)
    (p : ℝ × ℝ) (hp : p ∈ rectangle l r) (n a : ℕ)
    (ha : a ∈ OracleCode.eval (oracleFunction (pairOracle A p)) c n) :
    ∃ q : ℚ × ℚ, ((q.1 : ℝ),(q.2 : ℝ)) ∈ rectangle l r ∧
      a ∈ OracleCode.eval (oracleFunction (pairOracle A ((q.1 : ℝ),(q.2 : ℝ)))) c n := by
  obtain ⟨b,hb1,hb2,he⟩ := halting_left A c p n a ha
  obtain ⟨u,hu1,hu2⟩ := exists_rat_btwn (max_lt hb1 hp.1.1)
  obtain ⟨v,hv1,hv2⟩ := exists_rat_btwn (max_lt hb2 hp.2.1)
  exact ⟨(u,v),⟨⟨(le_max_right _ _).trans_lt hu1,hu2.trans hp.1.2⟩,
    ⟨(le_max_right _ _).trans_lt hv1,hv2.trans hp.2.2⟩⟩,
    he _ ((le_max_left _ _).trans_lt hu1) hu2.le ((le_max_left _ _).trans_lt hv1) hv2.le⟩

end CategorySearch
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_DegreeCoverage
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace BinarySeries

theorem irrational_of_noncomputable (B : Oracle) (h : ¬ Reduces B (fun _ => false)) :
    Irrational (value B) := by
  intro ⟨q,hq⟩
  apply h
  have hr := set_reduces_cut B (mixed_of_noncomputable B h)
  rw [←hq] at hr
  exact reduces_trans hr (rational_cut_reduces q _)

theorem noncomputable_series (B : Oracle) (h : ¬ Reduces B (fun _ => false)) :
    Irrational (value B) ∧ 0 < value B ∧ value B < 1 ∧
      Reduces (cut (value B)) B ∧ Reduces B (cut (value B)) := by
  have hm := mixed_of_noncomputable B h
  have hi := irrational_of_noncomputable B h
  refine ⟨hi,positive B ?_,lt_one B ?_,cut_reduces B hi,set_reduces_cut B hm⟩
  · obtain ⟨n,_,hn⟩ := (hm 0).1
    exact ⟨n,hn⟩
  · obtain ⟨n,_,hn⟩ := (hm 0).2
    exact ⟨n,hn⟩
end BinarySeries

theorem irrational_degree_coverage : IrrationalDegreeCoverage := by
  intro a ha
  obtain ⟨B,rfl⟩ := degree_surjective a
  have hn : ¬ Reduces B (fun _ => false) := by
    intro h
    exact ha (le_antisymm h bot_le)
  obtain ⟨hi,h0,h1,hforward,hback⟩ := BinarySeries.noncomputable_series B hn
  exact ⟨BinarySeries.value B,hi,h0,h1,(degree_eq_iff _ _).mpr ⟨hforward,hback⟩⟩

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_EffectiveRecovery
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace EffectiveRecovery
open RationalCoding

theorem window_primrec (A B : ℕ) : Primrec (window A B) := by
  let Q := Primrec.fst.comp (Primrec.fst.comp Primrec.snd) (α := Bool × (ℕ × ℕ) × (ℕ × ℕ))
  let D := Primrec.snd.comp (Primrec.fst.comp Primrec.snd) (α := Bool × (ℕ × ℕ) × (ℕ × ℕ))
  let N := Primrec.fst.comp (Primrec.snd.comp Primrec.snd) (α := Bool × (ℕ × ℕ) × (ℕ × ℕ))
  let S := Primrec.snd.comp (Primrec.snd.comp Primrec.snd) (α := Bool × (ℕ × ℕ) × (ℕ × ℕ))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) (Primrec.const (some 1))
    (Primrec.ite (Primrec.nat_lt.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp Q N) (Primrec.const A))
        (Primrec.nat_mul.comp D (Primrec.const B)))
      (Primrec.nat_mul.comp (Primrec.nat_mul.comp D S) (Primrec.const A)))
      (Primrec.const (some 1))
      (Primrec.ite (Primrec.nat_lt.comp
        (Primrec.nat_mul.comp D (Primrec.nat_add.comp
          (Primrec.nat_mul.comp S (Primrec.const A)) (Primrec.const B)))
        (Primrec.nat_mul.comp (Primrec.nat_mul.comp Q N) (Primrec.const A)))
        (Primrec.const (some 0)) (Primrec.const none)))

theorem lower_iff (Q D N S A B : ℕ) (hD : 0 < D) (hN : 0 < N) (hA : 0 < A) :
    (Q : ℝ)/D < (S : ℝ)/N - (B : ℝ)/(N*A) ↔ Q*N*A+D*B < D*S*A := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hden : (0 : ℝ) < D*N*A := mul_pos (mul_pos hd hn) ha
  have he : ((S : ℝ)/N - (B : ℝ)/(N*A) - (Q : ℝ)/D) * (D*N*A) =
      (D : ℝ)*S*A - ((Q : ℝ)*N*A+D*B) := by
    field_simp
    ring
  constructor
  · intro h
    have hp := mul_pos (sub_pos.mpr h) hden
    rw [he] at hp
    exact_mod_cast sub_pos.mp hp
  · intro h
    have hr : (Q : ℝ)*N*A+D*B < (D : ℝ)*S*A := by exact_mod_cast h
    have hp : 0 < ((S : ℝ)/N - (B : ℝ)/(N*A) - (Q : ℝ)/D) * (D*N*A) := by
      rw [he]; linarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hp)

theorem upper_iff (Q D N S A B : ℕ) (hD : 0 < D) (hN : 0 < N) (hA : 0 < A) :
    (S : ℝ)/N + (B : ℝ)/(N*A) < (Q : ℝ)/D ↔ D*(S*A+B) < Q*N*A := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hden : (0 : ℝ) < D*N*A := mul_pos (mul_pos hd hn) ha
  have he : ((Q : ℝ)/D - ((S : ℝ)/N + (B : ℝ)/(N*A))) * (D*N*A) =
      (Q : ℝ)*N*A - (D : ℝ)*(S*A+B) := by
    field_simp
  constructor
  · intro h
    have hp := mul_pos (sub_pos.mpr h) hden
    rw [he] at hp
    exact_mod_cast sub_pos.mp hp
  · intro h
    have hr : (D : ℝ)*(S*A+B) < (Q : ℝ)*N*A := by exact_mod_cast h
    have hp : 0 < ((Q : ℝ)/D - ((S : ℝ)/N + (B : ℝ)/(N*A))) * (D*N*A) := by
      rw [he]; linarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hden).mp hp)
end EffectiveRecovery

namespace RecoveryData
open RationalCoding EffectiveRecovery
variable {F : ℝ → Oracle} {t u v : ℝ}

theorem delta_numerator_pos (d : RecoveryData F t u v) : 0 < d.delta.num.natAbs := by
  have hn : 0 < d.delta.num := Rat.num_pos.mpr d.delta_pos
  have he : (d.delta.num.natAbs : ℤ) = d.delta.num := by
    rw [Int.natCast_natAbs,abs_of_pos hn]
  rw [←he] at hn
  exact_mod_cast hn

theorem delta_fraction (d : RecoveryData F t u v) :
    (d.delta : ℝ) = (d.delta.num.natAbs : ℝ)/(d.delta.den : ℝ) := by
  have hn : 0 < d.delta.num := Rat.num_pos.mpr d.delta_pos
  have he : (d.delta.num.natAbs : ℤ) = d.delta.num := by
    rw [Int.natCast_natAbs,abs_of_pos hn]
  have he' : (d.delta.num.natAbs : ℝ) = (d.delta.num : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) he
  rw [Rat.cast_def,he']

theorem radius_fraction (d : RecoveryData F t u v) (N : ℕ) (hN : 0 < N) :
    1/((N : ℝ)*(d.delta : ℝ)) = (d.delta.den : ℝ)/((N : ℝ)*d.delta.num.natAbs) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : (0 : ℝ) < d.delta.num.natAbs := by exact_mod_cast d.delta_numerator_pos
  have hb : (0 : ℝ) < d.delta.den := by exact_mod_cast d.delta.den_pos
  rw [d.delta_fraction]
  field_simp

theorem cutTrial_recursive (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    Nat.RecursiveIn {oracleFunction (fourTuple F t u v d.delta)}
      (fun z => Part.some (Encodable.encode (d.cutTrial (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction (fourTuple F t u v d.delta)}
  have hq := UniformOracle.total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hN := UniformOracle.total_primrec (O := O) (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
  have hS := UniformOracle.total_comp (d.count_recursive ht0 ht1) hN
  have hwindow : Primrec (fun z : ℕ => Encodable.encode
      (window d.delta.num.natAbs d.delta.den
        (negative (Nat.unpair z).1,
          (numeratorMagnitude (Nat.unpair z).1,denominator (Nat.unpair z).1),
          ((Nat.unpair (Nat.unpair z).2).1,(Nat.unpair (Nat.unpair z).2).2)))) :=
    Primrec.encode.comp ((window_primrec _ _).comp
      ((negative_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair
        (((numeratorMagnitude_primrec.comp (Primrec.fst.comp Primrec.unpair)).pair
          (denominator_primrec.comp (Primrec.fst.comp Primrec.unpair))).pair
            (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
  exact (UniformOracle.total_comp (UniformOracle.total_primrec hwindow)
    (UniformOracle.total_pair hq (UniformOracle.total_pair hN hS))).of_eq
      (fun z => by simp [cutTrial])

theorem cutTrial_sound (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1)
    (i m r : ℕ) (hr : r ∈ d.cutTrial i m) : r = if cut t i then 1 else 0 := by
  have hn : 0 < m+1 := Nat.succ_pos m
  have he := d.count_frequency_bound ht0 ht1 (m+1) hn
  rw [d.radius_fraction (m+1) hn] at he
  unfold cutTrial window at hr
  split at hr
  · rename_i hneg
    have hr' : r=1 := by symm; simpa using hr
    subst r
    have hq : (rationalEnumeration i : ℝ) ≤ 0 := by
      rw [query_value,ite_eq_left hneg]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hc : cut t i = true := (cut_eq_true t i).mpr (hq.trans_lt ht0)
    simp [hc]
  · rename_i hneg
    have hq : (rationalEnumeration i : ℝ) = (numeratorMagnitude i : ℝ)/(denominator i : ℝ) := by
      rw [query_value,ite_eq_right hneg]
    split at hr
    · rename_i hl
      have hr' : r=1 := by symm; simpa using hr
      subst r
      have hl' := (lower_iff (numeratorMagnitude i) (denominator i) (m+1) (d.count (m+1))
        d.delta.num.natAbs d.delta.den (denominator_pos i) hn d.delta_numerator_pos).mpr hl
      rw [←hq] at hl'
      have hh := (abs_lt.mp he).1
      have hc : cut t i = true := (cut_eq_true t i).mpr (by linarith)
      simp [hc]
    · split at hr
      · rename_i hu
        have hr' : r=0 := by symm; simpa using hr
        subst r
        have hu' := (upper_iff (numeratorMagnitude i) (denominator i) (m+1) (d.count (m+1))
          d.delta.num.natAbs d.delta.den (denominator_pos i) hn d.delta_numerator_pos).mpr hu
        rw [←hq] at hu'
        have hh := (abs_lt.mp he).2
        have htq : t < (rationalEnumeration i : ℝ) := by linarith
        have hc : cut t i = false := Bool.eq_false_iff.mpr
          (fun h => (not_lt_of_gt htq) ((cut_eq_true t i).mp h))
        simp [hc]
      · simp at hr

theorem cutTrial_complete (d : RecoveryData F t u v) (ht : Irrational t)
    (ht0 : 0 < t) (ht1 : t < 1) (i : ℕ) : ∃ m r, r ∈ d.cutTrial i m := by
  by_cases hneg : negative i = true
  · exact ⟨0,1,by simp [cutTrial,window,hneg]⟩
  · have hq : (rationalEnumeration i : ℝ) = (numeratorMagnitude i : ℝ)/(denominator i : ℝ) := by
      rw [query_value,ite_eq_right hneg]
    have hne : (rationalEnumeration i : ℝ) ≠ t := fun h => ht ⟨rationalEnumeration i,h⟩
    obtain ⟨⟨N,hN,hs⟩,_⟩ := comparison_search t (d.delta : ℝ)
      (fun n => (d.count n : ℝ)/(n : ℝ)) (by exact_mod_cast d.delta_pos)
      (fun n hn => d.count_frequency_bound ht0 ht1 n hn) (rationalEnumeration i) hne
    rw [d.radius_fraction N hN,hq] at hs
    have hm : N-1+1=N := by omega
    rcases hs with hl | hu
    · have hl' := (lower_iff (numeratorMagnitude i) (denominator i) N (d.count N)
        d.delta.num.natAbs d.delta.den (denominator_pos i) hN d.delta_numerator_pos).mp hl
      exact ⟨N-1,1,by simp [cutTrial,hm,window,hneg,hl']⟩
    · have hu' := (upper_iff (numeratorMagnitude i) (denominator i) N (d.count N)
        d.delta.num.natAbs d.delta.den (denominator_pos i) hN d.delta_numerator_pos).mp hu
      by_cases hl' : numeratorMagnitude i*N*d.delta.num.natAbs+denominator i*d.delta.den <
          denominator i*d.count N*d.delta.num.natAbs
      · exact ⟨N-1,1,by simp [cutTrial,hm,window,hneg,hl']⟩
      · exact ⟨N-1,0,by simp [cutTrial,hm,window,hneg,hl',hu']⟩

theorem cut_reduces (d : RecoveryData F t u v) (ht : Irrational t)
    (ht0 : 0 < t) (ht1 : t < 1) : Reduces (cut t) (fourTuple F t u v d.delta) := by
  apply RecursiveIn.iff_nat.mpr
  exact UniformOracle.total_search (d.cutTrial_recursive ht0 ht1)
    (fun i => if cut t i then 1 else 0) (d.cutTrial_sound ht0 ht1)
      (d.cutTrial_complete ht ht0 ht1)

end RecoveryData

theorem four_value_recovery : FourValueRecovery := by
  intro F hF hfiber hadd t ht ht0 ht1
  obtain ⟨G,hG,hdata⟩ := recovery_data_exists F hF hfiber hadd t
  refine ⟨G,hG,?_⟩
  intro p hp
  obtain ⟨d⟩ := hdata p hp
  refine ⟨d.delta,d.delta_pos,?_,d.cut_reduces ht ht0 ht1⟩
  exact_mod_cast d.delta_lt.trans d.radius_lt_one

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CategoryMachine
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CategorySearch
open Computable Encodable

theorem rationalBit_primrec : Primrec₂ rationalBit :=
  Primrec.ite (RationalCoding.ltCode_primrec.comp Primrec.snd Primrec.fst)
    (Primrec.const 1) (Primrec.const 0)

theorem rationalBit_eq (i k : ℕ) :
    Part.some (rationalBit i k) = oracleFunction (cut (rationalEnumeration i : ℝ)) k := by
  simp only [rationalBit,oracleFunction,cut_eq_true,RationalCoding.ltCode_iff]

theorem partialJoin_oracle (A B : Oracle) :
    partialJoin (oracleFunction A) (oracleFunction B) = oracleFunction (join A B) := by
  funext k
  cases h : k.bodd <;> simp [partialJoin,oracleFunction,join,h]

theorem finiteOracle_approximates (A : Oracle) (i j k : ℕ) :
    Approximates (oracleFunction (pairOracle A (sample i j)) k)
      (fun m => finiteOracle (UniformOracle.oraclePrefix (Avalue A) m) i j k) := by
  have hi : (fun k => Part.some (rationalBit i k)) = oracleFunction (cut (rationalEnumeration i : ℝ)) :=
    funext (rationalBit_eq i)
  have hj : (fun k => Part.some (rationalBit j k)) = oracleFunction (cut (rationalEnumeration j : ℝ)) :=
    funext (rationalBit_eq j)
  have h := BranchMachine.partialJoin_approximates
    (fun k => BranchMachine.partialJoin_approximates
      (UniformOracle.prefix_approximates (Avalue A))
      (fun k => Approximates.const (Part.some (rationalBit i k))) k)
    (fun k => Approximates.const (Part.some (rationalBit j k))) k
  simpa only [finiteOracle,hi,hj,show (fun k => Part.some (Avalue A k)) = oracleFunction A from rfl,
    partialJoin_oracle,pairOracle,sample] using h

theorem inside_primrec (l r : ℚ × ℚ) : PrimrecRel (inside l r) :=
  (RationalCoding.ltCode_primrec.comp (Primrec.const (encode l.1)) Primrec.fst).and
    ((RationalCoding.ltCode_primrec.comp Primrec.fst (Primrec.const (encode r.1))).and
      ((RationalCoding.ltCode_primrec.comp (Primrec.const (encode l.2)) Primrec.snd).and
        (RationalCoding.ltCode_primrec.comp Primrec.snd (Primrec.const (encode r.2)))))

theorem inside_iff (l r : ℚ × ℚ) (i j : ℕ) :
    inside l r i j ↔ sample i j ∈ rectangle l r := by
  simp [inside,RationalCoding.ltCode_iff,rationalEnumeration,sample,rectangle,and_assoc]

theorem finiteRun_partrec (c : OracleCode) (l r : ℚ × ℚ) : Partrec₂ (finiteRun c l r) := by
  let α := List ℕ × ℕ × ℕ
  have hA : Partrec₂ (fun z : α => BranchMachine.lookup z.1) :=
    BranchMachine.lookup_partrec.comp (fst.comp fst) snd
  have hi : Partrec₂ (fun z : α => fun k => Part.some (rationalBit z.2.1 k)) :=
    (rationalBit_primrec.to_comp.comp (fst.comp (snd.comp fst)) snd)
  have hj : Partrec₂ (fun z : α => fun k => Part.some (rationalBit z.2.2 k)) :=
    (rationalBit_primrec.to_comp.comp (snd.comp (snd.comp fst)) snd)
  have hg : Partrec₂ (fun z : α => finiteOracle z.1 z.2.1 z.2.2) :=
    BranchMachine.partialJoin_partrec (BranchMachine.partialJoin_partrec hA hi) hj
  have he : Partrec₂ (fun z : α => OracleCode.eval (finiteOracle z.1 z.2.1 z.2.2) c) :=
    OracleCode.eval_partrec hg c
  have hi' : Computable (fun z : List ℕ × ℕ => (Nat.unpair z.2).1) :=
    fst.comp (Computable.unpair.comp snd)
  have hj' : Computable (fun z : List ℕ × ℕ => (Nat.unpair (Nat.unpair z.2).2).1) :=
    fst.comp (Computable.unpair.comp (snd.comp (Computable.unpair.comp snd)))
  have hn' : Computable (fun z : List ℕ × ℕ => (Nat.unpair (Nat.unpair z.2).2).2) :=
    snd.comp (Computable.unpair.comp (snd.comp (Computable.unpair.comp snd)))
  have hb : Computable (fun z : List ℕ × ℕ => decide (inside l r (Nat.unpair z.2).1
      (Nat.unpair (Nat.unpair z.2).2).1)) :=
    (inside_primrec l r).decide.to_comp.comp hi' hj'
  have hparam : Computable (fun z : List ℕ × ℕ =>
      (z.1,(Nat.unpair z.2).1,(Nat.unpair (Nat.unpair z.2).2).1)) :=
    fst.pair (hi'.pair hj')
  have hr := he.comp hparam hn'
  exact (partrec_cond hb hr Partrec.none).of_eq (fun z => by simp [finiteRun])

theorem finiteRun_code (c : OracleCode) (l r : ℚ × ℚ) :
    ∃ d : Nat.Partrec.Code, ∀ L w,
      d.eval (Nat.pair (encode L) w) = finiteRun c l r L w := by
  obtain ⟨d,hd⟩ := partrec_code (finiteRun_partrec c l r)
  exact ⟨d,fun L w => hd (L,w)⟩

end TuringRigidity.CategorySearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CategoryReduction
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CategorySearch
open Encodable Set

theorem trialInput_primrec : Primrec trialInput := by
  have hn := Primrec.fst.comp Primrec.unpair
  have hs := Primrec.snd.comp Primrec.unpair
  have hi := Primrec.fst.comp (Primrec.unpair.comp hs)
  have hj := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hs)))
  have ht := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hs)))
  exact Primrec₂.natPair.comp (Primrec₂.natPair.comp hi (Primrec₂.natPair.comp hj hn)) ht

theorem searchTrial_recursive (A : Oracle) (d : Nat.Partrec.Code) :
    Nat.RecursiveIn {oracleFunction A}
      (fun z => Part.some (encode (searchTrial A d (Nat.unpair z).1 (Nat.unpair z).2))) := by
  have h := UniformOracle.total_comp (UniformOracle.trial_recursive (Avalue A) d)
    (UniformOracle.total_primrec trialInput_primrec)
  have hO : (fun n => Part.some (Avalue A n)) = oracleFunction A := rfl
  rw [hO] at h
  exact h.of_eq (fun z => by simp only [searchTrial,Nat.pair_unpair])

theorem searchTrial_pair (A : Oracle) (d : Nat.Partrec.Code) (n i j m k : ℕ) :
    searchTrial A d n (Nat.pair i (Nat.pair j (Nat.pair m k))) =
      d.evaln k (Nat.pair (encode (UniformOracle.oraclePrefix (Avalue A) m))
        (Nat.pair i (Nat.pair j n))) := by
  simp [searchTrial,trialInput,UniformOracle.trial]

theorem reduces_of_dense (A Y : Oracle) (c : OracleCode) (l r : ℚ × ℚ)
    (hne : (rectangle l r).Nonempty)
    (hd : rectangle l r ⊆ closure (success A Y c)) : Reduces Y A := by
  obtain ⟨d,hdcode⟩ := finiteRun_code c l r
  apply RecursiveIn.iff_nat.mpr
  apply UniformOracle.total_search (searchTrial_recursive A d) (Avalue Y)
  · intro n s a ha
    have hs := Nat.pair_unpair s
    generalize hi : (Nat.unpair s).1 = i at *
    generalize ht : (Nat.unpair s).2 = t at *
    subst s
    have ht := Nat.pair_unpair t
    generalize hj : (Nat.unpair t).1 = j at *
    generalize hu : (Nat.unpair t).2 = u at *
    subst t
    have hu := Nat.pair_unpair u
    generalize hm : (Nat.unpair u).1 = m at *
    generalize hk : (Nat.unpair u).2 = k at *
    subst u
    rw [searchTrial_pair] at ha
    have hrun := Nat.Partrec.Code.evaln_sound ha
    rw [hdcode] at hrun
    simp only [finiteRun,Nat.unpair_pair] at hrun
    split at hrun
    next hin =>
      exact dense_sound A Y c l r hd (sample i j) ((inside_iff l r i j).mp hin) n a
        ((OracleCode.eval_approximates (finiteOracle_approximates A i j) c n).1 m a hrun)
    next => simp at hrun
  · intro n
    obtain ⟨p,hp⟩ := hne
    obtain ⟨z,hzR,hzS⟩ := mem_closure_iff.mp (hd hp) (rectangle l r)
      (isOpen_Ioo.prod isOpen_Ioo) hp
    have hz : Avalue Y n ∈ OracleCode.eval (oracleFunction (pairOracle A z)) c n := by
      rw [hzS]
      exact Part.mem_some _
    obtain ⟨q,hqR,hq⟩ := rational_halting A c l r z hzR n (Avalue Y n) hz
    let i := encode q.1
    let j := encode q.2
    have hs : sample i j = ((q.1 : ℝ),(q.2 : ℝ)) := by simp [sample,i,j,rationalEnumeration]
    have hin : inside l r i j := (inside_iff l r i j).mpr (hs.symm ▸ hqR)
    rw [← hs] at hq
    obtain ⟨m,hm⟩ := (OracleCode.eval_approximates (finiteOracle_approximates A i j) c n).2
      (Avalue Y n) hq
    have hf : Avalue Y n ∈ d.eval (Nat.pair (encode (UniformOracle.oraclePrefix (Avalue A) m))
        (Nat.pair i (Nat.pair j n))) := by
      rw [hdcode]
      simpa [finiteRun,hin] using hm m le_rfl
    obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp hf
    exact ⟨Nat.pair i (Nat.pair j (Nat.pair m k)), Avalue Y n,by rwa [searchTrial_pair]⟩

end TuringRigidity.CategorySearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CategoryAvoidance
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Topology
namespace TuringRigidity.CategorySearch

theorem rational_rectangle_basis (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (p : ℝ × ℝ) (hp : p ∈ U) :
    ∃ l r : ℚ × ℚ, p ∈ rectangle l r ∧ rectangle l r ⊆ U := by
  obtain ⟨u,hu,v,hv,huv⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hp)
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
  obtain ⟨c,d,hcd,hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp hv
  obtain ⟨l1,hl1,hl1'⟩ := exists_rat_btwn hab.1
  obtain ⟨r1,hr1,hr1'⟩ := exists_rat_btwn hab.2
  obtain ⟨l2,hl2,hl2'⟩ := exists_rat_btwn hcd.1
  obtain ⟨r2,hr2,hr2'⟩ := exists_rat_btwn hcd.2
  refine ⟨(l1,l2),(r1,r2),⟨⟨hl1',hr1⟩,⟨hl2',hr2⟩⟩,?_⟩
  intro q hq
  exact huv ⟨hsub ⟨hl1.trans hq.1.1,hq.1.2.trans hr1'⟩,
    hsub' ⟨hl2.trans hq.2.1,hq.2.2.trans hr2'⟩⟩

theorem success_nowhereDense (A Y : Oracle) (hY : ¬ Reduces Y A) (c : OracleCode) :
    IsNowhereDense (success A Y c) := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨l,r,hpR,hR⟩ := rational_rectangle_basis _ isOpen_interior p hp
  exact hY (reduces_of_dense A Y c l r ⟨p,hpR⟩ (hR.trans interior_subset))

theorem category_avoidance : CategoryAvoidance := by
  intro A Y hY
  have heq : {p : ℝ × ℝ | Reduces Y (join (join A (cut p.1)) (cut p.2))} =
      ⋃ c : OracleCode, success A Y c := by
    ext p
    exact (OracleCode.turingReducible_iff_exists_code (oracleFunction Y)
      (oracleFunction (pairOracle A p))).trans (by simp [success])
  rw [heq]
  exact isMeagre_iUnion (fun c => (success_nowhereDense A Y hY c).isMeagre)

end TuringRigidity.CategorySearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem main_of_three_obligations (hrep : BorelRepresentation)
    (hcover : IrrationalDegreeCoverage) (havoid : CategoryAvoidance) : MainTheorem :=
  main_of_obligations hrep cut_arithmetic hcover four_value_recovery havoid

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CategoryMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem main_of_two_obligations (hrep : BorelRepresentation)
    (hcover : IrrationalDegreeCoverage) : MainTheorem :=
  main_of_three_obligations hrep hcover CategorySearch.category_avoidance

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CoverageMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem main_of_representation_oai (hrep : BorelRepresentation) : MainTheorem :=
  main_of_two_obligations hrep irrational_degree_coverage

end TuringRigidity

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.main_of_representation_oai := @OAI.TuringRigidity.main_of_representation_oai
