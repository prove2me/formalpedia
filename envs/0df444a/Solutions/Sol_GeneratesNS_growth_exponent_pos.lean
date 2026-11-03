-- Prove2me | solution 1 for GeneratesNS.growth_exponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:46:31.719494+00:00
-- url     : https://prove2.me/submissions/689d5858-b43e-4d2f-a975-45227d569c8c

import Mathlib
import Definitions.Def_OAIQ093D016

section
-- module Solutions.OAIQ093_PR.GrowthZero
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polynomial growth of the kernel, and growth exponent zero

`three_two_kernel_poly_growth`, and that a group of growth exponent zero is finite.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

open scoped RealInnerProductSpace

set_option synthInstance.maxHeartbeats 500000

set_option maxHeartbeats 1000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

/-- Degree-zero polynomial growth forces `G` to be finite: the balls `S ^ n` have bounded
cardinality, so some `S ^ y` already contains all of `Subgroup.closure S = ⊤`.

Extracted from the `zero` case of `main_gromov_theorem`, which now calls it. -/
lemma finite_of_growth_zero (h: HasPolynomialGrowthD S 0): Finite G := by
    simp [HasPolynomialGrowthD] at h
    obtain ⟨a, ha⟩ := h

    have S_closure := hGS.generates

    let pow_cards := Set.range (fun (n: ℕ) => #(S ^ n))
    -- TODO - this can probably be much simpler
    have pow_cards_bounded: ∃ y, ∀ n ∈ pow_cards, n ≤ y := by
      use a
      intro n hn
      simp [pow_cards] at hn
      obtain ⟨y, hy⟩ := hn
      rw [← hy]

      by_cases y_eq_zero: y = 0
      . simp [y_eq_zero]

        -- TODO - deduplicate this
        have a_ne_zero: a ≠ 0 := by
          by_contra!
          rw [this] at ha
          have hg_one := ha 1 (by omega)
          simp at hg_one
          have one_mem := hGS.one_mem
          rw [hg_one] at one_mem
          simp at one_mem

        omega
      . by_cases y_eq_one: y = 1
        .
          simp [y_eq_one]
          have card_mono := Finset.card_pow_mono (s := S) (m := 1) (n := 2) (by simp) (by simp)
          have card_two_le := ha 2 (by simp)
          simp at card_mono
          linarith
        .
          exact ha y (by omega)


    classical
    have max_card_mem := Nat.sSup_mem (s := pow_cards) ?_ ?_
    . simp [pow_cards] at max_card_mem
      obtain ⟨y, hy⟩ := max_card_mem


      have all_closure_mem: ∀ s ∈ (Subgroup.closure S), s ∈ (S ^ y) := by
        intro s hs
        induction hs using Subgroup.closure_induction with
        | one =>
          apply Finset.one_mem_pow
          exact Generates.one_mem
        | mem x hx =>
          by_cases y_eq_zero: y = 0
          .
            rw [y_eq_zero]
            rw [y_eq_zero] at hy
            simp at hy
            simp
            have y_eq := Nat.sSup_def (s := pow_cards) pow_cards_bounded
            have find_le := Nat.find_spec pow_cards_bounded
            rw [← y_eq] at find_le
            have S_one_le := find_le #(S) ?_
            .
              simp [pow_cards] at S_one_le
              rw [← hy] at S_one_le
              rw [Finset.card_le_one] at S_one_le
              have one_mem: 1 ∈ S := by exact Generates.one_mem
              have x_eq := S_one_le 1 one_mem x hx
              apply x_eq.symm
            . simp [pow_cards]
              use 1
              simp
          .
            have pow_mono := Finset.pow_subset_pow_right (s := S) (Generates.one_mem) (n := y) (m := 1) (by omega)
            simp at pow_mono
            apply pow_mono hx
        | mul a b a_mem_closure b_mem_closure a_mem_pow b_mem_pow =>
          by_cases y_eq_zero: y = 0
          .
            simp [y_eq_zero]
            simp [y_eq_zero] at a_mem_pow b_mem_pow
            simp [a_mem_pow, b_mem_pow]
          .
            by_contra!
            have a_b_mem_two: a * b ∈ (S ^ (y * 2)) := by
              have mem_mul := Finset.mul_mem_mul a_mem_pow b_mem_pow
              rw [← pow_two] at mem_mul
              rw [← pow_mul] at mem_mul
              exact mem_mul

            have subset := Finset.pow_subset_pow_right (s := S) (Generates.one_mem) (m := y) (n := (y * 2)) (by omega)

            have strict_subset : (S ^ y) ⊂ (S ^ (y * 2)) := by
              rw [Finset.ssubset_iff_of_subset subset]
              use (a * b)

            have card_lt: #(S ^ y) < #(S ^ (y * 2)) := by
              exact Finset.card_lt_card strict_subset


            rw [hy] at card_lt
            have y_eq := Nat.sSup_def (s := pow_cards) pow_cards_bounded
            have find_le := Nat.find_spec pow_cards_bounded
            rw [← y_eq] at find_le
            have reverse_le := find_le #(S ^ (y * 2)) ?_
            .
              simp [pow_cards] at reverse_le
              linarith
            . simp [pow_cards]
        | inv a ha a_mem_pow =>
          rw [← Finset.mem_inv']
          rw [← inv_pow]
          rw [← S_eq_Sinv]
          exact a_mem_pow

      have G_finite: Finite G := by
        rw [← Set.finite_univ_iff]
        have univ_eq: (Set.univ : Set G) = (S ^ y) := by
          simp at S_closure

          apply_fun (fun y => y.carrier) at S_closure
          conv at S_closure =>
            rhs
            equals Set.univ =>
              exact rfl

          rw [← S_closure]
          ext a
          refine ⟨?_, ?_⟩
          . intro ha
            simp at ha
            rw [← Finset.coe_pow]
            exact all_closure_mem a ha
          . intro ha
            simp
            exact mem_closure a

        rw [univ_eq]
        rw [← Finset.coe_pow]
        exact Finset.finite_toSet (S ^ y)
      exact G_finite
    .
      simp [pow_cards]
      apply Set.range_nonempty
    .
      rw [bddAbove_def]
      exact pow_cards_bounded

/-- The exponent in a polynomial growth bound is positive, since `G` is infinite. -/
lemma growth_exponent_pos_oai {d : ℕ} (h: HasPolynomialGrowthD S d): 0 < d := by
  by_contra!
  simp at this
  subst this
  have := finite_of_growth_zero h
  have := hGS.g_infinite
  exact (not_finite G)

-- TODO - add an explicit top-level universe parameter to avoid this 'omit hGS' hack

end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.growth_exponent_pos_oai.{u_1} := @GeneratesNS.growth_exponent_pos_oai.{u_1}
