-- Prove2me | solution 1 for GeneratesNS.three_two_S_n_generates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:04:55.050343+00:00
-- url     : https://prove2.me/submissions/f3fa5dcb-0ef4-4efd-9129-4914f60e4c89

import Mathlib
import Definitions.Def_OAIQ093D016
import Theorems.Thm_GeneratesNS_e_i_and_gamma_generates_G

section
-- module Solutions.OAIQ093_PR.Defs_WordMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The `Generates` class and the word metric

The `Generates` class packaging a finitely generated group with a symmetric generating set, the
definition of polynomial growth, and the word norm / word metric on `G` with its `MetricSpace`
@[expose]
instance.
-/


set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.whitespace false

open Subgroup
open scoped Finset
open scoped Pointwise
open scoped commutatorElement

namespace GeneratesNS
open Generates

variable [hGS: Generates]
include hGS

omit hGS in
lemma list_tail_unattach (T: Type*)  {p : T → Prop} (l: List { x : T // p x}): l.tail.unattach = l.unattach.tail := by
  unfold List.unattach
  simp

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_GroupTheory_Closure
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subgroup closures

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


open scoped Pointwise Finset

set_option maxHeartbeats 300000 in
lemma closure_iterate_mulact {T: Type*} [Group T] [DecidableEq T] (a b: T) (n: ℤ)
  (conj_in: (a^n * b * a^(-n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs))))
  (conj_inv_in: (a^(-n) * b * a^(n)) ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs)))) :
 (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) = (Subgroup.closure (G := T) (Set.range (fun (m : ℤ) => a^m * b * a^(-m)))) := by
  ext x
  refine ⟨?_, ?_⟩
  .
    intro hx
    apply Subgroup.closure_mono (h := (fun (m: ℤ) ↦ a ^ m * b * a ^ (-m)) '' Set.Ioo (-n.natAbs) n.natAbs)
    .
      intro y hy
      simp at hy
      simp
      obtain ⟨m, hm, y_eq⟩ := hy
      use m
    . exact hx
  .
    intro hx
    have closed_under_conj: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a * y * a⁻¹ ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: m < (n.natAbs : ℤ) - 1
        . apply Subgroup.subset_closure
          simp
          use (m + 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            . omega
            .
              apply_fun (fun (z: ℤ) => z + 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                exact m_lt_n_sub
              . exact StrictMono.add_const (fun ⦃a b⦄ a ↦ a) 1
          .
            rw [← mul_self_zpow]
            simp
            repeat rw [← mul_assoc]
        .
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (|n|) - 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← inv_zpow']
          rw [mul_assoc]
          rw [← zpow_add_one]
          simp
          simp at conj_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_inv_in
            exact conj_inv_in
      | one =>
        simp
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        simp at mul_mem
        simp
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem

    -- TODO - deduplicate this
    have closed_under_conj_inv: ∀ y ∈ (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )), a⁻¹ * y * a ∈  (Subgroup.closure (G := T) (Set.image (fun (m: ℤ) => a^m * b * a^(-m)) (Set.Ioo (-n.natAbs) n.natAbs) )) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        simp at hz
        obtain ⟨m, hm, z_eq⟩ := hz
        rw [← z_eq]
        by_cases m_lt_n_sub: (-n.natAbs : ℤ) < m - 1
        . apply Subgroup.subset_closure
          simp
          use (m - 1)
          refine ⟨?_, ?_⟩
          .
            refine ⟨?_, ?_⟩
            .
              simp at m_lt_n_sub
              omega

            .
              apply_fun (fun (z: ℤ) => z - 1) at m_lt_n_sub
              .
                simp at m_lt_n_sub
                omega
              . exact StrictMono.add_const (fun ⦃a b⦄ a ↦ a) (-1)
          .
            repeat rw [← mul_assoc]
            nth_rw 2 [← zpow_neg_one]
            rw [← zpow_add]
            rw [add_comm, ← sub_eq_add_neg]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← inv_zpow]
              rw [inv_zpow']
              rw [mul_zpow_self]
              rw [add_comm]
            simp
            rw [← inv_zpow]
            simp
            rw [sub_eq_add_neg]

        .
          simp at m_lt_n_sub
          have m_eq_n_minus: m = (-|n|) + 1 := by
            omega
          -- TODO - there must be an easier way to do this
          rw [m_eq_n_minus]
          repeat rw [← mul_assoc]
          rw [← mul_self_zpow]
          simp
          rw [← zpow_neg]
          rw [← zpow_neg_one]
          rw [mul_assoc]
          rw [mul_assoc]
          rw [mul_assoc]
          simp
          repeat rw [← mul_assoc]
          simp at conj_inv_in
          by_cases n_pos: 0 < n
          .
            have n_eq_abs: n = |n| := by
              exact Eq.symm (abs_of_pos n_pos)
            nth_rw 3 [← n_eq_abs]
            nth_rw 3 [← n_eq_abs]
            exact conj_inv_in
          .
            have n_eq_neg_abs: |n| = -n := by
              apply abs_of_nonpos
              omega
            simp at n_pos
            nth_rw 3 [n_eq_neg_abs]
            nth_rw 3 [n_eq_neg_abs]
            simp
            simp at conj_in
            exact conj_in
      | one =>
        simp
      | mul y z hy hz y_mem z_mem =>
        have mul_mem := Subgroup.mul_mem _ y_mem z_mem
        repeat rw [← mul_assoc] at mul_mem
        simp at mul_mem
        simp
        repeat rw [← mul_assoc]
        exact mul_mem
      | inv y hy y_mem =>
        rw [← Subgroup.inv_mem_iff]
        simp
        rw [← mul_assoc]
        simp at y_mem
        exact y_mem


    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp at hy
      obtain ⟨m, hm, y_eq⟩ := hy
      by_cases m_in_range: m ∈ Set.Ioo (-n.natAbs : ℤ) n.natAbs
      .
        apply Subgroup.subset_closure
        simp
        use m
        simp at m_in_range
        refine ⟨by omega, by simp⟩
      .
        simp only [Set.mem_Ioo] at m_in_range
        rw [not_and_or] at m_in_range
        simp at m_in_range
        by_cases m_pos: 0 < m
        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            rw [← m_eq_abs] at this
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              exact conj_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              simp at conj_inv_in
              rw [n_eq_neg_abs] at conj_inv_in
              simp at conj_inv_in
              rw [n_eq_neg_abs]
              simp
              exact conj_inv_in
          | succ p hsucc ih =>
            specialize closed_under_conj _ ih
            norm_cast
            rw [pow_succ']
            repeat rw [← mul_assoc] at closed_under_conj
            simp at closed_under_conj
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj

        .
          -- TODO - why is this needed?
          have exists_nat_abs: ∃ m_abs: ℕ, m = -m_abs := by
            use m.natAbs
            omega
          obtain ⟨m_abs, m_eq_abs⟩ := exists_nat_abs
          have abs_n_le: |n| ≤ m_abs := by
            by_contra!
            omega
          have nat_abs_n_le: n.natAbs ≤ m_abs := by
            rw [Int.abs_eq_natAbs] at abs_n_le
            omega
          rw [m_eq_abs]
          clear m_eq_abs
          clear abs_n_le
          induction m_abs, nat_abs_n_le using Nat.le_induction with
          | base =>
            simp at conj_in
            simp
            by_cases n_pos: 0 < n
            .
              have n_eq_abs: n = |n| := by
                exact Eq.symm (abs_of_pos n_pos)
              nth_rw 3 [← n_eq_abs]
              nth_rw 3 [← n_eq_abs]
              simp at conj_inv_in
              exact conj_inv_in
            .
              have n_eq_neg_abs: |n| = -n := by
                apply abs_of_nonpos
                omega
              rw [n_eq_neg_abs] at conj_in
              simp at conj_in
              rw [n_eq_neg_abs]
              simp
              exact conj_in
          | succ p hsucc ih =>
            specialize closed_under_conj_inv _ ih
            simp at ih
            norm_cast
            rw [zpow_negSucc]
            rw [pow_succ]
            repeat rw [← mul_assoc] at closed_under_conj_inv
            simp at closed_under_conj_inv
            simp
            repeat rw [← mul_assoc]
            exact closed_under_conj_inv


    | one => apply Subgroup.one_mem
    | mul y z hy hz y_mem z_mem =>
      apply Subgroup.mul_mem
      . exact y_mem
      . exact z_mem
    | inv y hy y_mem =>
      apply Subgroup.inv_mem _ y_mem
end

section
-- module Solutions.OAIQ093_PR.ThreeTwoGrowth
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Polynomial growth of the sets `S_n`

`new_three_two_poly_growth` and `three_poly_poly_growth_all_s_n`.
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

set_option maxHeartbeats 9000000

open MeasureTheory

open Additive

omit hGS in
lemma take_count_sum_eq_exp {T: Type*} [ht: Group T] [heq: DecidableEq T] {E: Set T} (l: List E) (g: T) (hg: g ≠ g⁻¹) (hl: ∀ val ∈ l, val = g ∨ val = g⁻¹): l.unattach.prod = g^(countElemOrInv l g) := by
  induction l with
  | nil =>
    simp [countElemOrInv]
  | cons h t ih =>
    simp [countElemOrInv]
    by_cases h_eq_g: h = g
    .
      simp [h_eq_g]
      rw [ih]
      . rw [← zpow_one_add]
      . simp at hl
        intro val hval
        have hl_right := hl.2 val (by simp) (by simp [hval])
        exact hl_right
    .
      have h_eq_inv: h = g⁻¹ := by
        specialize hl h
        simp at hl
        simp  [h_eq_g] at hl
        exact hl
      simp [h_eq_g, h_eq_inv]
      rw [ih]
      .
        rw [← zpow_neg_one]
        rw [← zpow_add]
        simp [hg.symm]
      .
        simp at hl
        intro val hval
        have hl_right := hl.2 val (by simp) (by simp [hval])
        exact hl_right

open Additive


omit hGS in
lemma list_filter_one {T: Type*} [DecidableEq T] [Group T] (l: List T): (l.filter (fun s => !decide (s = 1))).prod = l.prod := by
  induction l with
  | nil =>
    simp
  | cons h t ih =>
    simp
    by_cases h_eq_one: h = 1
    .
      simp [h_eq_one]
      exact ih
    .
      rw [List.filter_cons]
      simp [h_eq_one]
      exact ih


omit hGS in
lemma take_drop_len {T: Type*} {l: List T} {p: T → Bool}: (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  suffices h: l.takeWhile p ++ l.dropWhile p = l by
    nth_rw 3 [← h]
    rw [List.length_append]
  exact List.takeWhile_append_dropWhile

-- If G has polynomial growth, than we can find an N such that S_n ⊆ B_n * B_n⁻¹
set_option maxHeartbeats 2000000 in
lemma new_three_two_poly_growth (d: ℕ) (hG: HasPolynomialGrowthD S d ) (γ: G) (φ: (Additive G) →+ ℤ)  (s: G) (s_mem: s ∈ S): ∃ n, three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹)  := by
  by_contra!
  simp [HasPolynomialGrowthD] at hG
  have little_o_poly := isLittleO_pow_exp_pos_mul_atTop d (b := Real.log 2) (Real.log_pos (by simp))
  simp_rw [Real.exp_mul] at little_o_poly
  rw [Real.exp_log (by simp)] at little_o_poly
  apply Asymptotics.IsLittleO.eventuallyLE at little_o_poly
  apply Filter.Eventually.natCast_atTop at little_o_poly
  simp at little_o_poly

  -- Find an N' such that N^D < 2^N
  obtain ⟨N', hN⟩ := little_o_poly

  -- Write γ as a product of elements in S
  obtain ⟨gamma_list, gamma_list_prod⟩ := mem_S_prod_list γ
  simp [ProdS] at gamma_list_prod

  have gamma_list_inv: ((gamma_list.unattach).map (fun x => x⁻¹)).reverse.prod = γ⁻¹ := by
    rw [← List.prod_inv_reverse]
    rw [gamma_list_prod]

  have gamma_list_comm_inv: ((gamma_list.unattach).map (fun x => x⁻¹)) = (gamma_list.map (fun s => ⟨s.val⁻¹, hGS.has_inv s.val s.property⟩)).unattach := by
    clear gamma_list_prod gamma_list_inv
    induction gamma_list with
    | nil =>
      simp
    | cons a b ih =>
      simp
      exact ih

  rw [gamma_list_comm_inv] at gamma_list_inv


  -- Choose our N large enough that we can apply all of the above conditions
  let N := max N' (max gamma_list.length (max (φ (ofMul s)).natAbs 2))


  have disjoint_smul (M: ℕ) (hM: N ≤ M) (p: G) (p_mem: p ∈ three_two_S_n (S := {s}) φ γ (M + 1)) (p_not_prod: p ∉ three_two_B_n (S := {s}) φ γ M * (three_two_B_n (S := {s}) φ γ M)⁻¹): (p • three_two_B_n (S := {s}) φ γ M) ∩ (three_two_B_n (S := {s}) φ γ M) = ∅ := by
    rw [Finset.mem_mul.not] at p_not_prod
    push_neg at p_not_prod

    ext a
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro ha
    simp only [Finset.smul_finset_def, smul_eq_mul, Finset.mem_image] at ha
    obtain ⟨b, b_mem, s_b_eq⟩ := ha
    apply_fun (fun g => g * b⁻¹ ) at s_b_eq
    simp at s_b_eq
    apply Finset.inv_mem_inv at b_mem
    by_contra!
    specialize p_not_prod a this b⁻¹ b_mem
    rw [ne_comm] at p_not_prod
    contradiction


  have s_n_subset: ∀ M, N ≤ M → three_two_S_n (S := {s}) φ γ M ⊆ three_two_S_n (S := {s}) φ γ (M + 1) := by
    intro m hM a ha
    simp [three_two_S_n] at ha
    simp [three_two_S_n]
    obtain ⟨n, hn, s_n_eq⟩ := ha
    use n
    refine ⟨by omega, s_n_eq⟩

  have s_n_subset_all (x y: ℕ) (hxy: x ≤ y): three_two_S_n (S := {s}) φ γ x ⊆ three_two_S_n (S := {s}) φ γ (y) := by
    intro a ha
    simp [three_two_S_n] at ha
    simp [three_two_S_n]
    obtain ⟨n, hn, s_n_eq⟩ := ha
    use n
    refine ⟨by omega, s_n_eq⟩


  have b_n_subset_b_n_succ: ∀ M, N ≤ M → three_two_B_n (S := {s}) φ γ M ⊆ three_two_B_n (S := {s}) φ γ (M + 1) := by
    intro M hM a ha
    simp [three_two_B_n] at ha
    simp [three_two_B_n]
    obtain ⟨l, l_len, l_prod⟩ := ha
    simp [list_len_n]
    use l.map (fun s => ⟨s.val, by (
      exact s_n_subset M hM s.property
    )⟩)
    simp
    simp [list_len_n] at l_len
    refine ⟨by omega, ?_⟩
    conv =>
      lhs
      arg 1
      equals l.unattach =>
        simp [List.unattach, -List.map_subtype]
    exact l_prod

  have smul_subset (M: ℕ) (hM: N ≤ M) (p: G) (p_mem: p ∈ three_two_S_n (S := {s}) φ γ (M + 1)): p • three_two_B_n (S := {s}) φ γ M ⊆ three_two_B_n (S := {s}) φ γ (M + 1) := by
    intro a ha
    simp [three_two_B_n] at ha
    simp [three_two_B_n]
    simp only [Finset.smul_finset_def, smul_eq_mul, Finset.mem_image] at ha
    obtain ⟨list_prod, ⟨list, list_mem, list_prod_eq⟩, p_mul_eq⟩ := ha
    use (⟨p, p_mem⟩ :: (list.map (fun s => ⟨s.val, by (
      exact s_n_subset M hM s.property
    )⟩)))
    refine ⟨?_, ?_⟩
    .
      simp [list_len_n, list_mem]
      simp [list_len_n] at list_mem
      exact list_mem

    .
      simp
      conv =>
        lhs
        arg 2
        arg 1
        equals list.unattach =>
          simp [List.unattach, -List.map_subtype]
      rw [list_prod_eq, p_mul_eq]


  have s_n_bound: ∀ M: ℕ, N ≤ M → ∀ a ∈ three_two_S_n (S := {s}) φ γ M, ∃ l: List S, l.unattach.prod = a ∧ l.length ≤ 4*M^2 := by
    intro M hM a ha
    simp [three_two_S_n, gamma_m_helper, e_i_regular_helper] at ha
    obtain ⟨m, m_bound, s_m_eq⟩ := ha
    let gamma_inv_list: List S := (gamma_list.map (fun s => ⟨s.val⁻¹, hGS.has_inv s.val s.property⟩)).reverse

    -- Depending on whether these values are positive or negative, we either need to repeat γ or γ⁻¹ in the first list
    let m_list_choice := if 0 < m then gamma_list else gamma_inv_list
    let phi_list_choice := if 0 < (-φ (ofMul s)) then gamma_list else gamma_inv_list

    let m_list_choice_inv := if 0 < m then gamma_inv_list else gamma_list

    use (List.replicate m.natAbs m_list_choice).flatten ++ [⟨s, s_mem⟩] ++ (List.replicate (-(φ (ofMul s))).natAbs phi_list_choice).flatten ++ (List.replicate m.natAbs m_list_choice_inv).flatten
    refine ⟨?_, ?_⟩
    .
      simp [phi_list_choice]
      norm_cast
      rw [← s_m_eq]
      rw [← zpow_natCast]
      conv =>
        rhs
        arg 1
        arg 2
        -- TODO - is there a tactic that can normalize the 'ofMul' stuff for us?
        equals s * γ^(-(φ (ofMul s))) =>
          rw [← ofMul_zpow]
          rw [← sub_eq_add_neg]
          rw [← ofMul_div]
          rw [div_eq_mul_inv]
          rw [← inv_zpow]
          rw [inv_zpow']
          rfl


      simp
      simp_rw [m_list_choice, m_list_choice_inv]
      by_cases m_pos: 0 < m
      .
        simp_rw [m_pos]
        simp
        have m_eq_abs : |m| = m := by
          rw [Int.abs_eq_natAbs]
          omega
        rw [← zpow_natCast]
        simp [gamma_inv_list]
        rw [gamma_list_inv]
        rw [gamma_list_prod]
        rw [m_eq_abs]
        group
        by_cases phi_neg: (φ (ofMul s)) < 0
        .
          have phi_abs: |(φ (ofMul s))| = -φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_prod]
          rw [m_eq_abs]
          group
        .
          have phi_abs: |(φ (ofMul s))| = φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_inv]
          rw [m_eq_abs]
          group
      .
        simp_rw [m_pos]
        simp
        have neg_abs_m : |m| = - m := by
          rw [Int.abs_eq_natAbs]
          omega
        rw [← zpow_natCast]
        simp [gamma_inv_list]
        rw [gamma_list_inv]
        rw [gamma_list_prod]
        group
        rw [neg_abs_m]
        group
        -- TODO - this can be deduplicated
        by_cases phi_neg: (φ (ofMul s)) < 0
        .
          have phi_abs: |(φ (ofMul s))| = -φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_prod]
          rw [neg_abs_m]
          group
        .
          have phi_abs: |(φ (ofMul s))| = φ (ofMul s) := by
            rw [Int.abs_eq_natAbs]
            omega
          rw [phi_abs]
          simp_rw [phi_neg]
          simp
          rw [gamma_list_inv]
          rw [neg_abs_m]
          group
    .

      simp [m_list_choice, m_list_choice_inv]
      simp_rw [apply_ite]
      have m_natabs_le: m.natAbs ≤ M := by omega
      have gamma_list_len_le: gamma_list.length ≤ N := by omega
      have inv_list_len_eq: gamma_inv_list.length = gamma_list.length := by
        simp [gamma_inv_list]
      simp [inv_list_len_eq]
      have n_squared_pos: 1 ≤ N * N := by
        simp [N]
      have m_squared_pos: 1 ≤ M * M := by
        nlinarith
      have phi_choice_len: phi_list_choice.length = gamma_list.length := by
        simp [phi_list_choice]
        simp_rw [apply_ite]
        simp [inv_list_len_eq]
      rw [phi_choice_len]
      have phi_s_le_: (φ (ofMul s)).natAbs ≤ M := by omega
      calc
        _ ≤ M * M + ((φ (ofMul s)).natAbs * gamma_list.length + M * M + 1) := by
          nlinarith
        _ ≤ 2 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) + 1 := by
          nlinarith
        -- Extremely crude upper bound, but we only need to show a polynomial bound,
        -- so it's fine to use '1 <= N * N'
        _ ≤ 2 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) + M*M := by
          nlinarith
        _ ≤ 3 * M * M + ((φ (ofMul s)).natAbs * gamma_list.length) := by
          nlinarith
        _ ≤ 3 * M * M + (M * gamma_list.length) := by
          nlinarith
        _ ≤ 3 * M * M + (M * M) := by
          nlinarith
        _ = 4 * M * M := by
          nlinarith
        _ = 4 * M^2 := by nlinarith


  have b_n_subset_s_n_squared: ∀ M, N ≤ M → three_two_B_n (S := {s}) φ γ M ⊆ S ^ (M * (4 * M^2)) := by
    intro M hM a ha
    have orig_ha := ha
    rw [Finset.mem_pow]
    simp [three_two_B_n] at ha
    obtain ⟨l, l_len, l_prod⟩ := ha
    let nested_list := l.map (fun s => ((s_n_bound M hM s.val s.property).choose))
    have flat_list_prod: nested_list.flatten.unattach.prod = a := by
      simp [nested_list]
      rw [← l_prod]
      conv =>
        lhs
        arg 1
        equals l.unattach =>
          clear l_len l_prod nested_list
          induction l with
          | nil =>
            simp
          | cons h t ih =>
            simp
            rw [ih]
            simp [List.unattach, -List.map_subtype]
            have my_spec := Exists.choose_spec ((s_n_bound M hM h h.property))
            have first_prop := my_spec.1
            -- wtf
            nth_rw 8 [← first_prop]
            simp


    have flat_list_len: nested_list.flatten.length ≤ nested_list.length • (4 * M^2) := by
      simp
      have foo := List.sum_le_card_nsmul (l := (List.map List.length nested_list)) (4 * M^2) ?_
      .
        conv at foo =>
          rhs
          simp
        exact foo
      .
        intro q hq
        simp at hq
        obtain ⟨s_list, h_s_prod, s_len⟩ := hq
        simp [nested_list] at h_s_prod
        obtain ⟨gamma_n, gamma_n_mem, gamma_n_mem_l, s_prod_eq⟩ := h_s_prod
        have s_prod_prop: s_list.unattach.prod = gamma_n ∧ s_list.length ≤ 4*M^2 := by
          have my_spec := Exists.choose_spec ((s_n_bound M hM gamma_n gamma_n_mem))
          rw [s_prod_eq] at my_spec
          exact my_spec
        rw [← s_len]
        exact s_prod_prop.2

    have nested_len_eq: nested_list.length = l.length := by
      simp [nested_list]

    rw [nested_len_eq] at flat_list_len
    simp [list_len_n] at l_len
    simp only [smul_eq_mul] at flat_list_len
    have nested_list_le_n_squared: nested_list.flatten.length ≤ M * (4 * M^2) := by
      apply le_mul_of_le_mul_right (b := l.length)
      . omega
      . omega


    let filled_list := nested_list.flatten ++ (List.replicate ((M * (4 * M^2)) - nested_list.flatten.length) ⟨1, hGS.one_mem⟩)

    have filled_list_prod: filled_list.unattach.prod = nested_list.flatten.unattach.prod := by
      simp [filled_list]


    have len_eq: filled_list.length = M * (4 * M^2) := by
      simp [filled_list]
      apply Nat.add_sub_of_le
      simp at nested_list_le_n_squared
      exact nested_list_le_n_squared

    rw [← len_eq]
    use filled_list.get
    conv =>
      lhs
      equals (List.ofFn (filled_list.get)).unattach.prod =>
        simp

    simp
    rw [filled_list_prod]
    exact flat_list_prod

  conv at b_n_subset_s_n_squared =>
    intro M hM
    rhs
    rhs
    equals 4 * M^3 => ring


  -- #(B_n) grows exponentially, at least from N onword
  have b_n_card_exp: ∀ M: ℕ, N ≤ M → 2^(M - N) ≤ #(three_two_B_n (S := {s}) φ γ M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      simp [three_two_B_n, list_len_n]
      use [⟨(gamma_m_helper φ γ 0 ⟨s, s_mem⟩), ?_⟩]
      . simp [N]
      .
        simp [three_two_S_n]
        use 0
        refine ⟨by omega, ?_⟩
        simp [gamma_m_helper, e_i_regular_helper]

    | succ k hk ih =>
      rw [← tsub_add_eq_add_tsub hk]
      rw [pow_succ]

      specialize this k
      rw [Finset.not_subset] at this
      obtain ⟨p, ⟨p_mem, p_not_prod⟩⟩ := this

      have union_subset_n_succ: three_two_B_n (S := {s}) φ γ k ∪ (p • three_two_B_n (S := {s}) φ γ k) ⊆ three_two_B_n (S := {s}) φ γ (k + 1) := by
        apply Finset.union_subset
        . exact b_n_subset_b_n_succ k hk
        . exact smul_subset k hk p p_mem


      have card_le := Finset.card_le_card (union_subset_n_succ)
      rw [Finset.card_union_of_disjoint ?_] at card_le
      .
        simp at card_le
        ring_nf at card_le
        rw [add_comm] at card_le
        omega
      .
        specialize disjoint_smul  k hk p p_mem p_not_prod
        rw [Finset.inter_comm] at disjoint_smul
        rw [Finset.disjoint_iff_inter_eq_empty]
        exact disjoint_smul


  have little_o_poly := isLittleO_pow_exp_pos_mul_atTop (3 * d) (b := (Real.log 2)) (by
    apply Real.log_pos
    simp
  )
  simp_rw [Real.exp_mul] at little_o_poly
  rw [Real.exp_log (by simp)] at little_o_poly


  obtain ⟨a, hG⟩ := hG

  have a_ne_zero: a ≠ 0 := by
    by_contra!
    rw [this] at hG
    have hg_one := hG 1 (by omega)
    simp at hg_one
    have one_mem := hGS.one_mem
    rw [hg_one] at one_mem
    simp at one_mem

  have mul_four := Asymptotics.IsLittleO.const_mul_left little_o_poly (a * 4^d)
  rw [← Asymptotics.isLittleO_const_mul_right_iff (c := 2^(-N : ℤ)) (hc := (by simp))] at mul_four


  apply Asymptotics.IsLittleO.def (c := (1 : ℝ)  / 2) (hc := by simp) at mul_four
  apply Filter.Eventually.natCast_atTop at mul_four
  simp at mul_four
  obtain ⟨M', hM⟩ := mul_four
  let M: ℕ := max N M'


  have m_le_n: N ≤ M := by omega


  specialize b_n_card_exp M m_le_n
  specialize b_n_subset_s_n_squared
  have b_n_subset_n := Finset.card_le_card (b_n_subset_s_n_squared M (m_le_n))

  have m_ge_one: 1 ≤ M := by
    omega

  have m_cubed: 1 ≤ M^3 := by
    apply Nat.one_le_pow
    omega


  have other_poly := hG (4 * M ^ 3) (by
    omega
  )

  have m_pow_lt := hM (M) (by omega)
  rw [pow_mul] at m_pow_lt


  have helper_lemma (a b c : ℝ) (ha: 0 < a) (hb: 0 < b) (hc: 0 < c) (habc: a ≤ b * c) (hb: b < 1): a < c := by
    nlinarith

  have strict_lt: a * 4 ^ d * (↑M ^ 3) ^ d < (((2 : ℝ) ^ N)⁻¹ * 2 ^ M) := by
    apply helper_lemma (b := 2⁻¹)
    .
      field_simp
      positivity
    . simp
    . simp
    . exact m_pow_lt
    . norm_num


  conv at strict_lt =>
    rhs
    equals 2^(M - N) =>
      field_simp
      rw [← pow_add]
      simp
      omega


  norm_cast at strict_lt
  rw [mul_assoc, ← mul_pow] at strict_lt


  omega


attribute [local implicit_reducible] Additive Multiplicative

--- Consequence of `three_two_poly_growth` - the set of all 'γ^n *e_i γ^(-n)' is contained the closure of S_n
lemma three_poly_poly_growth_all_s_n (d: ℕ) (hG: HasPolynomialGrowthD S d ) (γ: G) (φ: (Additive G) →+ ℤ)
  : ∃ n, ∀ m, ((Finset.image (gamma_m_helper (S := S) φ γ m) Finset.univ : Finset G) : Set G) ⊆ Subgroup.closure ((three_two_S_n S  φ γ (n) : Finset G) : Set G) := by


  let r: ℕ := Finset.max' (Finset.image (fun s => (by
    exact sInf { n: ℕ | three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹) }
  )) S) (by
    simp
    exact S_nonempty
  )
  use r
  intro m
  intro x hx
  simp [gamma_m_helper] at hx
  simp [three_two_S_n, gamma_m_helper]
  obtain ⟨s, hs, x_eq_conj⟩ := hx

  let all_n_vals := { n : ℕ | three_two_S_n (S := {s}) φ γ (n + 1) ⊆ ((three_two_B_n (S := {s}) φ γ n) * (three_two_B_n (S := {s}) φ γ n)⁻¹)}
  let n := sInf all_n_vals
  have set_nonempty: all_n_vals.Nonempty := by
    exact new_three_two_poly_growth  d hG γ φ s hs
  have temp_s_n_subset := Nat.sInf_mem set_nonempty
  have s_n_subset: n ∈ all_n_vals := by
    exact temp_s_n_subset
  simp [all_n_vals] at s_n_subset
  have n_le_r: n ≤ r := by
    simp [r]
    apply Finset.le_max'
    simp
    use s


  have my_iter := closure_iterate_mulact γ (e_i_regular_helper φ γ ⟨s, hs⟩) (n + 1)
  simp [three_two_S_n, gamma_m_helper] at s_n_subset
  have closure_eq := my_iter ?_ ?_
  .
    have x_mem_closure_range: x ∈ Subgroup.closure (Set.range fun (m : ℤ) ↦ γ ^ m * e_i_regular_helper φ γ ⟨s, hs⟩ * γ ^ (-m : ℤ)) := by
      by_cases m_pos: 0 < m
      .
        have m_eq_natabs: m = m.natAbs := by
          omega
        apply Subgroup.subset_closure
        simp
        use m.natAbs
        rw [m_eq_natabs] at x_eq_conj
        rw [← x_eq_conj]
      .
        apply Subgroup.subset_closure
        simp
        use m

    rw [← closure_eq] at x_mem_closure_range
    apply Subgroup.closure_mono (h := ((fun (m : ℤ) ↦ γ ^ m * e_i_regular_helper φ γ ⟨s, hs⟩ * γ ^ (-m : ℤ)) '' (Set.Ioo (-(r + 1) : ℤ) (r + 1 : ℤ))))
    .
      intro p hp
      simp at hp
      simp
      obtain ⟨q, hp, p_eq⟩ := hp
      use q
      refine ⟨by omega, ?_⟩
      use s
      use hs
      rw [gamma_m_helper, zpow_neg]
      exact p_eq
    .
      apply (Subgroup.closure_mono _) x_mem_closure_range
      intro z hz
      simp at hz
      simp
      obtain ⟨a, ⟨a_gt, a_lt⟩, z_eq⟩ := hz
      use a
      refine ⟨⟨?_, ?_⟩, z_eq⟩
      .
        norm_cast at a_gt
        omega
      .
        norm_cast at a_lt
        omega
  .
    specialize s_n_subset (n + 1) (by omega) (by omega) s rfl
    simp [three_two_B_n] at s_n_subset
    rw [Finset.mem_mul] at s_n_subset
    obtain ⟨val, val_in_image, other_val, ⟨other_val_in_image, prod_vals_eq⟩⟩ := s_n_subset
    rw [← zpow_neg] at prod_vals_eq
    -- todo - avoid needing to do these simps
    simp [e_i_regular_helper] at prod_vals_eq
    simp [e_i_regular_helper]
    rw [← prod_vals_eq]
    apply Subgroup.mul_mem
    .
      simp at val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := val_in_image
      rw [← list_prod_eq]
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
    .
      simp at other_val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := other_val_in_image
      apply_fun Inv.inv at list_prod_eq
      simp at list_prod_eq
      rw [← list_prod_eq]
      apply Subgroup.inv_mem
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
  .
    -- TODO - 99% of this can be deduplicated
    specialize s_n_subset (-(n + 1)) (by omega) (by omega) s rfl
    -- Deduplicate verything after here
    simp [three_two_B_n] at s_n_subset

    rw [Finset.mem_mul] at s_n_subset
    obtain ⟨val, val_in_image, other_val, ⟨other_val_in_image, prod_vals_eq⟩⟩ := s_n_subset
    rw [← zpow_neg] at prod_vals_eq
    -- todo - avoid needing to do these simps
    simp [e_i_regular_helper] at prod_vals_eq
    simp [e_i_regular_helper]
    rw [← prod_vals_eq]
    apply Subgroup.mul_mem
    .
      simp at val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := val_in_image
      rw [← list_prod_eq]
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]
    .
      simp at other_val_in_image
      obtain ⟨list, hlist, list_prod_eq⟩ := other_val_in_image
      apply_fun Inv.inv at list_prod_eq
      simp at list_prod_eq
      rw [← list_prod_eq]
      apply Subgroup.inv_mem
      apply Subgroup.list_prod_mem
      intro z hz
      simp [list_len_n] at hlist
      simp at hz
      obtain ⟨z_in_s_n, z_in_list⟩ := hz
      simp [three_two_S_n] at z_in_s_n
      apply Subgroup.subset_closure
      simp
      obtain ⟨p, p_in_range, e_i_eq⟩ := z_in_s_n
      use p
      norm_cast
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      simp [gamma_m_helper] at e_i_eq
      obtain ⟨q, q_mem, e_i_eq'⟩ := e_i_eq
      simp [e_i_regular_helper]

end GeneratesNS
end

section
-- module Solutions.OAIQ093_PR.ThreeTwoGenerates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The sets `S_n` generate the kernel

`e_i_and_gamma_generates_G`, `three_two_gamma_m_generates` and the finite generation of the
kernel of `φ`.
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

set_option maxHeartbeats 9000000

open MeasureTheory

open Additive

attribute [local implicit_reducible] Additive Multiplicative

-- The kernel of `φ` is generated by {γ_m_i}
set_option maxHeartbeats 1000000
lemma three_two_gamma_m_generates (φ: (Additive G) →+ ℤ) (γ: G) (hγ: φ γ = 1) : Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S)  φ γ))) = AddSubgroup.toSubgroup φ.ker := by
  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ
  --
  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))


  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))
  have e_i_zero: ∀ s: S, φ (e_i s) = 0 := by
    intro s
    unfold e_i
    simp
    simp [phi_ofmul]

  have e_i_regular_zero: ∀ s: S, φ (ofMul (e_i_regular s)) = 0 := by
    dsimp [ofMul]
    intro s
    unfold e_i_regular
    simp
    simp [phi_ofmul]

  have closure_enlarge: Subgroup.closure ({1, γ, γ⁻¹} ∪ (e_i '' Set.univ)) = Subgroup.closure (({1, γ, γ⁻¹} ∪ (e_i_regular '' Set.univ))^(max_phi + 1)) := by
    rw [Subgroup.closure_pow]
    . simp
    . unfold max_phi
      simp


  have new_closure_e_i := e_i_and_gamma_generates_G φ γ hγ
  let gamma_m := fun (m: ℤ) (s: S) => γ^m * (e_i s).toMul * γ^(-m)
  have gamma_m_ker_phi: (Subgroup.closure (Set.range (Function.uncurry gamma_m))) = φ.ker.toSubgroup := by
    ext z
    refine ⟨?_, ?_⟩
    . intro hz
      have foo := Submonoid.exists_list_of_mem_closure (s := Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) (x := z)
      rw [← Subgroup.closure_toSubmonoid _] at foo
      specialize foo hz
      obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
      rw [← l_prod]
      rw [← MonoidHom.coe_toMultiplicative_ker]
      show (AddMonoidHom.toMultiplicative φ) (List.prod (l : List (Multiplicative (Additive G)))) = 1
      rw [map_list_prod]
      apply List.prod_eq_one
      intro x hx
      simp at hx
      obtain ⟨a, a_mem_l, phi_a⟩ := hx
      specialize l_mem_s a a_mem_l
      unfold gamma_m at l_mem_s
      simp at l_mem_s
      rw [← phi_a]
      match l_mem_s with
      | .inl a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
      | .inr a_eq_prod =>
        obtain ⟨n, val, val_in_s, prod_eq_a⟩ := a_eq_prod
        apply_fun Inv.inv at prod_eq_a
        simp at prod_eq_a
        -- TODO - deduplicate this with the branch above
        rw [← prod_eq_a]
        simp
        have apply_mult := AddMonoidHom.toMultiplicative_apply_apply φ (toMul (e_i ⟨val, val_in_s⟩))
        conv at apply_mult =>
          rhs
          rhs
          arg 2
          equals e_i ⟨val, val_in_s⟩ => rfl
        rw [e_i_zero] at apply_mult
        exact apply_mult
    .
      intro hz

      -- We need to write 'γ^a (f⁻¹ )' as an element of e_i


      have foo := Submonoid.exists_list_of_mem_closure (s := ({1, γ, γ⁻¹} ∪ e_i '' Set.univ) ∪ ({1, γ, γ⁻¹} ∪ e_i '' Set.univ)⁻¹) (x := z)
      apply_fun Subgroup.toSubmonoid at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i
      rw [Subgroup.closure_toSubmonoid _] at new_closure_e_i

      have e_i_eq: e_i = e_i_with_gamma φ γ := rfl
      rw [← e_i_eq] at new_closure_e_i
      rw [new_closure_e_i] at foo
      rw [← Subgroup.closure_toSubmonoid _] at foo
      simp only [mem_toSubmonoid, Finset.mem_coe] at foo

      conv at foo =>
        intro hz
        arg 1
        intro l
        lhs
        intro y
        intro hy
        rw [Set.union_comm {1, γ, γ⁻¹} (e_i '' Set.univ)]
        rw [Set.union_assoc]
        arg 1
        rhs
        rw [Set.union_comm]
        rw [Set.union_inv]
        rw [Set.union_assoc]
        rhs
        simp

      have generates := hGS.generates
      have z_in_top: z ∈ (⊤: Set G) := by
        simp

      rw [← generates] at z_in_top
      have z_eq_prod := foo z_in_top
      clear foo

      let E: Set G := {γ, γ⁻¹} ∪ Set.range e_i_regular ∪ (Set.range e_i_regular)⁻¹

      let rec rewrite_list (list: List (E)) (hlist: φ (ofMul list.unattach.prod) = 0): { t: List (((Set.range (Function.uncurry gamma_m) : (Set G)) ∪ (Set.range (Function.uncurry gamma_m))⁻¹ : (Set G))) // list.unattach.prod = t.unattach.prod } := by
        let is_gamma: E → Bool := fun (k: E) => k = γ ∨ k = γ⁻¹
        let is_gamma_prop: E → Prop := fun (k: E) => k = γ ∨ k = γ⁻¹
        have eq_split: list = list.takeWhile is_gamma ++ list.dropWhile is_gamma := by
          exact Eq.symm List.takeWhile_append_dropWhile
        by_cases header_eq_full: list.takeWhile is_gamma = list
        .
          have list_eq_gamma_m: ∃ m: ℤ, list.unattach.prod = γ ^ m := by
            unfold is_gamma at header_eq_full
            clear eq_split is_gamma is_gamma_prop hlist

            induction list with
            | nil =>
              use 0
              simp
            | cons h t ih =>
              have h_gamma: h = γ ∨ h = γ⁻¹ := by
                simp at header_eq_full
                exact header_eq_full.1
              rw [List.takeWhile_cons_of_pos] at header_eq_full
              .
                rw [List.cons_eq_cons] at header_eq_full
                specialize ih header_eq_full.2
                obtain ⟨m, hm⟩ := ih
                by_cases h_eq_gamma: h = γ
                .
                  use (m + 1)
                  simp [h_eq_gamma, hm]
                  exact mul_self_zpow γ m
                . use (-1 + m)
                  simp [h_eq_gamma] at h_gamma
                  simp [h_gamma, hm]
                  rw [← zpow_neg_one]
                  rw [zpow_add]
              . simp [h_gamma]


          have empty_prod_eq: list.unattach.prod = ([] : List E).unattach.prod := by
            obtain ⟨m, hm⟩ := list_eq_gamma_m
            rw [hm]
            simp
            rw [hm] at hlist
            simp at hlist
            simp [phi_ofmul] at hlist
            simp [hlist]

          exact ⟨[], empty_prod_eq⟩
        .

          have tail_nonempty: list.dropWhile is_gamma ≠ [] := by
            rw [not_iff_not.mpr List.takeWhile_eq_self_iff] at header_eq_full
            rw [← not_iff_not.mpr List.dropWhile_eq_nil_iff] at header_eq_full
            exact header_eq_full

          have dropwhile_len_gt: 0 < (list.dropWhile is_gamma).length := by
            exact List.length_pos_iff.mpr tail_nonempty

          have not_is_gamma := List.dropWhile_get_zero_not is_gamma list dropwhile_len_gt
          simp at not_is_gamma

          have not_is_gamma_prop: ¬ is_gamma_prop (List.dropWhile is_gamma list)[0] := by
            dsimp [is_gamma_prop]
            dsimp [is_gamma] at not_is_gamma
            exact of_decide_eq_false not_is_gamma

          simp [is_gamma_prop] at not_is_gamma_prop
          have drop_head_in_e_i: (List.dropWhile is_gamma list)[0].val ∈ (Set.range e_i_regular) ∪ (Set.range e_i_regular)⁻¹ := by
            have drop_in_E: (List.dropWhile is_gamma list)[0].val ∈ E := by
              simp [E]
            simp only [E] at drop_in_E
            simp_rw [Set.union_assoc] at drop_in_E
            rw [Set.mem_union] at drop_in_E
            have not_in_left: (List.dropWhile is_gamma list)[0].val ∉ ({γ, γ⁻¹} : Set G) := by
              simp [not_is_gamma_prop]

            -- TODO - why can't simp handle this?
            have in_right := Or.resolve_left drop_in_E not_in_left
            exact in_right


          let m := ((list.takeWhile is_gamma).map (fun (k : E) => if k = γ then 1 else if k = γ⁻¹ then -1 else 0)).sum

          have in_range: γ ^ m * ↑(List.dropWhile is_gamma list)[0] * γ ^ (-m) ∈ (Set.range (Function.uncurry gamma_m)) ∪ ((Set.range (Function.uncurry gamma_m)))⁻¹ := by
            simp [gamma_m]
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              left
              use m
              use s
              use s_in_S
              simp
              rw [← eq_e_i]
              rfl
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              right
              use m
              use s
              use s_in_S
              conv =>
                rhs
                rw [← mul_assoc]
              simp
              rw [← eq_e_i]
              rfl

          have phi_ofmul_gamma: φ (ofMul γ) = 1 := by
            exact hγ

          have gamma_ne_inv: γ ≠ γ⁻¹ := by
            by_contra this
            apply_fun ofMul at this
            apply_fun φ at this
            rw [phi_ofmul_gamma] at this
            rw [ofMul_inv] at this
            rw [AddMonoidHom.map_neg] at this
            rw [phi_ofmul_gamma] at this
            omega

          let gamma_copy: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ⁻¹, by simp [E]⟩
          let gamma_copy_inv: List E := if (m >= 0) then List.replicate m.natAbs ⟨γ⁻¹, by simp [E]⟩ else List.replicate (m.natAbs) ⟨γ, by simp [E]⟩

          have gamma_copy_prod: gamma_copy.unattach.prod = γ^m := by
            simp [gamma_copy]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have gamma_copy_inv_prod: gamma_copy_inv.unattach.prod = γ^(-m) := by
            simp [gamma_copy_inv]
            by_cases m_ge: 0 ≤ m
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              rw [← abs_eq_self] at m_ge
              rw [m_ge]
            .
              simp [m_ge]
              rw [← zpow_natCast]
              simp
              simp at m_ge
              have m_le: m ≤ 0 := by omega
              rw [← abs_eq_neg_self] at m_le
              simp [m_le]

          have E_inhabited: Inhabited E := by
            use γ
            simp [E]

          have header_prod: (List.takeWhile is_gamma list).unattach.prod = γ^m := by
            have my_lemma := take_count_sum_eq_exp (List.takeWhile is_gamma list) γ gamma_ne_inv ?_
            .
              rw [my_lemma]
            .
              have foo (x: E) := List.mem_takeWhile_imp (p := fun (val: E) => (val = γ ∨ val = γ⁻¹)) (l := list) (x := x)
              conv at foo =>
                intro x hx
                equals ↑x = γ ∨ ↑x = γ⁻¹ =>
                  simp
              exact foo

          -- 'γ^n * a * γ^(_n) * γn * tail', as a list of elements in E
          let mega_list := (gamma_copy ++ [(List.dropWhile is_gamma list)[0]] ++ gamma_copy_inv) ++ (gamma_copy ++ (list.dropWhile is_gamma).tail)
          have mega_list_prod: mega_list.unattach.prod = list.unattach.prod := by
            simp [mega_list]
            simp [gamma_copy_prod, gamma_copy_inv_prod]
            conv =>
              rhs
              rw [eq_split]
              rw [List.unattach_append]
              simp
            have dropwhile_not_nul : (List.dropWhile is_gamma list) ≠ [] := by
              exact tail_nonempty
            apply_fun (fun x => x * (List.dropWhile is_gamma list).unattach.prod⁻¹)
            .
              simp
              conv =>
                pattern _[0]
                equals (List.dropWhile is_gamma list).headI =>
                  rw [← List.head_eq_getElem_zero dropwhile_not_nul]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.head_eq_getElem_zero]
                  exact
                    Eq.symm
                      (List.getI_eq_getElem (List.dropWhile is_gamma list)
                        (List.length_pos_iff.mpr dropwhile_not_nul))

              have unattach_len_pos: 0 < (List.dropWhile is_gamma list).unattach.length := by
                rw [List.length_unattach]
                exact List.length_pos_iff.mpr dropwhile_not_nul

              -- TODO - this is gross, and should be removed
              letI : Inhabited G := {
                default := 1
              }

              conv =>
                lhs
                lhs
                rhs
                equals (List.dropWhile is_gamma list).unattach.headI * (List.dropWhile is_gamma list).unattach.tail.prod =>
                  rw [← List.getI_zero_eq_headI]
                  rw [← List.getI_zero_eq_headI]
                  rw [List.getI_eq_getElem _ (List.length_pos_iff.mpr dropwhile_not_nul)]
                  rw [List.getI_eq_getElem _ unattach_len_pos]
                  simp [List.getElem_unattach _ unattach_len_pos]
                  rw [list_tail_unattach]

              rw [List.headI_mul_tail_prod_of_ne_nil]
              .
                simp
                simp [header_prod]
              .
                by_contra this
                rw [List.eq_nil_iff_length_eq_zero] at this
                rw [List.length_unattach] at this
                rw [← List.eq_nil_iff_length_eq_zero] at this
                contradiction


            . exact mul_left_injective (List.dropWhile is_gamma list).unattach.prod⁻¹

          have sublist_phi_zero: φ (gamma_copy ++ (List.dropWhile is_gamma list).tail).unattach.prod = 0 := by
            rw [← mega_list_prod] at hlist
            unfold mega_list at hlist
            simp at hlist
            simp at drop_head_in_e_i
            match drop_head_in_e_i with
            | .inl drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist
            | .inr drop_head_in_e_i =>
              obtain ⟨s, s_in_S, eq_e_i⟩ := drop_head_in_e_i
              rw [inv_eq_iff_eq_inv.symm] at eq_e_i
              rw [← eq_e_i] at hlist
              simp [e_i_regular_zero] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              nth_rw 1 [← ofMul_list_prod] at hlist
              rw [gamma_copy_prod, gamma_copy_inv_prod] at hlist
              simp at hlist
              rw [← ofMul_list_prod] at hlist
              rw [← ofMul_list_prod] at hlist
              simp
              conv =>
                lhs
                arg 2
                equals (ofMul gamma_copy.unattach.prod) + (ofMul (List.dropWhile is_gamma list).tail.unattach.prod) =>
                  rfl

              simp
              rw [← ofMul_list_prod]
              rw [← ofMul_list_prod]
              exact hlist

          have count_head_lt: (List.map (fun (k: E) ↦ if ↑k = γ then (1 : ℤ) else if ↑k = γ⁻¹ then -1 else 0)
          (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list)).sum.natAbs ≤ (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list).length := by
            induction (List.takeWhile (fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹)) list) with
            | nil =>
              simp
            | cons h t ih =>
              simp
              split_ifs
              . omega
              . omega
              . omega

          let rewritten_sub_list := (rewrite_list (gamma_copy ++ (list.dropWhile is_gamma).tail) sublist_phi_zero)
          let return_list := (⟨γ^m * (List.dropWhile is_gamma list)[0] * γ^(-m), in_range⟩) :: rewritten_sub_list.val

          -- Show that the list (rewritten in terms of `γ^m * e_i * γ^(-m)` terms) is in the kernel of φ


          have mega_list_prod_preserve: mega_list.unattach.prod = return_list.unattach.prod := by
            unfold mega_list return_list
            simp
            rw [gamma_copy_prod]
            rw [gamma_copy_inv_prod]
            simp
            rw [← rewritten_sub_list.property]
            simp
            rw [gamma_copy_prod]
            conv =>
              rhs
              rw [mul_assoc]
              rhs
              rw [← mul_assoc]
              simp
            rw [mul_assoc]

          have return_list_prod: list.unattach.prod = return_list.unattach.prod := by
            rw [← mega_list_prod_preserve]
            exact mega_list_prod.symm


          exact ⟨return_list, return_list_prod⟩
      termination_by list.length
      decreasing_by {
        simp
        split_ifs
        .
          simp
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
        .
          simp-- [count_gamma_copy]
          conv =>
            rhs
            rw [← take_drop_len (p := fun (k: E) ↦ decide (↑k = γ) || decide (↑k = γ⁻¹))]
          apply add_lt_add_of_le_of_lt
          . apply count_head_lt
          . simp [is_gamma] at dropwhile_len_gt
            apply Nat.sub_one_lt
            apply Nat.pos_iff_ne_zero.mp dropwhile_len_gt
      }

      obtain ⟨z_list, h_z_list⟩ := z_eq_prod
      rw [← list_filter_one] at h_z_list
      have z_filter_mem_e: ∀ p ∈ (List.filter (fun s ↦ !decide (s = 1)) z_list), p ∈ E := by
        intro p hp
        dsimp [E]
        simp at hp
        obtain ⟨h_z_list_in, _⟩ := h_z_list
        specialize h_z_list_in p hp.1
        rw [Set.mem_union] at h_z_list_in
        rw [Set.mem_union] at h_z_list_in
        match h_z_list_in with
        | .inl h_z_list_in =>
          simp at h_z_list_in
          obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
          apply Set.mem_union_left
          apply Set.mem_union_right
          simp
          use a
          use a_mem_s
        | .inr h_z_list_in =>
          simp at h_z_list_in
          match h_z_list_in with
          | .inl h_z_list_in =>
            obtain ⟨a, a_mem_s, e_i_ap⟩ := h_z_list_in
            apply Set.mem_union_right
            simp
            use a
            use a_mem_s
          | .inr h_z_list_in =>
            simp [hp.2] at h_z_list_in
            apply Set.mem_union_left
            apply Set.mem_union_left
            simp
            exact h_z_list_in.symm

      let my_res := rewrite_list ((z_list.filter (fun s ↦ !decide (s = 1))).attach.map (fun (g) => ⟨g.val, z_filter_mem_e g.val g.property⟩)) (by
        simp
        -- TODO - there has to be a less awful way of doing this
        conv =>
          arg 1
          arg 2
          arg 1
          arg 2
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            clear h_z_list

            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        rw [← ofMul_list_prod]
        rw [h_z_list.2]
        exact hz
      )
      have my_res_prop := my_res.property
      rw [← Subgroup.mem_toSubmonoid]
      rw [Subgroup.closure_toSubmonoid _]
      conv =>
        equals z ∈ (Submonoid.closure (Set.range (Function.uncurry gamma_m) ∪ (Set.range (Function.uncurry gamma_m))⁻¹) : Set _) =>
          rfl
      rw [Submonoid.closure_eq_image_prod]
      rw [Set.mem_image]
      use my_res.val.unattach
      refine ⟨?_, ?_⟩
      . simp only [Set.mem_setOf_eq]
        intro x hx
        rw [List.mem_unattach] at hx
        obtain ⟨x_prop, _⟩ := hx
        exact x_prop
      .
        rw [← my_res_prop]
        conv =>
          pattern List.unattach _
          equals (List.filter (fun s ↦ !decide (s = 1)) z_list) =>
            ext i q
            simp
            by_cases list_get: (List.filter (fun s ↦ !decide (s = 1)) z_list)[i]? = none
            . simp [list_get]
            . simp at list_get
              simp [list_get]
        exact h_z_list.2
  exact gamma_m_ker_phi

lemma three_two_S_n_generates_oai  (d: ℕ) (hd: d >= 1) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ : Additive G) (phi_gamma: φ γ = 1): ∃ n, AddSubgroup.closure (Additive.ofMul '' (three_two_S_n S φ γ (n))) = φ.ker := by
  obtain ⟨n, hn⟩ := three_poly_poly_growth_all_s_n d hG γ φ
  use n
  ext z
  refine ⟨?_, ?_⟩
  . intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      have x_mem: x ∈ three_two_S_n S φ γ n := by
        simp at hx
        exact hx

      obtain ⟨y, hy, hyx⟩ := (three_two_S_n_subset_ker S φ γ phi_gamma n) x_mem
      rw [← hyx]
      exact hy
    | zero =>
      simp
    | add y z y_mem z_mem hy hz =>
      exact (AddSubgroup.add_mem_cancel_right φ.ker hz).mpr hy
    | neg x x_mem hx =>
      exact AddSubgroup.neg_mem φ.ker hx
  . intro hz
    have generates_ker := three_two_gamma_m_generates φ γ phi_gamma

    have hz' : z ∈ Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S) φ γ))) := by
      rw [generates_ker]; exact hz

    have hz'' : z ∈ (Subgroup.closure (Set.range (Function.uncurry (gamma_m_helper (S := S) φ γ)))).toSubmonoid := hz'
    rw [Subgroup.closure_toSubmonoid] at hz''
    have exists_prod := Submonoid.exists_list_of_mem_closure (M := Multiplicative (Additive G)) hz''
    obtain ⟨l, l_mem, z_eq_prod⟩ := exists_prod
    rw [← z_eq_prod]
    conv =>
      arg 2
      equals ofMul l.prod => rfl
    apply AddSubgroup.list_sum_mem
    simp only [Additive.forall]
    intro a ha
    specialize l_mem (ofMul a) ha
    rcases (Set.mem_union _ _ _).mp l_mem with l_mem | l_mem
    · obtain ⟨⟨p, s, s_mem⟩, helper_eq_a⟩ := Set.mem_range.mp l_mem
      simp only [Function.uncurry_apply_pair] at helper_eq_a
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      apply (AddSubgroup.mem_toSubgroup' _ (gamma_m_helper φ γ p ⟨s, s_mem⟩)).mp
      rw [AddSubgroup.toSubgroup'_closure]
      simp
      exact hn
    · rw [← AddSubgroup.neg_mem_iff]
      obtain ⟨⟨p, s, s_mem⟩, helper_eq_a⟩ := Set.mem_range.mp (Set.mem_inv.mp l_mem)
      simp only [Function.uncurry_apply_pair] at helper_eq_a
      conv at helper_eq_a =>
        rhs
        equals -ofMul a => rfl
      specialize hn p
      simp at hn
      rw [Set.range_subset_iff] at hn
      specialize hn ⟨s, s_mem⟩
      simp at hn
      rw [← helper_eq_a]
      apply (AddSubgroup.mem_toSubgroup' _ (gamma_m_helper φ γ p ⟨s, s_mem⟩)).mp
      rw [AddSubgroup.toSubgroup'_closure]
      simp
      exact hn

end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.three_two_S_n_generates_oai.{u_1} := @GeneratesNS.three_two_S_n_generates_oai.{u_1}
