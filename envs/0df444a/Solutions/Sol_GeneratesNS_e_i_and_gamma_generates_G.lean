-- Prove2me | solution 1 for GeneratesNS.e_i_and_gamma_generates_G
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:02:16.049557+00:00
-- url     : https://prove2.me/submissions/250285ac-7c5d-476b-946e-acd8f4c8197c

import Mathlib
import Definitions.Def_OAIQ093D016

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


-- The 'e_i' terms from Vikman 3.2, together with γ, generate the original group G
lemma e_i_and_gamma_generates_G_oai (φ: (Additive G) →+ ℤ) (γ: G) (hγ: φ γ = 1) : Subgroup.closure ({1, γ, γ⁻¹} ∪ ((e_i_with_gamma φ γ) '' Set.univ)) = (Subgroup.closure S) := by

  have phi_ofmul: φ (ofMul γ) = 1 := by
    exact hγ

  let e_i: S → (Additive G) := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))
  let e_i_regular: S → G := fun s => (ofMul s.val) +  ((-1 : ℤ) • (φ (ofMul s.val))) • (ofMul (γ))

  let max_phi := max 1 ((Finset.image Int.natAbs (Finset.image φ (Finset.image ofMul S))).max' (by simp [S_nonempty]))

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

  conv =>
    arg 1
    arg 1
    arg 2
    arg 1
    equals e_i_regular =>
      rfl
  rw [closure_enlarge]
  apply Subgroup.closure_eq_of_le
  .
    rw [hGS.generates]
    exact fun ⦃a⦄ a ↦ trivial
  .
    simp
    intro s hs
    simp
    rw [← mem_toSubmonoid]
    rw [Subgroup.closure_toSubmonoid]
    dsimp [Membership.mem]
    rw [Submonoid.closure_eq_image_prod]
    -- TODO - why do we need any of this?
    show s ∈ List.prod '' _
    rw [Set.mem_image]


    have foo := Submonoid.exists_list_of_mem_closure (s := ((S ∪ S⁻¹) : Set G)) (x := s)
    rw [← Subgroup.closure_toSubmonoid _] at foo
    simp only [mem_toSubmonoid, Finset.mem_coe] at foo
    have generates := hGS.generates
    have x_in_top: s ∈ (⊤: Set G) := by
      simp

    rw [← generates] at x_in_top
    specialize foo x_in_top
    obtain ⟨l, ⟨l_mem_s, l_prod⟩⟩ := foo
    norm_cast at l_mem_s
    rw [s_union_sinv] at l_mem_s

    let l_attach := l.attach
    let list_with_mem: List S := (l_attach).map (fun a => ⟨a.val, l_mem_s a.val a.prop⟩)
    let new_list := list_with_mem.map (fun s => (e_i s) + ofMul (γ^(((φ (ofMul s.val))))))

    have cancel_add_minus: max_phi - 1 + 1 = max_phi := by
      omega

    use new_list
    refine ⟨?_, ?_⟩
    .
      simp
      intro x hx
      unfold new_list list_with_mem l_attach at hx
      simp at hx
      obtain ⟨a, ha, x_eq_sum⟩ := hx
      left

      have gamma_phi_in_minus_plus: γ^(φ a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1  +1) := by
        by_cases val_pos: 0 < φ a
        .
          have eq_self: Int.natAbs (φ a) = φ a := by
            simp [val_pos]
            linarith
          conv =>
            arg 2
            equals γ ^ (Int.natAbs (φ a)) =>
              nth_rw 1 [← eq_self]
              norm_cast
          apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
          . simp
          .
            rw [cancel_add_minus]
            unfold max_phi
            simp
            right
            apply Finset.le_max'
            simp
            use a
            refine ⟨l_mem_s a ha, ?_⟩
            conv =>
              pattern ofMul a
              equals a => rfl
          .
            apply Set.pow_mem_pow
            simp
        .
          have eq_neg_abs: (φ a) = -(φ a).natAbs := by
            rw [← Int.abs_eq_natAbs]
            simp at val_pos
            rw [← abs_eq_neg_self] at val_pos
            omega
          rw [eq_neg_abs]
          conv =>
            arg 2
            equals (γ⁻¹) ^ (↑(φ a).natAbs) =>
              simp
              rw [Int.abs_eq_natAbs]
              norm_cast
          -- TOOD - deduplicate this with the positive case
          apply Set.pow_subset_pow_right (m := Int.natAbs (φ a)) (n := max_phi - 1 + 1)
          . simp
          .
            rw [cancel_add_minus]
            unfold max_phi
            simp
            right
            apply Finset.le_max'
            simp
            use a
            refine ⟨l_mem_s a ha, ?_⟩
            conv =>
              pattern ofMul a
              equals a => rfl
          .
            apply Set.pow_mem_pow
            simp
      have a_mem_s: a ∈ S := by exact l_mem_s a ha
      have prod_mem_power: e_i_regular ⟨a, a_mem_s⟩ * γ ^ φ (ofMul a) ∈ ({1, γ, γ⁻¹} ∪ Set.range e_i_regular) ^ (max_phi - 1 + 1 + 1) := by
        rw [pow_succ']
        rw [Set.mem_mul]
        use e_i_regular ⟨a, a_mem_s⟩
        refine ⟨by simp, ?_⟩
        use γ ^ φ (ofMul a)
        refine ⟨gamma_phi_in_minus_plus, ?_⟩
        simp

      have prod_eq_sum: e_i ⟨a, l_mem_s a ha⟩ + φ (ofMul a) • ofMul γ = (e_i_regular ⟨a, a_mem_s⟩) * (γ ^ φ (ofMul a)) := by
        simp [e_i, e_i_regular, cancel_add_minus]


        conv =>
          rhs
          arg 1
          equals ofMul (a* γ^(-(φ (ofMul a)))) =>
            simp

        apply_fun (fun x => x * (γ ^ (- φ (ofMul a))))
        .
          simp only
          simp
          conv =>
            lhs
            equals a * (γ ^ φ (ofMul a))⁻¹ =>
              simp
              rfl
          conv =>
            rhs
            rhs
            equals ofMul (γ ^ (- φ (ofMul a))) =>
              simp

          rw [← ofMul_mul]
          conv =>
            rhs
            equals (a * γ ^ (-φ (ofMul a))) =>
              rfl
          simp
        .
          exact mul_left_injective (γ ^ (-φ (ofMul a)))


      rw [← x_eq_sum]
      rw [prod_eq_sum]
      rw [cancel_add_minus] at prod_mem_power
      apply prod_mem_power


    unfold new_list list_with_mem l_attach
    simp
    conv =>
      arg 1
      arg 1
      arg 1
      arg 1
      intro z
      unfold e_i
      simp
    simp
    conv =>
      arg 1
      arg 1
      arg 1
      equals id =>
        rfl
    convert l_prod using 2
    all_goals try with_reducible_and_instances rfl
    exact List.map_id l


-- The kernel of `φ` is generated by {γ_m_i}
set_option maxHeartbeats 1000000

end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.e_i_and_gamma_generates_G_oai.{u_1} := @GeneratesNS.e_i_and_gamma_generates_G_oai.{u_1}
