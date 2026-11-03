-- Prove2me | solution 1 for GeneratesNS.three_two_kernel_poly_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:05:22.489309+00:00
-- url     : https://prove2.me/submissions/24abf1f2-3645-4588-a218-3dc64e484d93

import Mathlib
import Definitions.Def_OAIQ093D016
import Theorems.Thm_poly_growth_equiv

section
-- module Solutions.OAIQ093_PR.GrowthZero
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty
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


lemma three_two_kernel_poly_growth_oai  (d: ℕ) (hd: d >= 1) (n: ℕ) (hG: HasPolynomialGrowthD S d ) (φ: (Additive G) →+ ℤ) (γ: G) (hγ : φ γ = 1)
 : HasPolynomialGrowthD (G := Multiplicative φ.ker) (d - 1) (S := (S_n_ker_phi S φ γ hγ n) ∪ (S_n_ker_phi S φ γ hγ n)⁻¹) := by

  -- The set S_n, viewed a subset of ker φ


  obtain ⟨a, ha⟩ := hG

  by_cases a_eq_zero: a = 0
  .
    simp [a_eq_zero] at ha
    specialize ha 1 (by simp)
    simp at ha
    have s_nonempty := hGS.one_mem
    grind


  unfold HasPolynomialGrowthD


  have S_n_poly := poly_growth_equiv a d (by omega) S ((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1}) S_eq_Sinv hGS.one_mem (by simpa using hGS.generates) ha
  obtain ⟨b, hb, ker_poly⟩ := S_n_poly


  use b * (2 ^ d)

  intro r hr
  specialize ker_poly (2 * r) (by omega)


  let mul_by_i := fun (g: G) (i: Fin r) => g * (γ ^ i.val)
  have new_phi_gamma: φ (Additive.ofMul γ) = 1 := hγ
  have card_mul_range (g: G): #(Finset.image (mul_by_i g) Finset.univ) = r := by
    rw [Finset.card_image_of_injOn]
    . simp
    .

      intro j _ k _ mul_eq
      simp [mul_by_i] at mul_eq
      apply_fun φ ∘ (Additive.ofMul) at mul_eq
      simp [new_phi_gamma] at mul_eq
      rw [Fin.ext_iff]
      exact mul_eq

  have card_union: #((((((S_n_ker_phi S φ γ hγ n) ∪ (-(S_n_ker_phi S φ γ hγ n))).image Multiplicative.ofAdd) ^ r).image ofMul).biUnion (fun a => Finset.image (mul_by_i a.val) Finset.univ)) = r * #(r • ((S_n_ker_phi S φ γ hγ n) ∪ -((S_n_ker_phi S φ γ hγ n)))) := by
    rw [Finset.card_biUnion]
    .
      simp_rw [card_mul_range]
      simp
      rw [mul_comm]
      conv =>
        lhs
        arg 2
        arg 1
        equals r • ((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)) =>
          ext a
          rw [Finset.mem_image]
          simp_rw [Finset.mem_pow]
          refine Iff.trans ?_ Finset.mem_nsmul.symm
          refine ⟨?_, ?_⟩
          . intro h
            obtain ⟨b, ⟨f, hf⟩, b_eq_a⟩ := h
            use (fun i => ⟨(f i).val, (by
              have f_prop := (f i).property
              rw [Finset.mem_image] at f_prop
              obtain ⟨g, g_mem, hg⟩ := f_prop
              rw [← hg]
              exact g_mem
            )⟩)
            rw [← b_eq_a]
            rw [← hf]
            rfl
          . intro h
            obtain ⟨f, hf⟩ := h
            use a
            refine ⟨?_, rfl⟩
            use (fun i => ⟨(f i).val, (by
              have f_prop := (f i).property
              rw [Finset.mem_image]
              use (f i).val
              refine ⟨f_prop, ?_⟩
              rfl
            )⟩)
            rw [← hf]
            rfl


    .
      intro a ha b hb hab x h_first h_second
      simp at h_first
      simp at h_second
      simp

      by_contra!
      obtain ⟨p, hp⟩ := this
      have orig_h_first := h_first hp
      have orig_h_second := h_second hp
      specialize h_first hp
      specialize h_second hp

      simp at h_first
      simp at h_second

      obtain ⟨y, hy⟩ := h_first
      obtain ⟨z, hz⟩ := h_second

      have orig_hy := hy
      have orig_hz := hz

      rw [← hz] at hy
      simp [mul_by_i] at hy
      apply_fun φ ∘ (Additive.ofMul) at hy
      simp [new_phi_gamma] at hy

      have a_ker: a.val ∈ φ.ker := by
        simp

      have b_ker: b.val ∈ φ.ker := by
        simp

      rw [AddMonoidHom.mem_ker] at a_ker
      rw [AddMonoidHom.mem_ker] at b_ker
      simp [ofMul] at hy
      simp [a_ker, b_ker] at hy

      rw [← Fin.ext_iff] at hy
      rw [hy] at orig_hy
      rw [← orig_hy] at orig_hz
      simp [mul_by_i] at orig_hz
      rw [eq_comm] at orig_hz
      contradiction


  have card_union_le: #((((((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)).image Multiplicative.ofAdd) ^ r).image ofMul).biUnion (fun a => Finset.image (mul_by_i a.val) Finset.univ)) ≤ #(((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1}) ^ (2 * r)) := by
    grw [Finset.card_le_card]
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨s, s_mem, a_mem⟩ := ha
    rw [Finset.mem_image] at a_mem
    obtain ⟨k, _, hk⟩ := a_mem
    simp [mul_by_i] at hk
    rw [← hk]
    rw [two_mul]
    rw [pow_add]
    apply Finset.mul_mem_mul
    .
      unfold S_n_ker_phi at s_mem

      rw [Finset.mem_image] at s_mem
      obtain ⟨z, z_mem, hz⟩ := s_mem
      rw [← hz]

      rw [Finset.mem_pow] at z_mem
      obtain ⟨f, hf⟩ := z_mem
      rw [Finset.mem_pow]
      use (fun i => ⟨(f i).val.val, (by
        have f_prop := (f i).property
        rw [Finset.mem_image] at f_prop
        obtain ⟨g, g_mem, hg⟩ := f_prop
        rw [← hg]
        simp at g_mem
        cases g_mem
        .
          rename_i g_eq_zero
          apply Finset.mem_union_right
          rw [Finset.mem_singleton, g_eq_zero]
          first | rfl | simp
        . rename_i g_eq_nonzero
          cases g_eq_nonzero
          . rename_i left
            obtain ⟨z, z_mem, hz⟩ := left
            rw [← hz]
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            exact z_mem
          .
            rename_i right
            obtain ⟨z, z_mem, hz⟩ := right
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            apply Finset.mem_union_right
            simp
            conv =>
              arg 2
              equals (-g).val =>
                rfl
            rw [← hz]
            exact z_mem
      )⟩)
      rw [← hf, ofMul_list_prod, List.map_ofFn]
      first
        | (erw [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
        | (rw [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
        | (simp only [AddSubmonoidClass.coe_list_sum, List.map_ofFn]; rfl)
    .


      have gamma_r_subset: ({γ, 1} : Finset G)^r ⊆ ((three_two_S_n S φ γ n) ∪ ((three_two_S_n S φ γ n)⁻¹) ∪ {γ} ∪ {1})^r := by
        apply Finset.pow_subset_pow
        . grind
        . grind
        . simp

      have gamma_subset: ({γ, 1} : Finset G)^k.val ⊆ ({γ, 1} : Finset G)^r := by
        apply Finset.pow_subset_pow
        . simp
        . simp
        . simp


      have gamma_mem_self: γ^k.val ∈ ({γ, 1} : Finset G)^k.val := by
        apply Finset.pow_mem_pow
        simp

      grind


  rw [card_union] at card_union_le
  grw [ker_poly] at card_union_le
  rw [mul_pow] at card_union_le
  rw [← mul_assoc] at card_union_le
  rw [mul_comm] at card_union_le
  rw [← Nat.le_div_iff_mul_le] at card_union_le
  .
    rw [Nat.mul_div_assoc] at card_union_le
    .
      nth_rw 3 [← pow_one (a := r)] at card_union_le
      rw [Nat.pow_div] at card_union_le
      .
        -- TODO - get rid of this obnoxious  Additive/Multiplicative defeq abuse
        conv =>
          lhs
          arg 1
          equals r • ((S_n_ker_phi S φ γ hγ n) ∪ -(S_n_ker_phi S φ γ hγ n)) =>
            ext a
            rw [Finset.mem_pow]
            -- TODO - why do we need explicit args here
            refine Iff.trans ?_ Finset.mem_nsmul.symm
            refine ⟨?_, ?_⟩
            .
              intro hf
              obtain ⟨f, hf⟩ := hf
              use f
              exact hf
            . intro hf
              obtain ⟨f, hf⟩ := hf
              use f
              exact hf
        exact card_union_le
      . omega
      . omega

    .
      nth_rw 1 [← pow_one (a := r)]
      apply Nat.pow_dvd_pow
      omega
  . omega

end GeneratesNS
end

theorem solution.{u_1} : type_of% @GeneratesNS.three_two_kernel_poly_growth_oai.{u_1} := @GeneratesNS.three_two_kernel_poly_growth_oai.{u_1}
