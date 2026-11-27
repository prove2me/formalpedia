-- Prove2me | solution 1 for GlobalTheory.exists_tuple_normalisation_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:10.541273+00:00
-- url     : https://prove2.me/submissions/49c6394a-7b6e-4437-b1cc-cdea022fe730

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsIntegralMulPowOfSubalgebra
import Theorems.Thm_GlobalTheory_exists_finite_span_isIntegral_chart
import Theorems.Thm_GlobalTheory_exists_mul_pow_mem_chart
import Theorems.Thm_GlobalTheory_exists_isIntegral_mul_pow_of_subalgebra
import Theorems.Thm_GlobalTheory_exists_sum_mul_pow_div_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    [IsDedekindDomain o] [CharZero Ω] (_hinj : Function.Injective (algebraMap o Ω)) (J : Type)
    [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω) :
    ∃ (e n : ℕ) (z : Fin (n + 1) → Ω), 1 ≤ e ∧ (∀ i, ∃ k, z k = t i ^ e) ∧
      (∀ i, t i ≠ 0 → ∀ x, x ∈ Algebra.adjoin o (Set.range fun k => z k / t i ^ e) ↔
        IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) ∧
      ∀ k, z k ≠ 0 → ∃ c : J → Algebra.adjoin o (Set.range fun l => z l / z k),
        ∑ i, (c i : Ω) * (t i ^ e / z k) = 1 := by
  let A : J → Subalgebra o Ω := fun i => Algebra.adjoin o (Set.range fun j => t j / t i)
  have hA : ∀ i, ∀ x ∈ A i, IsIntegral (A i) x := fun i x hx =>
    isIntegral_algebraMap (x := (⟨x, hx⟩ : A i))
  have hmem : ∀ i j, t j / t i ∈ A i := fun i j => Algebra.subset_adjoin ⟨j, rfl⟩
  choose G hG hGi hGs using fun i : {i // t i ≠ 0} =>
    exists_finite_span_isIntegral_chart (o := o) t i.2 hfin
  haveI : ∀ i, Finite (G i) := fun i => (hG i).to_subtype
  choose N hN using fun a : (Σ i, G i) × J =>
    exists_isIntegral_mul_pow_of_subalgebra (A a.1.1) (A a.2) (hmem a.2 a.1.1)
      (fun r hr => exists_mul_pow_mem_chart t a.2 a.1.1.2 hr) (hGi _ _ a.1.2.2)
  obtain ⟨d, hd⟩ := (Set.finite_range N).bddAbove
  let Z : Set Ω := Set.range (fun a : J × J => t a.1 ^ d * t a.2) ∪
    Set.range (fun a : (Σ i, G i) => (a.2 : Ω) * t a.1 ^ (d + 1))
  have hZ : Z.Finite := (Set.finite_range _).union (Set.finite_range _)
  obtain ⟨n, z, -, hz⟩ := hZ.fin_param
  have hzt : ∀ i j, ∃ k, z k = t i ^ d * t j := fun i j =>
    (hz.ge (Or.inl ⟨(i, j), rfl⟩) :)
  obtain _ | n := n
  · obtain ⟨i, -⟩ := ht
    obtain ⟨k, -⟩ := hzt i i
    exact k.elim0
  have hzi : ∀ k i, t i ≠ 0 → IsIntegral (A i) (z k / t i ^ (d + 1)) := by
    intro k i hi
    obtain ⟨a, ha⟩ | ⟨a, ha⟩ : z k ∈ Z := hz.le ⟨k, rfl⟩
    · have : z k / t i ^ (d + 1) = (t a.1 / t i) ^ d * (t a.2 / t i) := by
        rw [← ha, div_pow, div_mul_div_comm, pow_succ]
      rw [this]
      exact hA _ _ (mul_mem (pow_mem (hmem _ _) _) (hmem _ _))
    · have : z k / t i ^ (d + 1) = a.2 * (t a.1 / t i) ^ (d + 1) := by
        rw [← ha, div_pow, mul_div_assoc]
      rw [this]
      exact hN (a, i) _ ((hd ⟨_, rfl⟩).trans (Nat.le_succ d))
  have hzp : ∀ i, ∃ k, z k = t i ^ (d + 1) := fun i => by simpa [pow_succ] using hzt i i
  refine ⟨d + 1, n, z, Nat.le_add_left _ _, hzp, fun i hi x => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun k hk => exists_sum_mul_pow_div_eq_one t ht _ hk (hzi k) _ fun i => ?_⟩
  · have : Algebra.adjoin o (Set.range fun k => z k / t i ^ (d + 1)) ≤
        (integralClosure (A i) Ω).restrictScalars o := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨k, rfl⟩
      exact hzi k i hi
    exact this hx
  · have h1 : A i ≤ Algebra.adjoin o (Set.range fun k => z k / t i ^ (d + 1)) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := hzt i j
      refine Algebra.subset_adjoin ⟨k, ?_⟩
      simp only [hk]
      rw [pow_succ, mul_div_mul_left _ _ (pow_ne_zero _ hi)]
    have h2 := hGs ⟨i, hi⟩ x hx
    clear hx
    induction h2 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk⟩ : y * t i ^ (d + 1) ∈ Set.range z := hz.ge (Or.inr ⟨⟨⟨i, hi⟩, y, hy⟩, rfl⟩)
      refine Algebra.subset_adjoin ⟨k, ?_⟩
      simp only [hk]
      field_simp
    | zero => exact zero_mem _
    | add y w _ _ hy hw => exact add_mem hy hw
    | smul c y _ hy => exact mul_mem (h1 c.2) hy
  · obtain ⟨l, hl⟩ := hzp i
    exact Algebra.subset_adjoin ⟨l, by simp only [hl]⟩
end GlobalTheory
