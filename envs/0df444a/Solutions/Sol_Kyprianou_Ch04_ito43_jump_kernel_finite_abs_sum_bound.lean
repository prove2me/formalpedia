-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_jump_kernel_finite_abs_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:33:28.267174+00:00
-- url     : https://prove2.me/submissions/b0e89b58-240b-4e22-b8d6-b1e5326b89c6

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
import Theorems.Thm_Kyprianou_Ch04_bvRestrictedDiracIntegralV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hJ : ({s : NNReal | 0 < s ∧ X s w ≠ L s w}).Countable)
    (T t : NNReal) (ht : t ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hE : Summable (fun s : Ioc (0 : NNReal) T => (X s w-L s w)^2))
    (F : ℝ × ℝ → ℝ)
    (hb : ∀ s : NNReal, 0 < s → s ≤ t →
      |F ((s : ℝ), X s w-L s w)| ≤ C*(X s w-L s w)^2) :
    let B : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ univ
    let J : Set NNReal := {s | 0 < s ∧ X s w ≠ L s w}
    let φ : J → ℝ × ℝ := fun s => (((s : NNReal) : ℝ), X s w-L s w)
    ∀ S : Finset J, (∑ s ∈ S, |B.indicator F (φ s)|) ≤
      C * ∑' s : Ioc (0 : NNReal) T, (X s w-L s w)^2 := by
  classical
  intro B J φ
  let G : J → ℝ := fun s => B.indicator F (φ s)
  let E : Ioc (0 : NNReal) T → ℝ := fun s => (X s w-L s w)^2
  have hmem (s : J) : φ s ∈ B ↔ (s : NNReal) ≤ t := by
    simp [B,φ,NNReal.coe_nonneg]
  have hfin (S : Finset J) : ∑ s ∈ S, |G s| ≤ C * ∑' s, E s := by
    let A : Finset J := S.filter fun s : J => s.val ≤ t
    have hsub (s : A) : s.val.val ∈ Ioc (0 : NNReal) T :=
      ⟨s.val.property.1, (Finset.mem_filter.mp s.property).2.trans ht⟩
    let e : A → Ioc (0 : NNReal) T := fun s => ⟨s.val.val,hsub s⟩
    have hinj : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : Ioc (0 : NNReal) T => x.val) hab
    have hEq : (∑ s ∈ S, |G s|) = ∑ s ∈ A, |F (φ s)| := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases h : (s : NNReal) ≤ t <;> simp [G,Set.indicator_apply,hmem,h]
    rw [hEq,← Finset.sum_attach A]
    calc
      _ ≤ ∑ s ∈ A.attach, C*E (e s) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hb s.val.val s.val.property.1 (Finset.mem_filter.mp s.property).2
      _ = C*(∑ s ∈ A.attach.image e, E s) := by
        rw [Finset.mul_sum,Finset.sum_image hinj.injOn]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hE.sum_le_tsum _ (fun _ _ => sq_nonneg _)) hC
  exact hfin
