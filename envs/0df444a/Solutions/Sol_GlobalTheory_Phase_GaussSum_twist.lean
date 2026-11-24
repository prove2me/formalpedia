-- Prove2me | solution 1 for GlobalTheory.Phase.GaussSum.twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:26:01.753912+00:00
-- url     : https://prove2.me/submissions/71ef3bd1-f00d-4ed5-bad9-a372b84a3f96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.GaussSum
namespace GlobalTheory.Phase.GaussSum
theorem _root_.solution {N W : Type} [AddCommGroup N] [Fintype N] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (Q : N → W) (B : N →+ N →+ W) (hQ : ∀ x y, Q (x + y) = Q x + Q y + B x y) (ψ : N →+ W)
    (hT : ∑ x, e (Q x) = ∑ x, e (ψ x - Q x)) :
    ∑ x, e (Q x) = 0 ∨ ∃ a, ∑ x, e (Q x) = e (Q a) * conj (∑ x, e (Q x)) := by
  by_cases hz : ∑ x, e (Q x) = 0
  · exact Or.inl hz
  right
  have hsq : (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) := by
    calc (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ x, e (ψ x - Q x) * ∑ y, e (Q y) := by
          rw [← Finset.sum_mul, ← hT]
      _ = ∑ x, ∑ z, e (Q z) * e (ψ x + B x z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Equiv.sum_comp (Equiv.addLeft x), Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [← he, ← he, Equiv.coe_addLeft, hQ]
          congr 1
          abel
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
  have hne : ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) ≠ 0 := hsq ▸ mul_ne_zero hz hz
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have ha' := right_ne_zero_of_mul ha
  have h1 : ∀ y, e (ψ y + B y a) = 1 := by
    intro y
    have : ∑ x, e (ψ x + B x a) = e (ψ y + B y a) * ∑ x, e (ψ x + B x a) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addLeft y)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← he, Equiv.coe_addLeft]
      congr 1
      simp only [map_add, AddMonoidHom.add_apply]
      abel
    exact (mul_eq_right₀ ha').1 this.symm
  refine ⟨a, ?_⟩
  conv_lhs => rw [hT]
  rw [map_sum, ← Equiv.sum_comp (Equiv.addRight a) (fun x => conj (e (Q x))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hc, ← he, Equiv.coe_addRight, hQ, ← mul_one (e (Q a + _)), ← h1 x, ← he]
  congr 1
  abel
end GlobalTheory.Phase.GaussSum
