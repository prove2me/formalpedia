-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.quadratic_cubic_composition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:51.583846+00:00
-- url     : https://prove2.me/submissions/d73ca6c8-fa44-4287-9882-f6e6453e63d2

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SieveComposition
import Theorems.Thm_OAI_SevenEighths_InverseMoment_bounded_coefficient_sum_sq

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution
    {K M H C P : Type*} [Fintype K] [Fintype M] [Fintype H] [Fintype C] [Fintype P]
    (q : K → M → H → ℂ) (χ : M → C → P → ℂ)
    (a : H → P → ℂ) (beta : C → M → H → ℂ) (Q S : ℝ) (hQ : 0 ≤ Q)
    (hbeta : ∀ c m h, ‖beta c m h‖ ≤ 1)
    (hquadratic : ∀ f : M → H → ℂ,
      (∑ k, ‖∑ m, ∑ h, q k m h * f m h‖ ^ 2) ≤ Q * ∑ m, ∑ h, ‖f m h‖ ^ 2)
    (hcubic : ∀ u : P → ℂ,
      (∑ m, ∑ c, ‖∑ p, u p * χ m c p‖ ^ 2) ≤ S * ∑ p, ‖u p‖ ^ 2) :
    (∑ k, ‖∑ m, ∑ h, q k m h *
      (∑ c, beta c m h * (∑ p, a h p * χ m c p))‖ ^ 2) ≤
      Q * (Fintype.card C : ℝ) * S * ∑ h, ∑ p, ‖a h p‖ ^ 2 := by
  classical
  apply (hquadratic (fun m h => ∑ c, beta c m h * (∑ p, a h p * χ m c p))).trans
  have hcauchy :
      (∑ m, ∑ h, ‖∑ c, beta c m h * (∑ p, a h p * χ m c p)‖ ^ 2) ≤
      (Fintype.card C : ℝ) * ∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2 := by
    calc
      _ ≤ ∑ m, ∑ h, (Fintype.card C : ℝ) *
          ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m _
        apply Finset.sum_le_sum
        intro h _
        exact bounded_coefficient_sum_sq _ _ (fun c => hbeta c m h)
      _ = _ := by
        simp only [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
  have hcs : (∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2) ≤
      S * ∑ h, ∑ p, ‖a h p‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun h _ => hcubic (a h)
  calc
    _ ≤ Q * ((Fintype.card C : ℝ) *
        ∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcauchy hQ
    _ ≤ Q * ((Fintype.card C : ℝ) * (S * ∑ h, ∑ p, ‖a h p‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)) hQ
    _ = _ := by ring
end OAI.SevenEighths.InverseMoment
