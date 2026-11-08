-- Prove2me | solution 1 for LindenReversibility.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:44:56.105053+00:00
-- url     : https://prove2.me/submissions/8de12394-14f5-412e-9f82-0e8d147306eb

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_LindenReversibility_liftA
import Definitions.Def_LindenReversibility_IsKrausFamily

open QAlgorithms (act traceLeft pureDensity)
open scoped Matrix

namespace Aux_Linden8

lemma sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ p, ∑ q, f i j p q = ∑ p, ∑ q, ∑ i, ∑ j, f i j p q := by
  calc ∑ i, ∑ j, ∑ p, ∑ q, f i j p q = ∑ i, ∑ p, ∑ j, ∑ q, f i j p q :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ p, ∑ q, ∑ j, f i j p q :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p _ => Finset.sum_comm))
    _ = ∑ p, ∑ i, ∑ q, ∑ j, f i j p q := Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ i, ∑ j, f i j p q := Finset.sum_congr rfl (fun p _ => Finset.sum_comm)

end Aux_Linden8

open LindenReversibility in
theorem solution {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ψ : EuclideanSpace ℂ (A × (B × C))) (hψ : ‖ψ‖ = 1)
    {n : ℕ} (K : Fin n → Matrix A A ℂ) (hK : IsKrausFamily K) :
    ∑ k, traceLeft (pureDensity (act (liftA (K k)) ψ)) = traceLeft (pureDensity ψ) := by
  have hact : ∀ k a s, (act (liftA (K k)) ψ) (a, s) = ∑ a1, K k a a1 * ψ (a1, s) := by
    intro k a s
    show ∑ j, liftA (K k) (a, s) j * WithLp.ofLp ψ j = ∑ a1, K k a a1 * WithLp.ofLp ψ (a1, s)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a1 _ => ?_)
    show ∑ y, K k a a1 * (1 : Matrix (B × C) (B × C) ℂ) s y * WithLp.ofLp ψ (a1, y)
      = K k a a1 * WithLp.ofLp ψ (a1, s)
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hKe : ∀ a2 a1, ∑ k, ∑ a, star (K k a a2) * K k a a1 = (1 : Matrix A A ℂ) a2 a1 := by
    intro a2 a1
    rw [← hK, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.mul_apply]
    rfl
  ext s s'
  simp only [traceLeft, pureDensity, Matrix.of_apply, Matrix.sum_apply, hact]
  simp only [starRingEnd_apply, star_sum, star_mul', Finset.sum_mul_sum]
  rw [Aux_Linden8.sum4]
  have e : ∀ a1 a2, ∑ k, ∑ a, K k a a1 * ψ (a1, s) * (star (K k a a2) * star (ψ (a2, s')))
      = ψ (a1, s) * star (ψ (a2, s')) * (1 : Matrix A A ℂ) a2 a1 := by
    intro a1 a2
    rw [← hKe a2 a1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  simp only [e, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
