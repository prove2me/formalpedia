-- Prove2me | solution 1 for GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:36.613424+00:00
-- url     : https://prove2.me/submissions/526c27b3-b283-4bf1-9c55-fb9418a37cd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
import Theorems.Thm_GlobalTheory_CofactorOrder_exists_diag
import Theorems.Thm_GlobalTheory_CofactorOrder_mulVec_eq_zero_of_det
import Theorems.Thm_GlobalTheory_CofactorOrder_ker_eq_bot_of_det
import Theorems.Thm_GlobalTheory_CofactorOrder_card_le_finrank
import Theorems.Thm_GlobalTheory_CofactorOrder_exists_coeff_adjugate_ne_zero
import Theorems.Thm_GlobalTheory_CofactorOrder_map_coeff_mul
import Theorems.Thm_GlobalTheory_CofactorOrder_diag_case

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open CofactorOrder
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (a m : ℕ)
    (Ψ : Matrix (Fin a) (Fin a) (Polynomial K))
    (H : ∀ x0 x1 : Fin (1 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0)
    (hν : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m + 1)
    (ha : a ≠ 0) :
    ∃ b c, ¬ (Polynomial.X : Polynomial K) ^ (2 * m + 1) ∣ Ψ.adjugate b c := by
  classical
  have : Nonempty (Fin a) := ⟨⟨0, Nat.pos_of_ne_zero ha⟩⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨b, c, hbc⟩ := exists_coeff_adjugate_ne_zero Ψ (by simpa using hν)
    exact ⟨b, c, by simpa using hbc⟩
  obtain ⟨P, Q, D, hP, hQ, hPQ⟩ := exists_diag (Ψ.map fun p => p.coeff 0)
  have hΘ0 : ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0) = diagonal D := by
    rw [map_coeff_mul]; exact hPQ
  have hz := card_le_finrank hP hQ hPQ
  have HΘ : ∀ x0 x1 : Fin (1 + 1) → Fin a → K,
      (∀ j, ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
        ((P.map C * Ψ * Q.map C).map fun p => p.coeff 1).mulVec (x0 j) +
          ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0 := by
    intro x0 x1 hx hli
    refine H (fun j => Q *ᵥ x0 j) (fun j => Q *ᵥ x1 j) (fun j => ?_)
      (hli.map' Q.mulVecLin (ker_eq_bot_of_det hQ))
    obtain ⟨h0, h1⟩ := hx j
    rw [map_coeff_mul] at h0 h1
    rw [map_coeff_mul] at h1
    constructor
    · apply mulVec_eq_zero_of_det hP
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc] using h0
    · apply mulVec_eq_zero_of_det hP
      simpa only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc] using h1
  obtain ⟨b, c, hbc⟩ := diag_case _ D hΘ0 HΘ
  by_contra hcon
  push Not at hcon
  apply hbc
  have hle : Fintype.card {i // D i = 0} + 1 ≤ 2 * m + 1 := by omega
  refine (pow_dvd_pow X hle).trans ?_
  rw [adjugate_mul_distrib, adjugate_mul_distrib, ← Matrix.mul_assoc]
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => Dvd.dvd.mul_right
    (Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hcon k l) _) _
end GlobalTheory
