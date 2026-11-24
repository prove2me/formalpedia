-- Prove2me | solution 1 for GlobalTheory.qminor_polyMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:31.28689+00:00
-- url     : https://prove2.me/submissions/3f945ce6-3058-424d-b975-d9a96742fdee

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorPolyMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory
open Finset
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (s : ℂ) :
    ∃ c : ℕ → A, ∀ u : ℂ, _root_.Formalism.REAL.qminor E a b (u - s) = ∑ i ∈ Finset.range (t + 1), u ^ i • c i := by
  classical
  let F : Equiv.Perm (Fin t) → Fin t → Polynomial A := fun σ k =>
    Polynomial.C (if a (σ k) = b k then (1 : A) else 0) * Polynomial.X +
      Polynomial.C ((if a (σ k) = b k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) +
        E (a (σ k)) (b k))
  let P : Polynomial A :=
    ∑ σ, Polynomial.C (((Equiv.Perm.sign σ : ℤ) : A)) * (List.ofFn (F σ)).prod
  have hdeg : P.natDegree < t + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_list_prod_le _).trans ?_
    have h1 : ∀ k, (F σ k).natDegree ≤ 1 := fun k =>
      (Polynomial.natDegree_add_le _ _).trans
        (max_le ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le) (by simp))
    rw [List.map_ofFn, List.sum_ofFn]
    calc ∑ k, (Polynomial.natDegree ∘ F σ) k ≤ ∑ _k : Fin t, 1 := Finset.sum_le_sum fun k _ => h1 k
      _ = t := by simp
  refine ⟨fun i => P.coeff i, fun u => ?_⟩
  have hcomm : ∀ (p : Polynomial A) (k : ℕ),
      Commute ((RingHom.id A) (p.coeff k)) (algebraMap ℂ A u) := fun p k =>
    Algebra.commute_algebraMap_right u _
  have hF : ∀ σ k, Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) (F σ k) =
      _root_.Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (a (σ k)) (b k) := by
    intro σ k
    unfold _root_.Formalism.REAL.Tm
    simp only [F, Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C,
      RingHom.id_apply]
    split_ifs with h
    · rw [one_mul, ← add_assoc, ← map_add]
      congr 2
      ring
    · simp
  have hP : Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) P = _root_.Formalism.REAL.qminor E a b (u - s) := by
    unfold _root_.Formalism.REAL.qminor
    simp only [P, Polynomial.eval₂_finset_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Polynomial.eval₂_mul_noncomm _ _ (hcomm _), Polynomial.eval₂_C,
      Polynomial.eval₂_list_prod_noncomm _ _ _ (fun p _ => hcomm p), List.map_ofFn]
    simp only [Function.comp_def, hF, RingHom.id_apply]
  rw [← hP, Polynomial.eval₂_eq_sum_range' _ hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes _ _).symm
end _root_.GlobalTheory
end GlobalTheory
