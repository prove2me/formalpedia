-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.EventuallyPoly.of_differences
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:41.582897+00:00
-- url     : https://prove2.me/submissions/59886ce6-9a08-468d-a13d-03a6d8bdc4a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_eval_aeval_coord
import Theorems.Thm_GlobalTheory_MultiHilbert_exists_antidifference

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {r : ℕ}
namespace GlobalTheory.MultiHilbert
namespace EventuallyPoly
theorem _root_.solution {f : (Fin r → ℕ) → ℚ}
    (hf : ∀ k, EventuallyPoly (fun n => f (n + Pi.single k 1) - f n)) : EventuallyPoly f := by
  classical
  choose Φ a h using hf
  choose Ψ hΨ using fun k => exists_antidifference (Φ k) k
  set N := ∑ k, a k with hN
  have haN : ∀ k, a k ≤ N := fun k =>
    Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have step : ∀ (k : Fin r) (m : Fin r → ℕ), (∀ j, N ≤ m j) → ∀ t : ℕ, N ≤ t →
      f (Function.update m k t) - f (Function.update m k N) =
        eval (fun j => ((Function.update m k t j : ℕ) : ℚ)) (Ψ k) -
          eval (fun j => ((Function.update m k N j : ℕ) : ℚ)) (Ψ k) := by
    intro k m hm t ht
    induction t, ht using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      have h1 := h k (Function.update m k t) (fun j => by
        by_cases hj : j = k
        · subst hj
          simpa using (haN j).trans ht
        · rw [Function.update_of_ne hj]
          exact (haN k).trans (hm j))
      have h2 := hΨ k (fun j => ((Function.update m k t j : ℕ) : ℚ))
      have e1 : Function.update m k t + Pi.single k 1 = Function.update m k (t + 1) := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp
        · simp [hj]
      have e2 : Function.update (fun j => ((Function.update m k t j : ℕ) : ℚ)) k
          (((Function.update m k t k : ℕ) : ℚ) + 1) =
          fun j => ((Function.update m k (t + 1) j : ℕ) : ℚ) := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp
        · simp [hj]
      simp only [e1] at h1
      rw [e2] at h2
      linarith
  have main : ∀ s : Finset (Fin r), ∃ P : MvPolynomial (Fin r) ℚ, ∀ n : Fin r → ℕ,
      (∀ j, N ≤ n j) → f (fun j => if j ∈ s then n j else N) = eval (fun j => (n j : ℚ)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨C (f (fun _ => N)), fun n _ => by simp⟩
    | insert k s hk ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨P + aeval (fun j => if j ∈ insert k s then X j else C (N : ℚ)) (Ψ k) -
        aeval (fun j => if j ∈ s then X j else C (N : ℚ)) (Ψ k), fun n hn => ?_⟩
      have h1 := step k (fun j => if j ∈ s then n j else N)
        (fun j => by split_ifs; exacts [hn j, le_rfl]) (n k) (hn k)
      have e1 : Function.update (fun j => if j ∈ s then n j else N) k (n k) =
          fun j => if j ∈ insert k s then n j else N := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp
        · simp [hj]
      have e2 : Function.update (fun j => if j ∈ s then n j else N) k N =
          fun j => if j ∈ s then n j else N := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp [hk]
        · simp [hj]
      rw [e1, e2] at h1
      have e3 : ∀ u : Finset (Fin r), (fun j => eval (fun j => (n j : ℚ))
          (if j ∈ u then X j else C (N : ℚ) : MvPolynomial (Fin r) ℚ)) =
          fun j => (((if j ∈ u then n j else N : ℕ)) : ℚ) := by
        intro u
        funext j
        split_ifs <;> simp
      rw [map_sub, map_add, eval_aeval_coord, eval_aeval_coord, e3, e3, ← hP n hn]
      linarith
  obtain ⟨P, hP⟩ := main Finset.univ
  exact ⟨P, N, fun n hn => by simpa using hP n hn⟩
end EventuallyPoly
end GlobalTheory.MultiHilbert
