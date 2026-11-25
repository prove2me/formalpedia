-- Prove2me | solution 1 for GlobalTheory.exists_mvPolynomial_of_iteratedBackwardDifferenceVanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:43.132531+00:00
-- url     : https://prove2.me/submissions/63ae9967-7c04-4c96-a964-d1788fdc49ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_DiffVanish_form_apply
import Theorems.Thm_GlobalTheory_DiffVanish_sub_form_diag
import Theorems.Thm_GlobalTheory_isHomogeneous_diffTopPoly
import Theorems.Thm_GlobalTheory_DiffVanish_eval_diffTopPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → G) (d : ℕ) : ∀ φ : G → K, DiffVanish (d + 1) φ → ∃ P : MvPolynomial ι K,
      P.totalDegree ≤ d ∧ (∀ n : ι → ℤ, P.eval (fun i ↦ (n i : K)) = φ (∑ i, n i • g i)) ∧
      MvPolynomial.homogeneousComponent d P = diffTopPoly d g φ 0 := by
  induction d with
  | zero =>
    intro φ h
    have h0 := isHomogeneous_diffTopPoly 0 g φ 0
    refine ⟨diffTopPoly 0 g φ 0, h0.totalDegree_le, fun n ↦ ?_, ?_⟩
    · rw [h.eval_diffTopPoly, h.form_apply _ (∑ i, n i • g i)]; simp
    · rw [MvPolynomial.homogeneousComponent_of_mem h0, if_pos rfl]
  | succ d ih =>
    intro φ h
    obtain ⟨Q, hQ, hQ', -⟩ := ih _ h.sub_form_diag
    have h0 := isHomogeneous_diffTopPoly (d + 1) g φ 0
    refine ⟨Q + diffTopPoly (d + 1) g φ 0, (MvPolynomial.totalDegree_add _ _).trans
      (max_le (by omega) h0.totalDegree_le), fun n ↦ ?_, ?_⟩
    · rw [map_add, hQ', h.eval_diffTopPoly]; simp
    · rw [map_add, MvPolynomial.homogeneousComponent_of_mem h0, if_pos rfl,
        MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), zero_add]
end GlobalTheory
