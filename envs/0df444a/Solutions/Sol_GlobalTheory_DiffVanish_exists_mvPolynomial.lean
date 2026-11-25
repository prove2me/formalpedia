-- Prove2me | solution 1 for GlobalTheory.DiffVanish.exists_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:48.170926+00:00
-- url     : https://prove2.me/submissions/5ae81dba-fa1e-4517-b8b6-88eb3d692955

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_translate
import Theorems.Thm_GlobalTheory_DiffVanish_translate
import Theorems.Thm_GlobalTheory_DiffVanish_eval_diffTopPoly
import Theorems.Thm_GlobalTheory_exists_mvPolynomial_of_iteratedBackwardDifferenceVanish

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
namespace DiffVanish
theorem _root_.solution {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G) (x : G) : ∃ P : MvPolynomial ι K,
      P.totalDegree ≤ d ∧ (∀ n : ι → ℤ, P.eval (fun i ↦ (n i : K)) = φ (x + ∑ i, n i • g i)) ∧
      MvPolynomial.homogeneousComponent d P = diffTopPoly d g φ x ∧
      ∀ n : ι → ℤ, (MvPolynomial.homogeneousComponent d P).eval (fun i ↦ (n i : K)) =
        (d.factorial : K)⁻¹ * h.form fun _ ↦ ∑ i, n i • g i := by
  obtain ⟨P, h1, h2, h3⟩ := exists_mvPolynomial_of_iteratedBackwardDifferenceVanish g d _ (h.translate x)
  have h4 : MvPolynomial.homogeneousComponent d P = diffTopPoly d g φ x := by
    rw [h3]; simp only [diffTopPoly, multiDiff_translate, add_zero]
  exact ⟨P, h1, h2, h4, fun n ↦ by rw [h4, h.eval_diffTopPoly]⟩
end DiffVanish
end GlobalTheory
