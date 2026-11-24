-- Prove2me | solution 1 for GlobalTheory.PolyOfDeriv.multilinear_diag_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:14.987123+00:00
-- url     : https://prove2.me/submissions/abd405fe-e88a-434a-b794-6e0a925ba332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqEvalOfDirDerivVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.PolyOfDeriv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.PolyOfDeriv
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℂ) :
    ∃ q : MvPolynomial ι ℂ, ∀ x : ι → ℝ,
      M (fun _ => x) = MvPolynomial.eval (fun i => (x i : ℂ)) q := by
  refine ⟨∑ r : Fin k → ι, MvPolynomial.C (M (fun j => Pi.single (r j) (1:ℝ))) *
    ∏ j, MvPolynomial.X (r j), ?_⟩
  intro x
  have hx : (fun _ : Fin k => x) = fun _ => ∑ i, x i • (Pi.single i (1:ℝ) : ι → ℝ) := by
    funext _; ext l; simp [Pi.single_apply]
  rw [hx, M.map_sum]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [M.map_smul_univ (fun j => x (r j)) (fun j => Pi.single (r j) 1)]
  rw [Complex.real_smul, Complex.ofReal_prod, mul_comm]
end GlobalTheory.PolyOfDeriv
