-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PolyGaussSchwartz.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:59.174031+00:00
-- url     : https://prove2.me/submissions/e2943bcf-c8dd-4f74-a674-8f766c2c073e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss
import Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_exists_schwartz_poly_mul_gauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PolyGaussSchwartz
variable {m n : ℕ}
namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz
theorem _root_.solution : ∀ (m n : ℕ) (P : MvPolynomial (Fin m × Fin n × Bool) ℂ), ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
    ⇑φ = fun u => MvPolynomial.eval (fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) P *
      Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) :=
  exists_schwartz_poly_mul_gauss
end GlobalTheory.CompanionTheory.PolyGaussSchwartz
