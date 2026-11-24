-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_schwartz_poly_mul_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:28:02.702839+00:00
-- url     : https://prove2.me/submissions/e1552bb3-e54a-4160-a942-d15d8fecc60f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss
import Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_eval_temperate
import Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_exists_gauss

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
theorem _root_.solution (m n : ℕ) (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑φ = fun u => MvPolynomial.eval (fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) P *
        Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  obtain ⟨g, hg⟩ := exists_gauss (m := m) (n := n)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => coord k u) P) g, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (eval_temperate P), hg, smul_eq_mul]
  rfl
end GlobalTheory.CompanionTheory.PolyGaussSchwartz
