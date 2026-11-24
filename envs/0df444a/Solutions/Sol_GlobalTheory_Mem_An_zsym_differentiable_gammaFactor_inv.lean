-- Prove2me | solution 1 for GlobalTheory.Mem.An.zsym_differentiable_gammaFactor_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:14.214058+00:00
-- url     : https://prove2.me/submissions/f8082319-cc9d-4cd8-ac63-6c44d0e3032c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
variable {q : ℕ}
namespace GlobalTheory.Mem.An
theorem _root_.solution (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (fun s => (χ.gammaFactor s)⁻¹) := by
  rcases χ.even_or_odd with h | h <;> simp only [h.gammaFactor_def]
  · exact differentiable_Gammaℝ_inv
  · exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
end GlobalTheory.Mem.An
