-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mulBm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:46.97588+00:00
-- url     : https://prove2.me/submissions/227ddc96-a244-44b8-816b-62f56111dc8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ} {K : Type} [CommRing K]
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (Y : Gl r K) (k : ℕ) : Y.2.2.1 ᵥ* (Y.1 ^ k * Bm Y) = fun j : Fin r => mom Y (k + j) := by
  funext j
  have : (Y.1 ^ k * Bm Y) = Matrix.of fun i (j : Fin r) => ((Y.1 ^ (k + (j : ℕ))) *ᵥ Y.2.1) i := by
    ext i j
    simp only [mul_apply, Bm, of_apply, pow_add, ← mulVec_mulVec]
    rfl
  rw [this]
  simp only [vecMul, mom, dotProduct, of_apply]
end GlobalTheory.JR.HermInv
