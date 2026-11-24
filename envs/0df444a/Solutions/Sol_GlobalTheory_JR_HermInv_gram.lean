-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:39.660836+00:00
-- url     : https://prove2.me/submissions/d94990e6-fc2f-4452-b3ec-79d6013728d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_form_pow

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
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (X : Hn r F E) : (Bm X.toGl)ᴴ * Bm X.toGl = Matrix.of fun i j : Fin r => mom X.toGl ((i : ℕ) + j) := by
  ext i j
  have : ((Bm X.toGl)ᴴ * Bm X.toGl) i j = star (X.1.1 ^ (i : ℕ) *ᵥ X.2.1) ⬝ᵥ (X.1.1 ^ (j : ℕ) *ᵥ X.2.1) := by
    simp only [mul_apply, conjTranspose_apply, Bm, of_apply, dotProduct, Pi.star_apply]
    rfl
  rw [this, form_pow X.1.1 X.1.2, mulVec_mulVec, ← pow_add]
  rfl
end GlobalTheory.JR.HermInv
