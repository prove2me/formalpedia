-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.form_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:49.15425+00:00
-- url     : https://prove2.me/submissions/10d60a43-2417-4446-bcb3-81cef247625b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_conjT_eq

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
theorem _root_.solution (A : Matrix (Fin r) (Fin r) E) (hA : IsSelfAdjoint A) (v w : Fin r → E) (k : ℕ) :
    star (A ^ k *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (A ^ k *ᵥ w) := by
  rw [Matrix.star_mulVec, ← dotProduct_mulVec, Matrix.conjTranspose_pow, conjT_eq A hA]
end GlobalTheory.JR.HermInv
