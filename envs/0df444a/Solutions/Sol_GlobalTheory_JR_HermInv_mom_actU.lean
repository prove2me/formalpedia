-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mom_actU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:33:45.055364+00:00
-- url     : https://prove2.me/submissions/b4c297d8-38b6-4a97-b18f-756efaa2b25a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_starU_mul
import Theorems.Thm_GlobalTheory_JR_HermInv_unit_conj_pow
import Theorems.Thm_GlobalTheory_JR_HermInv_unit_form

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
theorem _root_.solution (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (k : ℕ) :
    mom (actU g X).toGl k = mom X.toGl k := by
  show star (g.1 *ᵥ X.2.1) ⬝ᵥ ((g.1 * X.1.1 * star g.1) ^ k *ᵥ (g.1 *ᵥ X.2.1)) = star X.2.1 ⬝ᵥ (X.1.1 ^ k *ᵥ X.2.1)
  rw [unit_conj_pow, mulVec_mulVec, mul_assoc, mul_assoc, starU_mul g, mul_one,
    ← mulVec_mulVec, unit_form]
end GlobalTheory.JR.HermInv
