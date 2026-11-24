-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.gram_hankel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:26:01.727542+00:00
-- url     : https://prove2.me/submissions/a11109d9-cd86-4a5d-8759-8edac159b1f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_mom_map
import Theorems.Thm_GlobalTheory_JR_HermInv_gram

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
theorem _root_.solution (X : Hn r F E) (a : Inv r F) (h : HasInv X a) :
    (Bm X.toGl)ᴴ * Bm X.toGl = (hankel a).map (algebraMap F E) := by
  rw [gram]
  ext i j
  simp [hankel, mom_map X a h]
end GlobalTheory.JR.HermInv
