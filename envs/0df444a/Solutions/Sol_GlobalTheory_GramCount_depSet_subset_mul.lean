-- Prove2me | solution 1 for GlobalTheory.GramCount.depSet_subset_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:46.811714+00:00
-- url     : https://prove2.me/submissions/ab593935-67c3-4a87-a637-156f3d027bc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B]
namespace GlobalTheory.GramCount
theorem _root_.solution (c : B →+* B) {k n : ℕ} (x : Fin k → Fin n → B) (g : Fin k → B)
    (a b : B) : depSet c x g a ⊆ depSet c x g (b * a) := by
  rintro y ⟨h, s, hs⟩
  refine ⟨h, fun i => b * s i, ?_⟩
  rw [mul_smul, hs, Finset.smul_sum]
  simp [mul_smul]
end GlobalTheory.GramCount
