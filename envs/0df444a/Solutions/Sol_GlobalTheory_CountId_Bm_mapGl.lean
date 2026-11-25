-- Prove2me | solution 1 for GlobalTheory.CountId.Bm_mapGl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:59.163654+00:00
-- url     : https://prove2.me/submissions/0d46190a-bea6-4a79-805b-aa6b33dfe5eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_P2M_GlobalTheory_CountId_map_mulVec__74df2fa150c8
import Theorems.Thm_P2M_GlobalTheory_CountId_map_pow__f545ffa1a6ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']
namespace GlobalTheory.CountId
theorem _root_.solution (φ : k →+* k') (Y : Gl r k) : Bm (mapGl φ Y) = (Bm Y).map φ := by
  ext i j
  simp only [Bm, mapGl, Matrix.of_apply, Matrix.map_apply]
  rw [← map_pow', ← map_mulVec']
end GlobalTheory.CountId
