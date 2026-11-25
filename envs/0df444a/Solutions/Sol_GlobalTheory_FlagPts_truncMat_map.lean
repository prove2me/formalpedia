-- Prove2me | solution 1 for GlobalTheory.FlagPts.truncMat_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:41:59.033022+00:00
-- url     : https://prove2.me/submissions/52053b48-e19c-4630-b8ca-0a6aa7425787

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TruncMatMemSubalgebra
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
namespace GlobalTheory.FlagPts
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (m : ℕ)
    (M : Matrix (Fin d) (Fin d) R) : (truncMat m M).map f = truncMat m (M.map f) := by
  ext c e
  simp only [truncMat, Matrix.map_apply]
  split_ifs <;> simp
end GlobalTheory.FlagPts
