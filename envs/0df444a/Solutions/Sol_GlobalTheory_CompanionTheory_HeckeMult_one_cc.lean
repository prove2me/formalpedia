-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.one_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:46.345484+00:00
-- url     : https://prove2.me/submissions/c41ba70d-1b76-46c7-8b43-591ab8aa6f44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cl
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_lc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_ll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cc
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cl
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_lc
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_ll

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.HeckeMult
theorem _root_.solution {n : ℕ} (i j : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc j.castSucc
      = (1 : Matrix (Fin n) (Fin n) R) i j := by
  simp [Matrix.one_apply]
end GlobalTheory.CompanionTheory.HeckeMult
