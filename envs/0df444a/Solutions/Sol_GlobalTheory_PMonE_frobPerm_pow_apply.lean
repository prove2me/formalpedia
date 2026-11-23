-- Prove2me | solution 1 for GlobalTheory.PMonE.frobPerm_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:04.941464+00:00
-- url     : https://prove2.me/submissions/b971cfdf-c82b-48f5-b928-f6fc6a23286f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE
theorem _root_.solution (n : ℕ) (x : F) : (frobPerm (F := F) p ^ n) x = x ^ p ^ n := by
  rw [Equiv.Perm.coe_pow]
  have : (⇑(frobPerm (F := F) p)) = frobenius F p := by
    funext y; simp [frobPerm]
  rw [this, iterate_frobenius]
end GlobalTheory.PMonE
