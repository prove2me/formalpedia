-- Prove2me | solution 1 for GlobalTheory.Klein.DiffUnit.le_one_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:18.813903+00:00
-- url     : https://prove2.me/submissions/4b57e3cd-06d0-4f3b-b1bf-3f293711d229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein GlobalTheory.Klein.DiffUnit
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein.DiffUnit
theorem _root_.solution {s : ℂ_[p]} (h : s ^ 2 ∈ ball p) : s ∈ ball p := by
  have h' : ‖s ^ 2‖ ≤ 1 := h
  rw [norm_pow] at h'
  exact (sq_le_one_iff₀ (norm_nonneg s)).1 h'
end GlobalTheory.Klein.DiffUnit
