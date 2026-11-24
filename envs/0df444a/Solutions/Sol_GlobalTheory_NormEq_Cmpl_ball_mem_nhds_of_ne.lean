-- Prove2me | solution 1 for GlobalTheory.NormEq.Cmpl.ball_mem_nhds_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:49.159688+00:00
-- url     : https://prove2.me/submissions/5d0ec8dd-cb46-4612-bc6e-992a78d2e6ca

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.NormEq GlobalTheory.NormEq.Cmpl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq.Cmpl
theorem _root_.solution {x c : L} (hc : c ≠ 0) : {y | Valued.v (y - x) < Valued.v c} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c ≠ 0 := by simp [hc]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩
end GlobalTheory.NormEq.Cmpl
