-- Prove2me | solution 1 for GlobalTheory.LinSchurLatt.valuation_natCast_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:45:05.955063+00:00
-- url     : https://prove2.me/submissions/f506ae32-4093-4cdb-98a4-1497d0ee0c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.LinSchurLatt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LinSchurLatt
theorem _root_.solution (m : ℕ) : valuation k (m : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (natCast_mem (valuation k).integer m)
end GlobalTheory.LinSchurLatt
