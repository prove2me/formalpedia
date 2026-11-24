-- Prove2me | solution 1 for GlobalTheory.LinSchur.mem_latt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:35.992499+00:00
-- url     : https://prove2.me/submissions/6c9b290a-c82b-4237-9927-29e804ae285f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LinSchur
variable {k : Type} [Field k] [ValuativeRel k]
namespace GlobalTheory.LinSchur
theorem _root_.solution {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k} {Y : Matrix (Fin n) (Fin d) k} :
    Y ∈ latt ψ0 n d s ↔ ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1 := Iff.rfl
end GlobalTheory.LinSchur
