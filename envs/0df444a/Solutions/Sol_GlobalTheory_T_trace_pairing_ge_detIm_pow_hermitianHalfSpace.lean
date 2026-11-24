-- Prove2me | solution 1 for GlobalTheory.T.trace_pairing_ge_detIm_pow_hermitianHalfSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:48.555938+00:00
-- url     : https://prove2.me/submissions/74c63a6f-7c73-44af-b025-3d5749838374

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpaceStatement
import Theorems.Thm_GlobalTheory_SW_TracePair_trace_ge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N c : ℕ, 0 < N → 0 < c → ∃ k : ℝ, 0 < k ∧ ∀ T : Matrix (Fin N) (Fin N) E, ccT T = T → Den c T → (∀ τ : Ψ, (T.map τ.1).PosDef) → ∀ Z ∈ Hn Ψ N, k * detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤ ∑ τ : Ψ, (T.map τ.1 * imH (Z τ)).trace.re := by
  first | exact @GlobalTheory.SW.TracePair.trace_ge | exact GlobalTheory.SW.TracePair.trace_ge | (intros; apply GlobalTheory.SW.TracePair.trace_ge <;> assumption)
end _root_.GlobalTheory.T
