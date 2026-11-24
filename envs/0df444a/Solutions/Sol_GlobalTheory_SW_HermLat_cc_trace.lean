-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.cc_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:19.932953+00:00
-- url     : https://prove2.me/submissions/921087fb-23fd-46d6-be55-0ec5a58c5276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HermLat
theorem _root_.solution {N : ℕ} (X : Matrix (Fin N) (Fin N) E) : cc X.trace = (ccT X).trace := by
  simp only [Matrix.trace, diag_apply, ccT, transpose_apply, map_apply, cc, map_sum]
end GlobalTheory.SW.HermLat
