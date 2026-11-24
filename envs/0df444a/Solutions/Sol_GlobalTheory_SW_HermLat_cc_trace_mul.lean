-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.cc_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:44:32.072932+00:00
-- url     : https://prove2.me/submissions/017f0e26-9042-4192-90f2-98fe93c2e854

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
import Theorems.Thm_GlobalTheory_SW_HermLat_cc_trace
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul


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
theorem _root_.solution {N : ℕ} (X Y : HermSub E N) : cc (X.1 * Y.1).trace = (X.1 * Y.1).trace := by
  have hX : ccT X.1 = X.1 := X.2
  have hY : ccT Y.1 = Y.1 := Y.2
  rw [cc_trace, Base.ccT_mul, hX, hY, trace_mul_comm]
end GlobalTheory.SW.HermLat
