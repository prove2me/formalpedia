-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:45.576284+00:00
-- url     : https://prove2.me/submissions/21d93872-bda8-45f2-82f9-89792f38124f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
import Theorems.Thm_GlobalTheory_SW_HermLat_half_trace
import Theorems.Thm_GlobalTheory_SW_HermLat_cc_trace_mul

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
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {N : ℕ} (X Y : HermSub E N) :
    ((form E N X Y : ℚ) : ℂ) = ∑ τ : Ψ, τ.1 (X.1 * Y.1).trace :=
  half_trace hΨ (cc_trace_mul X Y)
end GlobalTheory.SW.HermLat
