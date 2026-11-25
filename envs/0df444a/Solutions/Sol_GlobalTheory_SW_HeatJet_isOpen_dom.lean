-- Prove2me | solution 1 for GlobalTheory.SW.HeatJet.isOpen_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:20.873428+00:00
-- url     : https://prove2.me/submissions/2b4245e3-1251-4f40-8b2d-db411e808906

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PolyDerivPairingEqZeroOfIsHeat
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_posDef_eventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatJet
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
namespace GlobalTheory.SW.HeatJet
theorem _root_.solution : IsOpen {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => Filter.eventually_all.2 fun τ =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
      (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => imH ((p.1 : CM Ψ N N) τ)) (fun i j => ?_)
      (fun p => ?_) x0 (hx0 τ)
  · change Continuous fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
      (2 * I)⁻¹ * (p.1 τ i j - star (p.1 τ j i))
    fun_prop
  · ext i j
    change star ((2 * I)⁻¹ * (p.1 τ j i - star (p.1 τ i j))) =
      (2 * I)⁻¹ * (p.1 τ i j - star (p.1 τ j i))
    simp
    ring
end GlobalTheory.SW.HeatJet
