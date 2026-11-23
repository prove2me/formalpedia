-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.isHolTo_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:48.750676+00:00
-- url     : https://prove2.me/submissions/27f67da8-4699-4b09-b6bd-9b2490172900

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution (B : Set V) (y : V → (Sp ℂ ⟶ X)) : IsHolTo B y ↔ IsOpen B ∧ HolOn B y := by
  constructor
  · intro h
    refine ⟨by simpa using (h ⊤ 0).1, fun U b hb hU => ?_⟩
    have hn : {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∈ 𝓝 b := (h U 0).1.mem_nhds ⟨hb, hU⟩
    exact ⟨Filter.Eventually.filter_mono nhdsWithin_le_nhds (Filter.mem_of_superset hn fun _ hx => hx.2),
      fun f => ((h U f).2.differentiableAt hn).differentiableWithinAt⟩
  · rintro ⟨hB, h⟩ U f
    refine ⟨isOpen_iff_mem_nhds.2 fun b hb => ?_, fun b hb => ((h U b hb.1 hb.2).2 f).mono fun _ hx => hx.1⟩
    have := (h U b hb.1 hb.2).1
    rw [hB.nhdsWithin_eq hb.1] at this
    exact Filter.inter_mem (hB.mem_nhds hb.1) this
end GlobalTheory.PeriodCompare
