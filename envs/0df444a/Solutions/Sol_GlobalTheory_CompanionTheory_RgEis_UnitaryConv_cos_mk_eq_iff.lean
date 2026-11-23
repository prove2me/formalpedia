-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.UnitaryConv.cos_mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:35.448323+00:00
-- url     : https://prove2.me/submissions/75eb2a71-6aff-4563-8db8-e4ac5c4538a1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv
theorem _root_.solution {P Γ : Subgroup G} (a b : Γ) :
    (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = Quotient.mk _ b ↔
      (b : G) * (a : G)⁻¹ ∈ P := by
  constructor
  · intro h
    have h1 : b * a⁻¹ ∈ P.subgroupOf Γ := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    simpa using Subgroup.mem_subgroupOf.mp h1
  · intro h
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    apply Subgroup.mem_subgroupOf.mpr
    simpa using h
end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
