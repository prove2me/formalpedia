-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.cls_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:35.45208+00:00
-- url     : https://prove2.me/submissions/cbc39847-3a1b-4b52-ab71-ce61fe4a2556

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {G : Type} [Group G] {P Δ Γ : Subgroup G}
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {a b : Γ} : (cls a : Cos P Γ) = cls b ↔ (b : G) * (a : G)⁻¹ ∈ P := by
  unfold cls
  rw [Quotient.eq]
  show QuotientGroup.rightRel _ a b ↔ _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp
end GlobalTheory.CompanionTheory.RgEis
