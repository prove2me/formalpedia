-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.cls_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:17.749802+00:00
-- url     : https://prove2.me/submissions/2fb567f5-32a4-4a01-9099-bc263b5573d6

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
theorem _root_.solution (q : Cos P Γ) : cls ⟨rep q, rep_mem q⟩ = q := Quotient.out_eq q
end GlobalTheory.CompanionTheory.RgEis
