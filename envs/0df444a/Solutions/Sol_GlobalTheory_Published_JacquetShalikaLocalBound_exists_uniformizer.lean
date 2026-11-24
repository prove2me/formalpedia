-- Prove2me | solution 1 for GlobalTheory.Published.JacquetShalikaLocalBound.exists_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:57.864573+00:00
-- url     : https://prove2.me/submissions/b8cf3943-978c-4f13-807c-94c5121e3f04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__NotIsGenericDetRepTwo_461173a5118a9903

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Whittaker
open GlobalTheory.Published.JacquetShalikaLocalBound
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.Published.JacquetShalikaLocalBound
theorem _root_.solution : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩
end GlobalTheory.Published.JacquetShalikaLocalBound
