-- Prove2me | solution 1 for GlobalTheory.Chow.IsBlockHomogeneous.rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:40:49.519478+00:00
-- url     : https://prove2.me/submissions/08c2d359-0eb4-4cfa-ba14-7d57e673fcd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_isBlockHomogeneous_iff
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']
namespace GlobalTheory.Chow
namespace IsBlockHomogeneous
theorem _root_.solution [Fintype σ] (e : β ≃ β') {f : MvPolynomial (β × σ) K}
    {a : β → ℕ} (h : IsBlockHomogeneous f a) :
    IsBlockHomogeneous (rename (Prod.map e id) f) (a ∘ e.symm) := by
  classical
  rw [isBlockHomogeneous_iff] at h ⊢
  intro d hd i
  have hinj : Function.Injective (Prod.map e id : β × σ → β' × σ) :=
    e.injective.prodMap Function.injective_id
  rw [support_rename_of_injective hinj, Finset.mem_image] at hd
  obtain ⟨c, hc, rfl⟩ := hd
  rw [Function.comp_apply, ← h c hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := Finsupp.mapDomain_apply hinj c (e.symm i, j)
  simpa using this
end IsBlockHomogeneous
end GlobalTheory.Chow
