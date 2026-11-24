-- Prove2me | solution 1 for GlobalTheory.Chow.rename_mem_elimIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:56.172895+00:00
-- url     : https://prove2.me/submissions/6bc20286-2a87-4af0-935f-4cce4f2cc1f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_genericForm_eq
import Theorems.Thm_GlobalTheory_Chow_C_mem_incidenceIdeal
import Theorems.Thm_GlobalTheory_Chow_genericForm_mem_incidenceIdeal
import Theorems.Thm_GlobalTheory_Chow_incidenceIdeal_le
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
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution (e : β → β') {p : Ideal (MvPolynomial σ K)}
    {f : MvPolynomial (β × σ) K} (hf : f ∈ elimIdeal β p) :
    rename (Prod.map e id) f ∈ elimIdeal β' p := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨m, fun j => ?_⟩
  have hle : incidenceIdeal β p ≤ (incidenceIdeal β' p).comap
      (rename (Prod.map e id : β × σ → β' × σ) : _ →ₐ[MvPolynomial σ K] _) := by
    refine incidenceIdeal_le.2 ⟨fun g hg => ?_, fun i => ?_⟩
    · simpa [Ideal.mem_comap] using C_mem_incidenceIdeal hg
    · have := genericForm_mem_incidenceIdeal p (e i)
      simpa [Ideal.mem_comap, genericForm_eq] using this
  have := hle (hm j)
  rwa [Ideal.mem_comap, map_mul, rename_C, ← map_rename] at this
end GlobalTheory.Chow
