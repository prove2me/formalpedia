-- Prove2me | solution 1 for GlobalTheory.Chow.map_mem_span_linForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:16.717153+00:00
-- url     : https://prove2.me/submissions/8b05b8d7-1edf-4918-afab-46b66bfceb20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_map_linForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {σ β : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {u : σ → R}
    {h : MvPolynomial (β × σ) R} (hh : h ∈ Ideal.span (Set.range (linForm u : β → _))) :
    map φ h ∈ Ideal.span (Set.range (linForm (fun j => φ (u j)) : β → _)) := by
  have hle : Ideal.span (Set.range (linForm u : β → _)) ≤
      (Ideal.span (Set.range (linForm (fun j => φ (u j)) : β → _))).comap (map φ) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, (map_linForm φ u i).symm⟩
  exact hle hh
end GlobalTheory.Chow
