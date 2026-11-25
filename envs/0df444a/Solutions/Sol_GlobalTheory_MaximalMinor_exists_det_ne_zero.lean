-- Prove2me | solution 1 for GlobalTheory.MaximalMinor.exists_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:06:51.580823+00:00
-- url     : https://prove2.me/submissions/132fc58f-3666-4646-ad1c-90f51cb3e6d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfDetMemNonZeroDivisors
import Theorems.Thm_GlobalTheory_MaximalMinor_det_ne_zero_of_linearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule Function
open GlobalTheory
open GlobalTheory.MaximalMinor
variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.MaximalMinor
theorem _root_.solution [IsDomain R] (b : Basis ι R F) (G : κ → F)
    (hr : Fintype.card ι ≤ finrank R (span R (Set.range G))) :
    ∃ σ : ι → κ, b.det (G ∘ σ) ≠ 0 := by
  by_contra! h
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank hr
  have hw' := (hw.comp _ (Fintype.equivFin ι).injective).map' _ (ker_subtype _)
  refine det_ne_zero_of_linearIndependent b hw' ?_
  have h0 : (b.det.compLinearMap (span R (Set.range G)).subtype).toMultilinearMap = 0 := by
    refine MultilinearMap.ext_of_span_eq_top
      (g := fun (_ : ι) (k : κ) => (⟨G k, subset_span ⟨k, rfl⟩⟩ : span R (Set.range G)))
      (fun _ => span_range_subtype_eq_top_iff _ _ |>.2 rfl) fun σ => h σ
  exact DFunLike.congr_fun h0 (w ∘ Fintype.equivFin ι)
end GlobalTheory.MaximalMinor
