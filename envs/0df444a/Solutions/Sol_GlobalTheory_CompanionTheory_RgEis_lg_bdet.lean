-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.lg_bdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:14:00.619041+00:00
-- url     : https://prove2.me/submissions/785875e2-47e2-43db-801e-b9e83bcc0390

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_val
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bdet_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_norm_det_blk
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_det_mem_subring
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_lg_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [Field E]
variable [TopologicalSpace R] [IsTopologicalRing R]
open Classical
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (A : Ad E R) (hA : A.GoodL) (s : Set ι) {p : GL ι R} (hp : p ∈ stab R s)
    (hk : p ∈ A.kGL ι) : A.lg (bdet s p) = 0 := by
  refine lg_eq_zero A hA _ ?_ ?_ fun w => ?_
  · rw [bdet_val s hp]
    exact det_mem_subring _ _ fun r c => (hk.1 _ _).1
  · rw [bdet_inv s hp, bdet_val s (inv_mem hp)]
    exact det_mem_subring _ _ fun r c => (hk.1 _ _).2
  · rw [bdet_val s hp, RingHom.map_det]
    refine (congrArg norm (congrArg Matrix.det ?_)).trans
      (norm_det_blk _ (hk.2 w) s fun r hr c hc => ?_)
    · ext r c; rfl
    · simp [(hp r hr c hc).1]
end GlobalTheory.CompanionTheory.RgEis
