-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.piP_mem_kGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:25:22.16099+00:00
-- url     : https://prove2.me/submissions/2084ec65-cec4-494f-9256-144af3518d3a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_unit_corner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)))
    (hq : q.1 ∈ A.kGL (ι ⊕ ι)) : piP q ∈ A.kGL ι := by
  refine ⟨fun r c => ⟨(hq.1 _ _).1, (hq.1 _ _).2⟩, fun w => ?_⟩
  have := unit_corner _ (hq.2 w) (fun r c => by
    simp [(mem_stab_univ.1 q.2 r c).1])
  exact this
end GlobalTheory.CompanionTheory.RgEisLevi
