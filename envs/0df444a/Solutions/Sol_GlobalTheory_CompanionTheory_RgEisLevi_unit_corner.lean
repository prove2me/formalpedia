-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.unit_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:24.939242+00:00
-- url     : https://prove2.me/submissions/e6afd047-9251-4983-bcf8-867f3ef1234d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet

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
theorem _root_.solution (Q : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ)
    (h0 : ∀ r c, Q (Sum.inr r) (Sum.inl c) = 0) : Q.toBlocks₁₁ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext r c
  have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hQ) (Sum.inl r)) (Sum.inl c)
  simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.star_apply, h0, Matrix.one_apply, Matrix.toBlocks₁₁] using this
end GlobalTheory.CompanionTheory.RgEisLevi
