-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.piQ_jQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:15.559316+00:00
-- url     : https://prove2.me/submissions/f43f6346-2f78-4a70-92c6-157e4e473689

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
variable (A : Ad E R) (ε : ℤˣ)
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (h : ∀ x, A.σ (A.σ x) = x) (m : GL ι R) : piQ A ε (jQ A ε h m) = m :=
  Units.ext (by
    show (fromBlocks (m : Matrix ι ι R) 0 0 (((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map A.σ)).toBlocks₁₁ = m
    simp)
end GlobalTheory.CompanionTheory.RgEisLevi
