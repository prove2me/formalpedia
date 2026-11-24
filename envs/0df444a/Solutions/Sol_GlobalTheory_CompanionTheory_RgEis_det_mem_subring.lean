-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.det_mem_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:16.271949+00:00
-- url     : https://prove2.me/submissions/5a043f63-3f5f-4200-886e-f3954addd251

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockDeterminantLaw

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
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (O : Subring R) (m : Matrix κ κ R)
    (h : ∀ r c, m r c ∈ O) : m.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => h _ _)
end GlobalTheory.CompanionTheory.RgEis
