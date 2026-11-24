-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.sum_eq_sum_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:31.80445+00:00
-- url     : https://prove2.me/submissions/47e7406f-da58-4d8f-8177-f57f1d93194b

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
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {S : Type} [AddCommMonoid S] (s : Set ι) [Fintype s] (f : ι → S)
    (h : ∀ m, m ∉ s → f m = 0) : ∑ m, f m = ∑ m : s, f m := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ s)) (by simp) f]
  exact (Finset.sum_filter_of_ne fun m _ hm => by_contra fun hs => hm (h m hs)).symm
end GlobalTheory.CompanionTheory.RgEis
