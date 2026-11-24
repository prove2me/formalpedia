-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.mem_stab_inl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:22.547801+00:00
-- url     : https://prove2.me/submissions/feaaecd0-4697-4b00-a593-20c55fa05e0a

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
theorem _root_.solution (s : Set ι) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι))) :
    q.1 ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι)) ↔ piP q ∈ stab R s := by
  constructor
  · intro h r hr c hc
    exact h (Sum.inl r) (by simpa using hr) (Sum.inl c) ⟨c, hc, rfl⟩
  · intro h r hr c hc
    obtain ⟨c', hc', rfl⟩ := hc
    rcases r with r | r
    · exact h r (fun hrs => hr ⟨r, hrs, rfl⟩) c' hc'
    · exact mem_stab_univ.1 q.2 r c'
end GlobalTheory.CompanionTheory.RgEisLevi
