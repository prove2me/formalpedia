-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.continuous_piQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:00.397884+00:00
-- url     : https://prove2.me/submissions/58b30407-dbba-460d-b7d6-981155030e11

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
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (ε : ℤˣ) : Continuous (piQ A ε (ι := ι)) := by
  have hv : Continuous fun q : A.uQ ε (Set.univ : Set ι) => (q.1.1 : GL (ι ⊕ ι) R) :=
    continuous_subtype_val.comp continuous_subtype_val
  rw [Units.continuous_iff]
  refine ⟨continuous_matrix fun r c => ?_, continuous_matrix fun r c => ?_⟩
  · exact (Units.continuous_val.comp hv).matrix_elem _ _
  · exact (Units.continuous_val.comp hv.inv).matrix_elem _ _
end GlobalTheory.CompanionTheory.RgEisLevi
