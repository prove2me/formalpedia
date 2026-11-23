-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.isClosed_uQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:15.657575+00:00
-- url     : https://prove2.me/submissions/b9a1d48b-7390-4899-9455-b1f9f98a203e

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
theorem _root_.solution (A : Ad E R) (ε : ℤˣ) (s : Set ι)
    (h : IsClosed (stab R (Sum.inl '' s : Set (ι ⊕ ι)) : Set (GL (ι ⊕ ι) R))) :
    IsClosed (A.uQ ε s : Set (A.U ε ι)) :=
  h.preimage continuous_subtype_val
end GlobalTheory.CompanionTheory.RgEisLevi
