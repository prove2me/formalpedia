-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.bdet_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:26:40.40389+00:00
-- url     : https://prove2.me/submissions/1096302e-5552-46e4-b625-3fcad63b3592

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_bdet_congr

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
theorem _root_.solution (s : Set ι) (g : GL (ι ⊕ ι) R) (m : GL ι R)
    (h : ∀ r c, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl r) (Sum.inl c) = (m : Matrix ι ι R) r c) :
    bdet (Sum.inl '' s : Set (ι ⊕ ι)) g = bdet s m :=
  bdet_congr s _ (Equiv.Set.image Sum.inl s Sum.inl_injective) g m fun a b => h a.1 b.1
end GlobalTheory.CompanionTheory.RgEisLevi
