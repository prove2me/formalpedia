-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.mem_uQ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:13.894646+00:00
-- url     : https://prove2.me/submissions/ea5583f0-5eef-4a2b-b9ea-5615285b7168

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_mem_stab_inl_iff

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
theorem _root_.solution (A : Ad E R) (ε : ℤˣ) (s : Set ι) (q : A.uQ ε (Set.univ : Set ι)) :
    q.1 ∈ A.uQ ε s ↔ piQ A ε q ∈ stab R s :=
  Subgroup.mem_subgroupOf.trans (mem_stab_inl_iff s ⟨q.1.1, Subgroup.mem_subgroupOf.1 q.2⟩)
end GlobalTheory.CompanionTheory.RgEisLevi
