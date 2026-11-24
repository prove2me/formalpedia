-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.iwa_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:27.970188+00:00
-- url     : https://prove2.me/submissions/6e144123-6559-4570-956d-6b0bf90fe7ed

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_jG_mem_k
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_mem_uQ_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_factor

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
variable [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (hA : A.Good) (ε : ℤˣ) (hI : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) (s : Set ι) :
    Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) := by
  intro g
  obtain ⟨q, hq, k, hk, rfl⟩ := hI g
  obtain ⟨p, hp, k', hk', e⟩ := hA.iwa ι s (piQ A ε ⟨q, hq⟩)
  obtain ⟨q', h1, h2⟩ := factor A ε hA.σσ ⟨q, hq⟩ p k' e
  have hjk : ((jQ A ε hA.σσ k').1 : A.U ε ι) ∈ A.uK ε ι :=
    Subgroup.mem_subgroupOf.2 (jG_mem_k A hA.σO hA.σφ k' hk')
  refine ⟨q'.1, ⟨(mem_uQ_iff A ε s q').2 (h1 ▸ hp), q'.2⟩, (jQ A ε hA.σσ k').1 * k, mul_mem hjk hk, ?_⟩
  rw [← mul_assoc, ← h2]
end GlobalTheory.CompanionTheory.RgEisLevi
