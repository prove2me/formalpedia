-- Prove2me | solution 1 for GlobalTheory.GradedBezout.ringKrullDim_quotient_eq_natDegree_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:00.108422+00:00
-- url     : https://prove2.me/submissions/98e6b75c-23e0-4bb0-958e-5989cdfeb263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_GradedBezout_exists_ringKrullDim_quotient_eq_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module DirectSum
open GlobalTheory
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] (𝒜 : ℕ → Submodule K T)
open GlobalTheory.GradedBezout
variable [GradedAlgebra 𝒜]
variable {𝒜}
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
namespace GlobalTheory.GradedBezout
theorem _root_.solution {P : Ideal T} [P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) (h : ∃ i, x i ∉ P) :
    ringKrullDim (T ⧸ P) = ((gradedQuotHilbertPoly 𝒜 P).natDegree + 1 : ℕ) := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ hx hfin hI hi
  rw [natDegree_eq_of_degree_eq_some (degree_hilbertPoly_eq_of_isPrime hx hfin hI he), he]
end GlobalTheory.GradedBezout
