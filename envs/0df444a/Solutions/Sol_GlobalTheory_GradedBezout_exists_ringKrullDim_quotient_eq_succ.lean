-- Prove2me | solution 1 for GlobalTheory.GradedBezout.exists_ringKrullDim_quotient_eq_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:51:33.664466+00:00
-- url     : https://prove2.me/submissions/170127e3-f1f9-440c-8dbe-13d3419475d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup

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
theorem _root_.solution {P : Ideal T} [hP : P.IsPrime]
    (hI : P.IsHomogeneous 𝒜) {i : ι} (h : x i ∉ P) :
    ∃ e : ℕ, ringKrullDim (T ⧸ P) = (e + 1 : ℕ) := by
  obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_eq_nat hfin hP.ne_top
  have h1 := (zero_le_degree_iff.2 (hilbertPoly_ne_zero hx hfin hI h)).trans_lt
    (degree_hilbertPoly_lt hx hfin hI hδ.le)
  have h2 : 0 < δ := by exact_mod_cast h1
  exact ⟨δ - 1, by rw [hδ, Nat.sub_add_cancel h2]⟩
end GlobalTheory.GradedBezout
