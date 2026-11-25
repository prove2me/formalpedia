-- Prove2me | solution 1 for GlobalTheory.GradedBezout.ringKrullDim_quotient_of_mem_minimalPrimes_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:59:26.653882+00:00
-- url     : https://prove2.me/submissions/7dad14d4-7acf-4c8c-b655-f4d4305cf7d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup


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
omit hx [GradedAlgebra 𝒜]
namespace GlobalTheory.GradedBezout
theorem _root_.solution {P Q : Ideal T} [P.IsPrime] {r : ℕ}
    (hr : ringKrullDim (T ⧸ P) = (r + 1 : ℕ)) {f : T} (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : ringKrullDim (T ⧸ Q) = r := by
  haveI := finiteType hfin
  obtain ⟨δ, hδ⟩ := exists_ringKrullDim_quotient_eq_nat hfin hQ.1.1.ne_top
  have h1 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup K hfP hQ
  rw [hr, hδ] at h1
  have : δ + 1 = r + 1 := by exact_mod_cast h1
  rw [hδ, show δ = r by omega]
end GlobalTheory.GradedBezout
