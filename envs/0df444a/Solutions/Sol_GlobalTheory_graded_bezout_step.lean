-- Prove2me | solution 1 for GlobalTheory.graded_bezout_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:39.415947+00:00
-- url     : https://prove2.me/submissions/e47b1e6f-0c8e-47d0-8c0a-93955f2bdee7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_GradedBezout_ringKrullDim_quotient_eq_natDegree_add_one
import Theorems.Thm_GlobalTheory_GradedBezout_exists_pos_nat_gradedQuotDeg_eq
import Theorems.Thm_GlobalTheory_GradedBezout_ringKrullDim_quotient_of_mem_minimalPrimes_sup
import Theorems.Thm_GlobalTheory_GradedBezout_sum_gradedQuotDeg_le
import Theorems.Thm_GlobalTheory_isHomogeneous_of_mem_minimalPrimes


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
open GradedBezout
namespace GlobalTheory
theorem _root_.solution [GradedAlgebra 𝒜] {ι : Type*} [Finite ι] (x : ι → T)
    (hx : ∀ i, x i ∈ 𝒜 1) (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T) :
    (∀ J : Ideal T, J.IsHomogeneous 𝒜 →
      IsHilbertPoly (gradedQuotPiece 𝒜 J) (gradedQuotHilbertPoly 𝒜 J)) ∧
    ∀ (P : Ideal T) (r : ℕ), P.IsPrime → P.IsHomogeneous 𝒜 → (∃ i, x i ∉ P) →
      (gradedQuotHilbertPoly 𝒜 P).natDegree = r →
      (ringKrullDim (T ⧸ P) = (r + 1 : ℕ) ∧ ∃ D : ℕ, 1 ≤ D ∧ gradedQuotDeg 𝒜 r P = D) ∧
      ∀ (a : ℕ) (f : T), f ∈ 𝒜 a → f ∉ P →
        (P ⊔ Ideal.span {f}).minimalPrimes.Finite ∧
        (∀ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
          Q.IsHomogeneous 𝒜 ∧ ringKrullDim (T ⧸ Q) = r) ∧
        (1 ≤ r →
          (∀ Q ∈ relevantMinimalPrimes x (P ⊔ Ideal.span {f}),
            (gradedQuotHilbertPoly 𝒜 Q).natDegree = r - 1) ∧
          ∑ᶠ Q ∈ relevantMinimalPrimes x (P ⊔ Ideal.span {f}), gradedQuotDeg 𝒜 (r - 1) Q ≤
            a * gradedQuotDeg 𝒜 r P) := by
  refine ⟨fun J hJ => isHilbertPoly hx hfin hJ, fun P r hp hP hi hr => ?_⟩
  have hdim := ringKrullDim_quotient_eq_natDegree_add_one hx hfin hP hi
  rw [hr] at hdim
  refine ⟨⟨hdim, exists_pos_nat_gradedQuotDeg_eq hx hfin hP hdim⟩, fun a f hf hfP => ?_⟩
  haveI := isNoetherianRing hfin
  have hfinite := (P ⊔ Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hQ : ∀ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
      Q.IsHomogeneous 𝒜 ∧ ringKrullDim (T ⧸ Q) = r := fun Q hQ =>
    ⟨isHomogeneous_of_mem_minimalPrimes _ (isHomogeneous_sup_span hP hf) hQ,
      ringKrullDim_quotient_of_mem_minimalPrimes_sup hfin hdim hfP hQ⟩
  refine ⟨hfinite, hQ, fun h1 => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, r = e + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine ⟨fun Q h => ?_, ?_⟩
  · haveI := h.1.1.1
    exact natDegree_eq_of_degree_eq_some
      (degree_hilbertPoly_eq_of_isPrime hx hfin (hQ Q h.1).1 (hQ Q h.1).2)
  · have h2 : (relevantMinimalPrimes x (P ⊔ Ideal.span {f})).Finite :=
      hfinite.subset fun _ h => h.1
    rw [finsum_mem_eq_finite_toFinset_sum _ h2]
    exact sum_gradedQuotDeg_le hx hfin hP hdim hf hfP _ fun Q h => (h2.mem_toFinset.1 h).1
end GlobalTheory
