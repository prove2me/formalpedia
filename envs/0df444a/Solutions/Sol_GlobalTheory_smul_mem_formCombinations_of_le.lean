-- Prove2me | solution 1 for GlobalTheory.smul_mem_formCombinations_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:51.797502+00:00
-- url     : https://prove2.me/submissions/1c9575c9-ab13-4b21-8ae8-3874bcee0d17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ ι R : Type*} [CommRing R]
variable [Fintype ι]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial σ R)}
    {F : ι → MvPolynomial σ R} {a : R} {e d₀ : ℕ} (he : e ≤ d₀)
    (h : ∀ p : MvPolynomial σ R, p.IsHomogeneous d₀ → a • p ∈ formCombinations I F (d₀ - e))
    {d : ℕ} (hd : d₀ ≤ d) (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    a • p ∈ formCombinations I F (d - e) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hp' : p ∈ homogeneousSubmodule σ R d₀ * homogeneousSubmodule σ R c := by
    rwa [← homogeneousSubmodule_one_pow R d₀, ← homogeneousSubmodule_one_pow R c, ← pow_add,
      homogeneousSubmodule_one_pow]
  clear hp
  induction hp' using Submodule.mul_induction_on' with
  | mem_mul_mem x hx y hy =>
    obtain ⟨G, hG, hπ⟩ := h x hx
    refine ⟨fun i => G i * y, fun i => ?_, ?_⟩
    · have := (hG i).mul hy
      rwa [show d₀ - e + c = d₀ + c - e by omega] at this
    · convert I.mul_mem_right y hπ using 1
      simp only [sub_mul, Finset.sum_mul, mul_assoc, smul_mul_assoc]
  | add x _ y _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
end GlobalTheory
