-- Prove2me | solution 1 for GlobalTheory.tensor_pairing_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:55.488031+00:00
-- url     : https://prove2.me/submissions/231cb736-0500-4c6a-80c6-87ff7552c6df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorProductNondegeneratePairing
import Theorems.Thm_GlobalTheory_pairing_surjective_of_separating

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)]
    [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ),
    (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) →
    ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)),
      (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧
      ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by
  intro ι _ _ M N _ _ _ _ _ b hb
  refine ⟨(PiTensorProduct.dualDistrib (R := ℂ) (M := N)).compMultilinearMap
    ((PiTensorProduct.tprod ℂ).compLinearMap b), ?_, ?_⟩
  · intro v x
    simp [PiTensorProduct.dualDistrib_apply]
  · intro u hu
    let e : ∀ τ, Basis (Fin (finrank ℂ (N τ))) ℂ (N τ) := fun τ => Module.finBasis ℂ (N τ)
    let E := Basis.piTensorProduct e
    obtain ⟨k, hk⟩ : ∃ k, E.repr u k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (E.repr.injective (by ext k; simp [h k]))
    have hs : ∀ τ, ∃ v, b τ v = (e τ).coord (k τ) := fun τ =>
      pairing_surjective_of_separating (b τ) (hb τ) _
    choose v hv using hs
    refine ⟨v, ?_⟩
    have key : (PiTensorProduct.dualDistrib (R := ℂ) (M := N))
        (PiTensorProduct.tprod ℂ fun τ => b τ (v τ)) = E.coord k := by
      apply E.ext
      intro j
      simp only [hv, E, Basis.piTensorProduct_apply, PiTensorProduct.dualDistrib_apply,
        Basis.coord_apply, Basis.repr_self]
      rw [← Basis.piTensorProduct_apply, Basis.repr_self]
      simp only [Finsupp.single_apply]
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [if_neg hjk]
        obtain ⟨τ, hτ⟩ : ∃ τ, j τ ≠ k τ := by
          by_contra h; push_neg at h; exact hjk (funext h)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    simpa [key] using hk
end GlobalTheory
