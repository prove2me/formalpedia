-- Prove2me | solution 1 for GlobalTheory.T.fixed_vectors_irreducible_subrep_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:17:46.619779+00:00
-- url     : https://prove2.me/submissions/6d05b2f0-c937-4c22-859d-b5503229d60e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FixedVectorsIrreducibleSubrepDecomposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FixedVectorsIrreducibleSubrepDecompositionStatement
import Theorems.Thm_GlobalTheory_AbsDec_fixed_decomposition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Set G) (F : Submodule ℂ V), (∀ v, v ∈ F ↔ ∀ k ∈ K, ρ k v = v) → ∀ 𝒜 : Set (Submodule ℂ V), (∀ P ∈ 𝒜, P ≠ ⊥ ∧ (∀ g, ∀ v ∈ P, ρ g v ∈ P) ∧ ∀ W : Submodule ℂ V, W ≤ P → (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = P) → FiniteDimensional ℂ ((⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V)) → ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ V), (∀ i, π i ∈ 𝒜 ∧ π i ⊓ F ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ F) ∧ (⨆ i, π i ⊓ F) = (⨆ P ∈ 𝒜, P ⊓ F) ∧ ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → ∃ i, ∃ T : V →ₗ[ℂ] V, (∀ v ∈ P, T v ∈ π i) ∧ (∀ v ∈ P, T v = 0 → v = 0) ∧ ∀ g, ∀ v ∈ P, T (ρ g v) = ρ g (T v) := by
  first | exact @GlobalTheory.AbsDec.fixed_decomposition | exact GlobalTheory.AbsDec.fixed_decomposition | (intros; apply GlobalTheory.AbsDec.fixed_decomposition <;> assumption)
end _root_.GlobalTheory.T
