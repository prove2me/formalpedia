-- Prove2me | solution 1 for GlobalTheory.SemilinearExt.carries_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:04:17.783827+00:00
-- url     : https://prove2.me/submissions/ceb28c3e-bc84-44f5-9140-d1d17c23a204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SemilinearExtensionBases
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open Module
open GlobalTheory GlobalTheory.SemilinearExt
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
namespace GlobalTheory.SemilinearExt
theorem _root_.solution {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] {σ : L →+* L'} (e : V →ₛₗ[σ] V') {n : ℕ} (B : Basis (Fin n) L V) (C : Basis (Fin n) L' V')
    (h : ∀ k, e (B k) = C k) {ι : Type} (b : Basis ι L V) : ∃ c : Basis ι L' V', ∀ i, c i = e (b i) := by
  classical
  have : Module.Finite L V := Module.Finite.of_basis B
  have : Module.Finite L' V' := Module.Finite.of_basis C
  have : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  have hspan : ⊤ ≤ Submodule.span L' (Set.range fun i => e (b i)) := by
    rw [← C.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [← h k, ← b.sum_repr (B k), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card ι = finrank L' V' := by
    rw [finrank_eq_card_basis C, ← finrank_eq_card_basis B, finrank_eq_card_basis b]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, fun i => by simp⟩
end GlobalTheory.SemilinearExt
