-- Prove2me | solution 1 for GlobalTheory.exists_finset_mem_range_map_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:44.593842+00:00
-- url     : https://prove2.me/submissions/2ec228b1-a66a-4397-b1ec-d95ba452f56b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open Algebra.TensorProduct
namespace GlobalTheory
theorem _root_.solution {F A K : Type*} [Field F] [CommRing A] [Algebra F A]
    [Field K] [Algebra F K] (x : A ⊗[F] K) :
    ∃ T : Finset K, ∀ R : Subalgebra F K, (↑T : Set K) ⊆ (R : Set K) →
      x ∈ (Algebra.TensorProduct.map (AlgHom.id F A) R.val).range := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun R _ ↦ Subalgebra.zero_mem _⟩
  | tmul a k =>
    refine ⟨{k}, fun R hR ↦ ⟨a ⊗ₜ ⟨k, hR (by simp)⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    refine ⟨T₁ ∪ T₂, fun R hR ↦ Subalgebra.add_mem _ (h₁ R ?_) (h₂ R ?_)⟩
    · exact fun z hz ↦ hR (by simp [hz])
    · exact fun z hz ↦ hR (by simp [hz])
end GlobalTheory
