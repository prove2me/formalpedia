-- Prove2me | solution 1 for GlobalTheory.ClassParam.exists_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:19.346777+00:00
-- url     : https://prove2.me/submissions/ea262b28-1abf-45eb-9da7-455f6733e142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_mem_UJ_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)
namespace GlobalTheory.ClassParam
theorem _root_.solution (J : Matrix (Fin r) (Fin r) A) (t : (Fin r → A) ≃ₗ[A] (Fin r → A))
    (ht : ∀ x y, hform σ J (t x) (t y) = hform σ J x y) :
    ∃ g : UJ σ J, ∀ u, ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ u = t u := by
  let g : GL (Fin r) A := ⟨LinearMap.toMatrix' t.toLinearMap, LinearMap.toMatrix' t.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : ∀ u, (g : Matrix (Fin r) (Fin r) A) *ᵥ u = t u := fun u => by
    simp [g, LinearMap.toMatrix'_mulVec]
  exact ⟨⟨g, (mem_UJ_iff σ J g).2 fun x y => by rw [hg, hg, ht]⟩, hg⟩
end GlobalTheory.ClassParam
