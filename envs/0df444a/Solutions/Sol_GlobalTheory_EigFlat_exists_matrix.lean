-- Prove2me | solution 1 for GlobalTheory.EigFlat.exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:54.641948+00:00
-- url     : https://prove2.me/submissions/9ec6101a-f867-43cb-b948-130188e9645d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open GlobalTheory.EigFlat
variable {A : Type} [CommRing A]
namespace GlobalTheory.EigFlat
theorem _root_.solution [IsNoetherianRing A] {I : Type} {g : ℕ} (D : I → Matrix (Fin g) (Fin g) A) :
    ∃ (n : ℕ) (H : Matrix (Fin g) (Fin n × Fin g) A), ∀ (B : Type) [CommRing B] [Algebra A B]
      (w : Fin g → B), w ᵥ* H.map (algebraMap A B) = 0 ↔
        ∀ i, w ᵥ* (D i).map (algebraMap A B) = 0 := by
  have hfg : (Submodule.span A (Set.range D)).FG := IsNoetherian.noetherian _
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine ⟨n, Matrix.of fun j p => s p.1 j p.2, fun B _ _ w => ?_⟩
  let K : Submodule A (Matrix (Fin g) (Fin g) A) :=
    { carrier := {X | w ᵥ* X.map (algebraMap A B) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro X Y hX hY
        simp only [Set.mem_setOf_eq] at hX hY ⊢
        rw [Matrix.map_add _ (map_add _), Matrix.vecMul_add, hX, hY, add_zero]
      smul_mem' := by
        intro r X hX
        simp only [Set.mem_setOf_eq] at hX ⊢
        have : (r • X).map (algebraMap A B) = algebraMap A B r • X.map (algebraMap A B) := by
          ext i j; simp
        rw [this, Matrix.vecMul_smul, hX, smul_zero] }
  have h1 : (∀ i, w ᵥ* (D i).map (algebraMap A B) = 0) ↔ Submodule.span A (Set.range D) ≤ K := by
    rw [Submodule.span_le, Set.range_subset_iff]; rfl
  have h2 : (∀ i, w ᵥ* (s i).map (algebraMap A B) = 0) ↔ Submodule.span A (Set.range s) ≤ K := by
    rw [Submodule.span_le, Set.range_subset_iff]; rfl
  rw [h1, ← hs, ← h2]
  constructor
  · intro h i
    funext j
    exact congrFun h (i, j)
  · intro h
    funext p
    exact congrFun (h p.1) p.2
end GlobalTheory.EigFlat
