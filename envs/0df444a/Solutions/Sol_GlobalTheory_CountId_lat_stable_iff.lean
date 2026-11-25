-- Prove2me | solution 1 for GlobalTheory.CountId.lat_stable_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:23.389857+00:00
-- url     : https://prove2.me/submissions/ad3b7961-bae6-446c-9b50-be826f8377bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_GlobalTheory_CountId_mem_lat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]
variable (O : Type) [CommRing O] [Algebra O E] [Module O V] [IsScalarTower O E V]
variable [IsDomain O] [Module.IsTorsionFree O E]
namespace GlobalTheory.CountId
theorem _root_.solution (e : Basis (Fin n) E V) (T : V →ₗ[E] V) :
    (∀ y ∈ lat O e, T y ∈ lat O e) ↔ ∀ i j, LinearMap.toMatrix e e T i j ∈ (algebraMap O E).range := by
  constructor
  · intro h i j
    rw [LinearMap.toMatrix_apply]
    exact (mem_lat O e _).1 (h _ (by unfold lat; exact Submodule.subset_span ⟨j, rfl⟩)) i
  · intro h y hy
    rw [mem_lat] at hy ⊢
    intro i
    rw [← LinearMap.toMatrix_mulVec_repr e e T y]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hy j)
end GlobalTheory.CountId
