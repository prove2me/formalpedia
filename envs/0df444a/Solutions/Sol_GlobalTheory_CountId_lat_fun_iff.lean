-- Prove2me | solution 1 for GlobalTheory.CountId.lat_fun_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:19.499924+00:00
-- url     : https://prove2.me/submissions/dad2d9ba-9a25-4724-84ec-fcc7f5d1ecd4

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
theorem _root_.solution (e : Basis (Fin n) E V) (l : V →ₗ[E] E) :
    (∀ y ∈ lat O e, l y ∈ (algebraMap O E).range) ↔ ∀ j, l (e j) ∈ (algebraMap O E).range := by
  constructor
  · intro h j
    exact h _ (by unfold lat; exact Submodule.subset_span ⟨j, rfl⟩)
  · intro h y hy
    rw [mem_lat] at hy
    rw [← e.sum_repr y, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact Subring.mul_mem _ (hy i) (h i)
end GlobalTheory.CountId
