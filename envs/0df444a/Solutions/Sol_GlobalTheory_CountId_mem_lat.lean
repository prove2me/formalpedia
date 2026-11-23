-- Prove2me | solution 1 for GlobalTheory.CountId.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:26.443631+00:00
-- url     : https://prove2.me/submissions/4037ccef-5acc-4f43-9157-5708ab8a8317

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight

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
theorem _root_.solution (e : Basis (Fin n) E V) (y : V) :
    y ∈ lat O e ↔ ∀ i, e.repr y i ∈ (algebraMap O E).range := by
  constructor
  · intro hy
    unfold lat at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      intro i
      rw [map_add, Finsupp.add_apply]
      exact Subring.add_mem _ (hx i) (hz i)
    | smul a x _ hx =>
      intro i
      rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ ⟨a, rfl⟩ (hx i)
  · intro h
    choose c hc using h
    rw [← e.sum_repr y]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hc i, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.CountId
