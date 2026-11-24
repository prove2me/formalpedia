-- Prove2me | solution 1 for GlobalTheory.CountId.lat_tw_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:55.706145+00:00
-- url     : https://prove2.me/submissions/1f0fe916-939f-495b-9c02-a513ef1eb616

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_GlobalTheory_CountId_repr_tw_apply
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
theorem _root_.solution (e : Basis (Fin n) E V) (γ : GL (Fin n) E) :
    lat O (tw e γ) ≤ lat O e ↔
      ∀ i j, ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range := by
  rw [show lat O (tw e γ) = Submodule.span O (Set.range (tw e γ)) from rfl, Submodule.span_le]
  constructor
  · intro h i j
    have hj := (mem_lat O e (tw e γ j)).1 (h ⟨j, rfl⟩) i
    rwa [repr_tw_apply] at hj
  · rintro h _ ⟨j, rfl⟩
    exact (mem_lat O e _).2 fun i => by rw [repr_tw_apply]; exact h i j
end GlobalTheory.CountId
