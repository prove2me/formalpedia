-- Prove2me | solution 1 for GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:21.227741+00:00
-- url     : https://prove2.me/submissions/58b054d9-ba54-4daa-b932-7141767feafe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSemisimpleRepresentationOfISupRangeEquivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
open Matrix
open scoped Kronecker ComplexOrder TensorProduct
namespace GlobalTheory.ClassFin
namespace _root_.GlobalTheory.ClassFin
theorem _root_.solution :
    ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  intro G _ W _ _ ρ J V _ _ r p hr hp htop
  let f : ∀ j, (r j).IntertwiningMap ρ := fun j => ⟨p j, fun g => LinearMap.ext fun v => hp j g v⟩
  let F : ∀ j, (r j).asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule :=
    fun j => Representation.IntertwiningMap.equivLinearMapAsModule (r j) ρ (f j)
  have hF : ∀ j (v : V j), F j v = p j v := fun j v => rfl
  have hs : ∀ j, IsSemisimpleModule (MonoidAlgebra ℂ G) (LinearMap.range (F j)) := by
    intro j
    haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (r j)).mp
      (hr j)
    exact IsSemisimpleModule.range (F j)
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' hs ?_
  rw [eq_top_iff]
  intro x _
  have hx : (show W from x) ∈ ⨆ j, LinearMap.range (p j) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (fun j => LinearMap.range (p j))
    (motive := fun y : W => (show ρ.asModule from y) ∈ ⨆ j, LinearMap.range (F j)) hx ?_ ?_ ?_
  · rintro j y ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem j ⟨v, hF j v⟩
  · exact Submodule.zero_mem _
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz
end _root_.GlobalTheory.ClassFin
end GlobalTheory.ClassFin
