-- Prove2me | solution 1 for GlobalTheory.exists_finite_dvr_algHom_subset_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:10:01.497574+00:00
-- url     : https://prove2.me/submissions/e5b1f59e-6a6f-42c8-b321-2d70eede7f14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFiniteDvrExtensionEmbeddingResidueField
import Theorems.Thm_GlobalTheory_exists_finite_dvr_algHom_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
namespace GlobalTheory
theorem _root_.solution {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (s : Finset K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ (s : Set K) ⊆ Set.range e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, fun _ _ h => h, Algebra.ofId B K, ‹IsLocalHom (algebraMap B K)›, by simp⟩
  | insert θ s _ ih =>
    obtain ⟨C, _, _, _, _, _, hfin, hinj, e, hloc, hs⟩ := ih
    letI : Algebra C K := (e : C →+* K).toAlgebra
    have : IsScalarTower B C K := .of_algebraMap_eq fun b => (e.commutes b).symm
    have : IsLocalHom (algebraMap C K) := hloc
    have : Module.Finite C K := .of_restrictScalars_finite B C K
    obtain ⟨D, _, _, _, _, _, hfin', hinj', e', hloc', hθ⟩ :=
      exists_finite_dvr_algHom_mem_range (B := C) θ
    letI : Algebra B D := ((algebraMap C D).comp (algebraMap B C)).toAlgebra
    have : IsScalarTower B C D := .of_algebraMap_eq fun _ => rfl
    refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      Module.Finite.trans C D, hinj'.comp hinj, e'.restrictScalars B, hloc', ?_⟩
    rw [Finset.coe_insert]
    refine Set.insert_subset hθ fun x hx => ?_
    obtain ⟨c, rfl⟩ := hs hx
    exact ⟨algebraMap C D c, e'.commutes c⟩
end GlobalTheory
