-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.exists_kProj_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:40.923847+00:00
-- url     : https://prove2.me/submissions/22712f7a-fde1-49c7-8954-be144357b414

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_apply_eq_self_iff
import Theorems.Thm_GroundTheory_Automorphic_CompactRep_isSemisimpleModule_asModule
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.CompactRep
open Module Set RestrictedTensor
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ K X}
variable (hσ : IsKFinite σ) {c : Submodule (MonoidAlgebra ℂ K) σ.asModule}
  (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule)
namespace GroundTheory.Automorphic.CompactRep
theorem _root_.solution {Y : Submodule ℂ X} (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y) (hY0 : Y ≠ ⊥) :
    ∃ (c : Submodule (MonoidAlgebra ℂ K) σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule),
      ∃ y ∈ Y, y ≠ 0 ∧ kProj hσ hc y = y := by
  haveI := isSemisimpleModule_asModule hσ
  let P : Subrepresentation σ := ⟨Y, fun k y hy => hY k y hy⟩
  set N := Subrepresentation.subrepresentationSubmoduleOrderIso P
  have hN0 : N ≠ ⊥ := by
    intro h
    apply hY0
    have : P = ⊥ := by
      have := congrArg (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)).symm h
      rwa [OrderIso.symm_apply_apply, OrderIso.map_bot] at this
    have := congrArg Subrepresentation.toSubmodule this
    exact this
  obtain ⟨S, hSatom, hSN⟩ := (eq_bot_or_exists_atom_le N).resolve_left hN0
  have hS : IsSimpleModule (MonoidAlgebra ℂ K) S := (isSimpleModule_iff_isAtom).2 hSatom
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSatom.1
  refine ⟨isotypicComponent (MonoidAlgebra ℂ K) σ.asModule S, ⟨S, hS, rfl⟩, s, hSN hs, hs0, ?_⟩
  exact (kProj_apply_eq_self_iff hσ _).2 (Submodule.le_isotypicComponent S hs)
end GroundTheory.Automorphic.CompactRep
