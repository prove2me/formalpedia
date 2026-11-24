-- Prove2me | solution 1 for GlobalTheory.TraceIso.split_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:53.463293+00:00
-- url     : https://prove2.me/submissions/99cc4d5f-9caf-48f8-b42b-810b9adb693d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
import Theorems.Thm_GlobalTheory_TraceIso_finiteDimensional_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
namespace GlobalTheory.TraceIso
theorem _root_.solution [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (f : V →ₗ[A] W) (hf : f ≠ 0) :
    ∃ (P : Submodule A V) (Q S : Submodule A W), Nonempty (V ≃ₗ[A] P × S) ∧ Nonempty (W ≃ₗ[A] Q × S) ∧
      finrank k P < finrank k V ∧ finrank k Q < finrank k W := by
  obtain ⟨P', hP'⟩ := exists_isCompl (LinearMap.ker f)
  obtain ⟨Q, hQ⟩ := exists_isCompl (LinearMap.range f)
  let e₁ : V ≃ₗ[A] (LinearMap.ker f) × (LinearMap.range f) :=
    (Submodule.prodEquivOfIsCompl _ _ hP').symm.trans
      ((LinearEquiv.refl A _).prodCongr
        ((Submodule.quotientEquivOfIsCompl _ _ hP').symm.trans f.quotKerEquivRange))
  let e₂ : W ≃ₗ[A] Q × (LinearMap.range f) := (Submodule.prodEquivOfIsCompl _ _ hQ.symm).symm
  haveI := finiteDimensional_sub (k := k) (LinearMap.ker f)
  haveI := finiteDimensional_sub (k := k) (LinearMap.range f)
  haveI := finiteDimensional_sub (k := k) Q
  haveI : Nontrivial (LinearMap.range f) :=
    Submodule.nontrivial_iff_ne_bot.2 fun h => hf (LinearMap.range_eq_bot.1 h)
  have hpos : 0 < finrank k (LinearMap.range f) := Module.finrank_pos
  refine ⟨_, Q, _, ⟨e₁⟩, ⟨e₂⟩, ?_, ?_⟩
  · rw [(e₁.restrictScalars k).finrank_eq, finrank_prod]; omega
  · rw [(e₂.restrictScalars k).finrank_eq, finrank_prod]; omega
end GlobalTheory.TraceIso
