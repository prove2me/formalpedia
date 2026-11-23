-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_unipotentRadical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:04.471918+00:00
-- url     : https://prove2.me/submissions/a352667d-9d5c-4799-b17b-e71e0437439f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {g : GL (Fin n) F} :
    g ∈ unipotentRadical F n β ↔ g ∈ blockUpper F n β ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, fun i j hij => ?_⟩
    have h := congrArg (fun m : levi F n β => ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)
      ((leviProj F n β).mem_ker.1 hp)
    simp only [leviProj_apply, if_pos hij] at h
    simpa using h
  · rintro ⟨hP, h⟩
    refine ⟨⟨g, hP⟩, (leviProj F n β).mem_ker.2 (Subtype.ext (Units.ext ?_)), rfl⟩
    ext i j
    show (if β i = β j then g i j else 0) = ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j
    split_ifs with hij
    · rw [h i j hij, Units.val_one]
    · rw [Units.val_one, one_apply_ne fun e => hij (by rw [e])]
end GroundTheory.Automorphic.Parabolic
