-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.conj_permGL_mem_blockUpper_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:58.575311+00:00
-- url     : https://prove2.me/submissions/87b23fb6-641d-41ce-833a-efe34fadc195

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable {β γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {α : Type*} [LinearOrder α] {β : Fin n → α}
    (s : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permGL F s * g * (permGL F s)⁻¹ ∈ blockUpper F n β ↔ g ∈ blockUpper F n (β ∘ s) := by
  have key : ∀ r c, ((permGL F s * g * (permGL F s)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c =
      (g : Matrix (Fin n) (Fin n) F) (s⁻¹ r) (s⁻¹ c) := by
    intro r c
    rw [← map_inv, Units.val_mul, Units.val_mul, mul_permGL_apply, permGL_mul_apply]
  constructor
  · intro h i j hij
    have := h (i := s i) (j := s j) hij
    rw [key] at this
    simpa using this
  · intro h r c hrc
    show ((permGL F s * g * (permGL F s)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r c = 0
    rw [key]
    apply h
    simpa using hrc
end GroundTheory.Automorphic.Parabolic
