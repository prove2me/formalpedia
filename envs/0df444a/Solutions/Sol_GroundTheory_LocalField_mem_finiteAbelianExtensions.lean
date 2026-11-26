-- Prove2me | solution 1 for GroundTheory.LocalField.mem_finiteAbelianExtensions
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:30.794683+00:00
-- url     : https://prove2.me/submissions/59f26831-27ae-4d7d-be5e-aef677f97f93

import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
omit [IsGalois F Ω]
theorem _root_.solution {L : IntermediateField F Ω} :
    L ∈ finiteAbelianExtensions F Ω ↔ FiniteDimensional F L ∧ IsAbelianGalois F L := by
  first
    | (intros; simp [finiteAbelianExtensions])
    | (intros; unfold finiteAbelianExtensions; simp)
    | (intros; simp [finiteAbelianExtensions]; done)
    | (intros; ext; simp [finiteAbelianExtensions])
    | (intros; simp only [finiteAbelianExtensions]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [finiteAbelianExtensions])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [finiteAbelianExtensions])
    | (intros; unfold finiteAbelianExtensions; split_ifs <;> simp_all)
    | (intros; unfold finiteAbelianExtensions; positivity)
    | (intros; unfold finiteAbelianExtensions; ring)
    | (intros; unfold finiteAbelianExtensions; exact?)
    | (intros; aesop (add norm simp [finiteAbelianExtensions]))
    | (intros; simp [finiteAbelianExtensions] <;> aesop)
    | (intros; exact finiteAbelianExtensions.symm ..)
    | (intros; exact finiteAbelianExtensions.comm ..)
  trace "HIT_109_0"

