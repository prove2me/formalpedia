-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.diagGL_mul_mul_inv_mem_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:19:00.547933+00:00
-- url     : https://prove2.me/submissions/4a2582ce-519a-4ad4-9a4b-d83279e64550

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_diagGL_mul_mul_diagGL_apply_self
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
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution {u : GL (Fin n) F} (hu : u ∈ unipotent F n)
    (d : Fin n → Fˣ) : diagGL F n d * u * (diagGL F n d)⁻¹ ∈ unipotent F n := by
  refine ⟨(borel F n).mul_mem ((borel F n).mul_mem (diagGL_mem_borel F n d) hu.1)
    ((borel F n).inv_mem (diagGL_mem_borel F n d)), fun i => ?_⟩
  rw [← map_inv, diagGL_mul_mul_diagGL_apply_self F n hu]
  simp
end GroundTheory.Automorphic.Iwasawa
