-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.diagGL_mul_mul_diagGL_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:29.165775+00:00
-- url     : https://prove2.me/submissions/a304e4d4-4513-48c0-b8ce-d94c0e526f66

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
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
    (a c : Fin n → Fˣ) (i : Fin n) :
    (diagGL F n a * u * diagGL F n c : GL (Fin n) F) i i = a i * c i := by
  rw [mul_apply_self_of_mem_borel F n ((borel F n).mul_mem (diagGL_mem_borel F n a) hu.1)
    (diagGL_mem_borel F n c), mul_apply_self_of_mem_borel F n (diagGL_mem_borel F n a) hu.1,
    hu.2]
  simp
end GroundTheory.Automorphic.Iwasawa
