-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mul_inv_borelDiag_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:40.307679+00:00
-- url     : https://prove2.me/submissions/1c101c09-e26d-4154-b210-57b8f32ba175

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_unipotent
import Theorems.Thm_GroundTheory_Automorphic_borel_diag_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {b : GL (Fin n) F} (hb : b ∈ borel n F) :
    b * (Iwasawa.diagGL F n (borelDiag hb))⁻¹ ∈ Iwasawa.unipotent F n := by
  have hbu : (b : Matrix (Fin n) (Fin n) F).IsUpperTriangular := hb
  rw [Iwasawa.mem_unipotent F n, ← map_inv, Units.val_mul, Iwasawa.coe_diagGL]
  refine ⟨hbu.mul (blockTriangular_diagonal _), fun i => ?_⟩
  rw [mul_diagonal]
  simp only [borelDiag, Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_mk0]
  exact mul_inv_cancel₀ (borel_diag_ne_zero hb i)
end GroundTheory.Automorphic.Whittaker
