-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_doubleCoset_iff_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:19:57.195147+00:00
-- url     : https://prove2.me/submissions/6ae208bc-366b-406a-b370-c93d8135d437

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_unipotent_le_borel
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_diagGL_mem_borel
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mul_inv_borelDiag_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_inv_borelDiag_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_permGL_mul_diagGL
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_unipotent_le_borel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} :
    g ∈ doubleCoset (permGL F w) (borel n F) (borel n F) ↔
      ∃ u ∈ Iwasawa.unipotent F n, ∃ t : Fin n → Fˣ, ∃ v ∈ Iwasawa.unipotent F n,
        g = u * Iwasawa.diagGL F n t * permGL F w * v := by
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_doubleCoset.1 h
    refine ⟨x * (Iwasawa.diagGL F n (borelDiag hx))⁻¹, mul_inv_borelDiag_mem hx,
      borelDiag hx * (fun r => borelDiag hy (w⁻¹ r)),
      (Iwasawa.diagGL F n (borelDiag hy))⁻¹ * y, inv_borelDiag_mul_mem hy, ?_⟩
    rw [map_mul]
    have e := permGL_mul_diagGL (F := F) w (borelDiag hy)
    calc x * permGL F w * y
        = x * (permGL F w * Iwasawa.diagGL F n (borelDiag hy)) *
            ((Iwasawa.diagGL F n (borelDiag hy))⁻¹ * y) := by group
      _ = _ := by rw [e]; group
  · rintro ⟨u, hu, t, v, hv, rfl⟩
    exact mem_doubleCoset.2 ⟨u * Iwasawa.diagGL F n t,
      (borel n F).mul_mem (unipotent_le_borel hu) (diagGL_mem_borel t), v, unipotent_le_borel hv,
      rfl⟩
end GroundTheory.Automorphic.Whittaker
