-- Prove2me | solution 1 for GroundTheory.Global.range_powMonoidHom_real_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:56.025188+00:00
-- url     : https://prove2.me/submissions/fb96353b-121b-4920-8ae6-2ba11d3786dd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_exists_pos_real_pow_eq
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


attribute [local simp] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} (ho : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = ⊤ := by
  have hn : n ≠ 0 := by rintro rfl; simp at ho
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [MonoidHom.mem_range]
  rcases lt_or_gt_of_ne x.ne_zero with hx | hx
  · obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq (neg_pos.2 hx) hn
    refine ⟨Units.mk0 (-y) (neg_ne_zero.2 hy.ne'), ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, ho.neg_pow, hyx, neg_neg]
  · obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx hn
    refine ⟨Units.mk0 y hy.ne', ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hyx]
end GroundTheory.Global
