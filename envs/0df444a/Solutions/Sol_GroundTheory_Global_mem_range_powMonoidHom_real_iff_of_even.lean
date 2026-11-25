-- Prove2me | solution 1 for GroundTheory.Global.mem_range_powMonoidHom_real_iff_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:57.825573+00:00
-- url     : https://prove2.me/submissions/3e1a0ac5-100c-47d2-ae81-07209912252f

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (he : Even n) (x : ℝˣ) :
    x ∈ (powMonoidHom n : ℝˣ →* ℝˣ).range ↔ 0 < (x : ℝ) := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    exact he.pow_pos y.ne_zero
  · intro hx
    obtain ⟨y, hy, hyx⟩ := exists_pos_real_pow_eq hx hn
    refine ⟨Units.mk0 y hy.ne', ?_⟩
    ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hyx]
end GroundTheory.Global
