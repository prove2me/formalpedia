-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_real_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:22.81644+00:00
-- url     : https://prove2.me/submissions/9d09ef1c-6a69-4ea9-a34e-78025f2f0ce3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Theorems.Thm_GroundTheory_Global_mem_range_powMonoidHom_real_iff_of_even

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (he : Even n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b ↦ ?_⟩
  rw [mem_range_powMonoidHom_real_iff_of_even hn he, mem_range_powMonoidHom_real_iff_of_even hn he,
    Units.val_mul, Units.val_neg, Units.val_one, mul_neg_one]
  rcases lt_or_gt_of_ne b.ne_zero with hb | hb
  · exact Or.inl ⟨neg_pos.2 hb, hb.not_gt⟩
  · exact Or.inr ⟨hb, by linarith⟩
end GroundTheory.Global
