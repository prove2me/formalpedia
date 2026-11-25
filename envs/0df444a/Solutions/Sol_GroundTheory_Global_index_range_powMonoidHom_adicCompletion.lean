-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:02.647088+00:00
-- url     : https://prove2.me/submissions/e27a4014-fbe9-4635-a4e6-37f1c7d15911

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Theorems.Thm_GroundTheory_Global_natCard_residueField_adicCompletion
import Theorems.Thm_GroundTheory_Global_norm_eq_absNorm_zpow_neg_ord
import Theorems.Thm_GroundTheory_Global_natCast_ne_zero_adicCompletion
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom


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
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable {v}
variable (v)
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n * Nat.card (rootsOfUnity n (v.adicCompletion K)) / ‖(n : v.adicCompletion K)‖ := by
  have hn' := natCast_ne_zero_adicCompletion (v := v) hn
  rw [index_range_powMonoidHom hn', natCard_residueField_adicCompletion,
    norm_eq_absNorm_zpow_neg_ord v hn', zpow_neg, div_inv_eq_mul]
end GroundTheory.Global
