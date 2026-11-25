-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:42.213029+00:00
-- url     : https://prove2.me/submissions/b04039d8-8621-4fdb-a51e-1a0dba1bf2cb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_real_of_even
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_real_of_odd

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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = if Even n then 2 else 1 := by
  split_ifs with he
  · exact index_range_powMonoidHom_real_of_even hn he
  · exact index_range_powMonoidHom_real_of_odd (Nat.not_even_iff_odd.1 he)
end GroundTheory.Global
