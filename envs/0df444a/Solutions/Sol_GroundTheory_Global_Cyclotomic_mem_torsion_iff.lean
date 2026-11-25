-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.mem_torsion_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:30.507067+00:00
-- url     : https://prove2.me/submissions/6d7c6836-498f-4fbd-bf22-aa04e36928bd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (u : ℤ_[ℓ]ˣ) :
    u ∈ CommGroup.torsion ℤ_[ℓ]ˣ ↔ u ^ torsionExponent ℓ = 1 := by
  rw [← ker_padicUnitsLog, MonoidHom.mem_ker, padicUnitsLog_eq_one_iff]
end GroundTheory.Global.Cyclotomic
