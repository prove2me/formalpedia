-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.continuous_unitsPadicEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:26.262648+00:00
-- url     : https://prove2.me/submissions/76c5d600-ef19-48aa-94c2-92dc006f21d0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_unitsPadicEquiv_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped GroundTheory.LocalField.Abstract ComplexConjugate
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (q : Nat.Primes) :
    Continuous fun u : ℤ̂ˣ => unitsPadicEquiv u q := by
  simp_rw [unitsPadicEquiv_apply]
  rw [Units.continuous_iff]
  exact ⟨(continuous_toPadicInt q).comp Units.continuous_val,
    (continuous_toPadicInt q).comp Units.continuous_coe_inv⟩
end GroundTheory.Global.Cyclotomic
