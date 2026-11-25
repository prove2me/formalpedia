-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.continuous_degreeComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:42.480639+00:00
-- url     : https://prove2.me/submissions/a28146f6-85b8-43f4-a01c-e15ccc1d44ee

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_toPadicInt_degree

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
theorem _root_.solution (q : Nat.Primes) : Continuous (degreeComponent q) := by
  have h : Continuous fun σ : Gal(ℚ̄/ℚ) => Multiplicative.toAdd (degreeComponent q σ) :=
    ((continuous_toPadicInt q).comp (continuous_toAdd.comp continuous_degree)).congr
      (toPadicInt_degree q)
  exact continuous_ofAdd.comp h
end GroundTheory.Global.Cyclotomic
