-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.toPadicInt_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:03.313344+00:00
-- url     : https://prove2.me/submissions/dd17a850-df35-4997-940c-55aefacdb396

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
theorem _root_.solution (q : Nat.Primes) (σ : Gal(ℚ̄/ℚ)) :
    toPadicInt q (Multiplicative.toAdd (degree σ)) = Multiplicative.toAdd (degreeComponent q σ) := by
  rw [degree_apply, toPadicInt_unitsDegree, unitsPadicEquiv_apply]
  rfl
end GroundTheory.Global.Cyclotomic
