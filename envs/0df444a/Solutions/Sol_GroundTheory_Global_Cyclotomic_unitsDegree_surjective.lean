-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.unitsDegree_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:23:58.928181+00:00
-- url     : https://prove2.me/submissions/bf8f2080-c18b-472d-b6f2-c33d83342bf0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Theorems.Thm_GroundTheory_Global_Cyclotomic_ext_toPadicInt


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
theorem _root_.solution : Function.Surjective unitsDegree := by
  intro y
  choose g hg using fun q : Nat.Primes =>
    padicUnitsLog_surjective q (Multiplicative.ofAdd (toPadicInt q (Multiplicative.toAdd y)))
  refine ⟨unitsPadicEquiv.symm g, Multiplicative.toAdd.injective (ext_toPadicInt fun q => ?_)⟩
  rw [toPadicInt_unitsDegree, MulEquiv.apply_symm_apply, hg, toAdd_ofAdd]
end GroundTheory.Global.Cyclotomic
