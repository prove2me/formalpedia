-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_isComplexConjugation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:16.749067+00:00
-- url     : https://prove2.me/submissions/1fd42bc2-17bd-4d21-8e27-5f485d00b593

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree

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
theorem _root_.solution : ∃ σ : Gal(ℚ̄/ℚ), IsComplexConjugation σ := by
  let ι : ℚ̄ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := exists_algEquiv_conj ι.toRingHom
  exact ⟨σ, ι.toRingHom, hσ⟩
end GroundTheory.Global.Cyclotomic
