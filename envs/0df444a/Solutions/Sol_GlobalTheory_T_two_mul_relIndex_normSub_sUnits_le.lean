-- Prove2me | solution 1 for GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:33:57.684506+00:00
-- url     : https://prove2.me/submissions/521201d5-cc57-4c98-bd38-dcdd8a3b14e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FirstInequalitySUnitsStatement
import Theorems.Thm_GlobalTheory_QNorm_first_inequality_sUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧ 2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ 2 ^ (tFin F δ S + tReal F δ) := by
  first | exact @GlobalTheory.QNorm.first_inequality_sUnits | exact GlobalTheory.QNorm.first_inequality_sUnits | (intros; apply GlobalTheory.QNorm.first_inequality_sUnits <;> assumption)
end _root_.GlobalTheory.T
