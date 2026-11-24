-- Prove2me | solution 1 for GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:48:22.86169+00:00
-- url     : https://prove2.me/submissions/e0d70368-2ef4-4daf-bc4f-67092226e5f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualBicharacterPairingOfSymmBilinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualBicharacterPairingOfSymmBilinFormStatement
import Theorems.Thm_GlobalTheory_KSp_isPair_addChar_form


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F), (∀ x y, β x y = β y x) → (∀ y, (∀ x, β x y = 0) → y = 0) → IsPair fun x y => ψ (β x y) := by
  first | exact @GlobalTheory.KSp.isPair_addChar_form | exact GlobalTheory.KSp.isPair_addChar_form | (intros; apply GlobalTheory.KSp.isPair_addChar_form <;> assumption)
end _root_.GlobalTheory.T
