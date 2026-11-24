-- Prove2me | solution 1 for GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:37.19004+00:00
-- url     : https://prove2.me/submissions/b337f79e-e2e7-47d8-b0ad-8ec939cf42f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarBasicPropertiesStatement
import Theorems.Thm_GlobalTheory_KSp_sc_basic


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : ResEtaPow (R := F) ⊥ χ m), sc F χ m 1 = 1 ∧ (∀ z z' : E, sc F χ m (z * z') = sc F χ m z * sc F χ m z') ∧ (∀ z : Eˣ, sc F χ m (z : E) = (χ z : ℂ) * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖sc F χ m (z : E)‖ ^ 2 = nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, sc F χ m (c (z : E))⁻¹ * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = sc F χ m (z : E)) ∧ (∀ t : Fˣ, sc F χ m (algebraMap F E t) = (sgn E t * (nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, sc F χ m ((z : E) * c (z : E)) = ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  first | exact @GlobalTheory.KSp.sc_basic | exact GlobalTheory.KSp.sc_basic | (intros; apply GlobalTheory.KSp.sc_basic <;> assumption)
end _root_.GlobalTheory.T
