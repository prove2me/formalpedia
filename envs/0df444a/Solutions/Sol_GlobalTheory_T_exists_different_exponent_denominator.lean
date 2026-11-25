-- Prove2me | solution 1 for GlobalTheory.T.exists_different_exponent_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:04:50.327677+00:00
-- url     : https://prove2.me/submissions/d679891a-7b7b-4d9f-a200-8da3fcc7198d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominatorStatement
import Theorems.Thm_GlobalTheory_DifferentElement_diff_element


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧ ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = algebraMap O K D * σ y := by
  first | exact @GlobalTheory.DifferentElement.diff_element | exact GlobalTheory.DifferentElement.diff_element | (intros; apply GlobalTheory.DifferentElement.diff_element <;> assumption)
end _root_.GlobalTheory.T
