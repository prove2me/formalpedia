-- Prove2me | solution 1 for GlobalTheory.T.sum_nonzero_integers_principal_ideals_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:14.6218+00:00
-- url     : https://prove2.me/submissions/2d99c441-ec0b-47e1-b12d-124f1b512913

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNonzeroIntegersPrincipalIdealsUnits
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNonzeroIntegersPrincipalIdealsUnitsStatement
import Theorems.Thm_GlobalTheory_sum_over_principal_ideals_units


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : 𝓞 K → E), f 0 = 0 → ∀ (c : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → E) (β : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → (𝓞 K)ˣ → ℝ) (b : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → ℝ), (∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, HasSum (fun u : (𝓞 K)ˣ => f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))) (c J)) → (∀ (J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}) (u : (𝓞 K)ˣ), ‖f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))‖ ≤ β J u) → (∀ J, HasSum (β J) (b J)) → Summable b → HasSum f (∑' J, c J) := by
  first | exact @GlobalTheory.sum_over_principal_ideals_units | exact GlobalTheory.sum_over_principal_ideals_units | (intros; apply GlobalTheory.sum_over_principal_ideals_units <;> assumption)
end _root_.GlobalTheory.T
