-- Prove2me | solution 1 for GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:56.415787+00:00
-- url     : https://prove2.me/submissions/ebf3f8b8-b3f1-4ace-ab0d-c072ead1b75e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceLeSpanPureTensors
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceLeSpanPureTensorsStatement
import Theorems.Thm_GlobalTheory_coefSpace_le_span_pure_tensors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (S : ι → Set (MvPolynomial (Fin n × Fin n) K)), (∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (S τ)) → VV K lam ≤ Submodule.span K {P | ∃ f : ι → MvPolynomial (Fin n × Fin n) K, (∀ τ, f τ ∈ S τ) ∧ P = ten f} := by
  first | exact @GlobalTheory.coefSpace_le_span_pure_tensors | exact GlobalTheory.coefSpace_le_span_pure_tensors | (intros; apply GlobalTheory.coefSpace_le_span_pure_tensors <;> assumption)
end _root_.GlobalTheory.T
