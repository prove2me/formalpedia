-- Prove2me | solution 1 for GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:06.397323+00:00
-- url     : https://prove2.me/submissions/9c95e4f4-c217-4a9a-a660-cab36dd2279d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KrasnerLemmaDecompositionGroupStabilizerVersion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KrasnerLemmaDecompositionGroupStabilizerVersionStatement
import Theorems.Thm_GlobalTheory_krasner_stabiliser


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (β β' : Ω), (∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) → ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  first | exact @GlobalTheory.krasner_stabiliser | exact GlobalTheory.krasner_stabiliser | (intros; apply GlobalTheory.krasner_stabiliser <;> assumption)
end _root_.GlobalTheory.T
