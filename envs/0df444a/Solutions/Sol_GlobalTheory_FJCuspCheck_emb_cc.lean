-- Prove2me | solution 1 for GlobalTheory.FJCuspCheck.emb_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:25.597972+00:00
-- url     : https://prove2.me/submissions/c09558a6-4da8-407f-ae88-98fe485e0636

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_TransvMemZGam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.FJCuspCheck
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.FJCuspCheck
theorem _root_.solution (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x
end GlobalTheory.FJCuspCheck
