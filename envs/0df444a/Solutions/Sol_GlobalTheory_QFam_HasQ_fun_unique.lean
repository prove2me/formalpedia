-- Prove2me | solution 1 for GlobalTheory.QFam.HasQ.fun_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:29.868008+00:00
-- url     : https://prove2.me/submissions/8b94d24c-0f67-4a81-b7f7-67912d8da7e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelCoeffAndFunctionUnique
import Theorems.Thm_GlobalTheory_HasQExpansion_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
namespace HasQ
theorem _root_.solution {N : ℕ} {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g a) :
    f = g := by
  funext τ
  exact (hf τ).unique (hg τ)
end HasQ
end GlobalTheory.QFam
