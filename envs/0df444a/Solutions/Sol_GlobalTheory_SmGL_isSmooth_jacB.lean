-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_jacB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:14.609822+00:00
-- url     : https://prove2.me/submissions/10762229-6624-4fb7-a350-85c86ed77bcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_jac
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviTorus
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {k}
variable [LinearOrder n]
namespace GlobalTheory.SmGL
theorem _root_.solution {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) : IsSmooth (jacB π) :=
  isSmooth_comp (isSmooth_jac _ hπ) _ (continuous_leviTorus k n)
end GlobalTheory.SmGL
