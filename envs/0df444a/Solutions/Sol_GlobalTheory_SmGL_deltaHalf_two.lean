-- Prove2me | solution 1 for GlobalTheory.SmGL.deltaHalf_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:30:44.272001+00:00
-- url     : https://prove2.me/submissions/49433bdd-f95f-458f-953c-60a80bdab588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_apply

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
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SmGL
theorem _root_.solution (g : GL a k × GL b k) :
    deltaHalf k (Two a b) (leviTwo k a b g) =
      absPow k ((Fintype.card b : ℂ) / 2) (GeneralLinearGroup.det g.1) *
        absPow k (-(Fintype.card a : ℂ) / 2) (GeneralLinearGroup.det g.2) := by
  have h1 : modExp (Two a b) false = Fintype.card b := by
    simp [modExp, Finset.sum_filter]
  have h2 : modExp (Two a b) true = -Fintype.card a := by
    simp [modExp, Finset.sum_filter]
  rw [deltaHalf_apply, Fintype.prod_bool, h1, h2, mul_comm]
  push_cast
  rfl
end GlobalTheory.SmGL
