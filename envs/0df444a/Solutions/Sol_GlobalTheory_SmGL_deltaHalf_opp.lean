-- Prove2me | solution 1 for GlobalTheory.SmGL.deltaHalf_opp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:06.766916+00:00
-- url     : https://prove2.me/submissions/353ad6b4-5599-4f52-87b4-936c60503067

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_absPow_neg
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_apply
import Theorems.Thm_GlobalTheory_SmGL_modExp_opp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
namespace GlobalTheory.SmGL
theorem _root_.solution (g : Levi k m) :
    deltaHalf k (fun a : αᵒᵈ => m (OrderDual.ofDual a)) g = (deltaHalf k m g)⁻¹ := by
  rw [deltaHalf_apply k g, ← Finset.prod_inv_distrib]
  refine (deltaHalf_apply k (m := fun a : αᵒᵈ => m (OrderDual.ofDual a)) g).trans
    (Finset.prod_congr rfl fun a _ => ?_)
  have key : ∀ (z : ℤ) (x : kˣ), z = -modExp m a →
      absPow k ((z : ℂ) / 2) x = (absPow k ((modExp m a : ℂ) / 2) x)⁻¹ := by
    rintro _ x rfl
    rw [Int.cast_neg, neg_div, absPow_neg]
    rfl
  exact key _ _ (modExp_opp (m := m) a)
end GlobalTheory.SmGL
