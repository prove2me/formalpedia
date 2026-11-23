-- Prove2me | solution 1 for GlobalTheory.SmGL.val_deltaHalf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:48.306322+00:00
-- url     : https://prove2.me/submissions/303bc43d-0da4-4ee3-a53d-b061e1e772d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_val_absPow_ofReal
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
namespace GlobalTheory.SmGL
theorem _root_.solution (g : Levi k m) : (deltaHalf k m g : ℂ) = (√(modulus k m g) : ℝ) := by
  rw [deltaHalf_apply, Units.coe_prod, modulus,
    Real.sqrt_prod _ fun _ _ => (zpow_pos (nabs_pos' k _) _).le, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  have : ((modExp m a : ℂ) / 2) = (((modExp m a : ℝ) * (1 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [this, val_absPow_ofReal, Real.sqrt_eq_rpow, Real.rpow_mul (nabs_pos' k _).le, Real.rpow_intCast]
end GlobalTheory.SmGL
