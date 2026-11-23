-- Prove2me | solution 1 for GlobalTheory.SmGL.modulus_torus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:38.181832+00:00
-- url     : https://prove2.me/submissions/f7799ad3-6ecd-400c-939c-6b7e18eaa65e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd

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
theorem _root_.solution {n : Type} [Fintype n] [LinearOrder n] (t : n → kˣ) :
    modulus k (fun _ : n => Unit) (leviTorus k n t) =
      ∏ i, ∏ j with i < j, nabs k (t i / t j) := by
  have hd : ∀ i, GeneralLinearGroup.det (leviTorus k n t i) = t i :=
    congrFun ((leviTorus k n).left_inv t)
  have hq : ∀ x y : kˣ, nabs k (x / y) = nabs k x / nabs k y := fun x y => by simp [nabs]
  simp only [modulus, hd, modExp, hq, Finset.prod_div_distrib, Fintype.card_unique, Nat.cast_one,
    Finset.sum_const, nsmul_eq_mul, mul_one, zpow_sub₀ (nabs_pos' k _).ne', zpow_natCast,
    Finset.prod_const]
  congr 1
  simp only [← Finset.prod_const, Finset.prod_filter]
  exact Finset.prod_comm
end GlobalTheory.SmGL
