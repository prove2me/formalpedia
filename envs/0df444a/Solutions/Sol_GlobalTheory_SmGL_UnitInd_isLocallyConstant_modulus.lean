-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.isLocallyConstant_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:07.595219+00:00
-- url     : https://prove2.me/submissions/8748b8a0-3864-4681-936c-09e1698e37bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isLocallyConstant_of_open
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_deltaHalf
import Theorems.Thm_GlobalTheory_SmGL_modulus_pos
import Theorems.Thm_GlobalTheory_SmGL_val_deltaHalf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution : IsLocallyConstant (modulus k m) := by
  refine isLocallyConstant_of_open (isSmoothChar_deltaHalf k) (one_mem _) fun x u hu => ?_
  have h : deltaHalf k m (x * u) = deltaHalf k m x := by rw [map_mul, show deltaHalf k m u = 1 from hu, mul_one]
  have h2 := congrArg Units.val h
  rw [val_deltaHalf, val_deltaHalf, Complex.ofReal_inj] at h2
  exact (Real.sqrt_inj (modulus_pos k _).le (modulus_pos k _).le).1 h2
end GlobalTheory.SmGL.UnitInd
