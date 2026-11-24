-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.modulus_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:13.027335+00:00
-- url     : https://prove2.me/submissions/56e41d73-7e78-46c6-a669-233a58abcb71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus

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
theorem _root_.solution (g : Levi k m) : modulus k m g * modulus k m g⁻¹ = 1 := by
  have : ∀ a, ((distribHaarChar k (GeneralLinearGroup.det (g a)) : NNReal) : ℝ) ≠ 0 := fun a => (nabs_pos' k _).ne'
  simp only [modulus, nabs, ← Finset.prod_mul_distrib, Pi.inv_apply, map_inv, NNReal.coe_inv, ← mul_zpow,
    mul_inv_cancel₀ (this _), _root_.one_zpow, Finset.prod_const_one]
end GlobalTheory.SmGL.UnitInd
