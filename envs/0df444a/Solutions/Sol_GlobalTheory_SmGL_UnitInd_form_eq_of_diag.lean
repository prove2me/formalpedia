-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.form_eq_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:24.581958+00:00
-- url     : https://prove2.me/submissions/457aa072-d6ec-4b85-b000-0916b960589d

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
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (B C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (h : ∀ v, B v v = C v v) (v w : V) : B v w = C v w := by
  have h1 := h (v + w)
  have h2 := h (v + Complex.I • w)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h v, h w,
    Complex.conj_I, smul_eq_mul, RingHom.id_apply] at h1 h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 +
    ((1 / 2 : ℂ) * (B v w - C v w - B w v + C w v)) * Complex.I_mul_I
end GlobalTheory.SmGL.UnitInd
