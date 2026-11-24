-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.integral_KO_mul_right_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:13.579816+00:00
-- url     : https://prove2.me/submissions/63440304-6c96-40ce-bf12-2b2187487afa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_lintegral_KO_mul_right
import Theorems.Thm_GlobalTheory_SmGL_modulus_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
open GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SmGL.IndDual
theorem _root_.solution (μ : Measure (GL n k)) [μ.IsHaarMeasure] {f : GL n k → ℝ}
    (hf : Continuous f) (hlaw : ∀ (p : parab k e) x, f (p * x) = modulus k m (leviProj k e p) * f x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), f (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), f x ∂μ := by
  have h1 : IntegrableOn (fun x => f (x * g)) (KO k n : Set (GL n k)) μ :=
    (hf.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn f (KO k n : Set (GL n k)) μ := hf.continuousOn.integrableOn_compact isCompact_KO
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (f x)) hf.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ENNReal.ofReal_mul (modulus_pos k _).le]) g,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (-f x)) hf.neg.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ← mul_neg, ENNReal.ofReal_mul (modulus_pos k _).le]) g]
end GlobalTheory.SmGL.IndDual
