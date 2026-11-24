-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.integral_integralGL_mul_right_complex_productSigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:29.082913+00:00
-- url     : https://prove2.me/submissions/c7e203bd-9b8d-4edb-843c-26b12255198f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Theorems.Thm_GlobalTheory_SmGL_IndDual_integral_KO_mul_right_real
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
theorem _root_.solution (μ : Measure (GL n k)) [μ.IsHaarMeasure] {F : GL n k → ℂ}
    (hF : Continuous F) (hlaw : ∀ (p : parab k e) x, F (p * x) = (modulus k m (leviProj k e p) : ℂ) * F x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  have h1 : IntegrableOn (fun x => F (x * g)) (KO k n : Set (GL n k)) μ :=
    (hF.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn F (KO k n : Set (GL n k)) μ := hF.continuousOn.integrableOn_compact isCompact_KO
  have hre := integral_KO_mul_right_real e μ (Complex.continuous_re.comp hF)
    (fun p x => by simp [hlaw]) g
  have him := integral_KO_mul_right_real e μ (Complex.continuous_im.comp hF)
    (fun p x => by simp [hlaw]) g
  refine Complex.ext ?_ ?_
  · exact ((integral_re h1).symm.trans hre).trans (integral_re h2)
  · exact ((integral_im h1).symm.trans him).trans (integral_im h2)
end GlobalTheory.SmGL.IndDual
