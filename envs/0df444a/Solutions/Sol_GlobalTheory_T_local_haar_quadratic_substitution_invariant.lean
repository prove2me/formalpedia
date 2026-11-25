-- Prove2me | solution 1 for GlobalTheory.T.local_haar_quadratic_substitution_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:52.383886+00:00
-- url     : https://prove2.me/submissions/f18f59d4-9605-4e6c-b1c1-8d497ec1b300

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariantStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_measure_quad_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ a c : Fv F v, Valued.v a = 1 → c ∈ v.adicCompletionIntegers F → ∀ A : Set (Fv F v), MeasurableSet A → lam {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ A} = lam (A ∩ {s | Valued.v s < 1}) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv | exact GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv | (intros; apply GlobalTheory.CompanionTheory.SW.QuadIso.measure_quad_Fv <;> assumption)
end _root_.GlobalTheory.T
