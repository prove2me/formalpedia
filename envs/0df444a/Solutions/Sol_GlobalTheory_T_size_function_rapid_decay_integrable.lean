-- Prove2me | solution 1 for GlobalTheory.T.size_function_rapid_decay_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:25.025805+00:00
-- url     : https://prove2.me/submissions/0304f5b1-58bb-43cf-8c0e-8c8bc62a7e97

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrableStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_size_neg_pow_integrable


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) ∧ (∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X) ∧ ∃ N : ℕ, ∫⁻ X, ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) ∂μ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SW.SizeInt.size_neg_pow_integrable | exact GlobalTheory.CompanionTheory.SW.SizeInt.size_neg_pow_integrable | (intros; apply GlobalTheory.CompanionTheory.SW.SizeInt.size_neg_pow_integrable <;> assumption)
end _root_.GlobalTheory.T
