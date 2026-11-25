-- Prove2me | solution 1 for GlobalTheory.T.arithmetic_unitary_group_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:46.472034+00:00
-- url     : https://prove2.me/submissions/d81a72a0-e6a8-469f-89c8-7ebe1986ada1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArithmeticUnitaryGroupDiscrete
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArithmeticUnitaryGroupDiscreteStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_rational_countable_discrete


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Countable (HFinIn (AF F) σ J) ∧ ∃ U ∈ 𝓝 (1 : HA (AF F) σ J), ∀ h ∈ U, HA.mat (AF F) σ J h ∈ HFin (AF F) σ J → h = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.rational_countable_discrete | exact GlobalTheory.CompanionTheory.SW.rational_countable_discrete | (intros; apply GlobalTheory.CompanionTheory.SW.rational_countable_discrete <;> assumption)
end _root_.GlobalTheory.T
