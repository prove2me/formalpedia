-- Prove2me | solution 1 for GlobalTheory.T.hermitian_one_by_one_is_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:28.974151+00:00
-- url     : https://prove2.me/submissions/327bb64d-08bf-432c-ab56-cd0096f2937b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOneByOneIsScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOneByOneIsScalarStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_hermOne_eq_scal


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Matrix (Fin 1) (Fin 1) E) (hT : ∀ a b, σ (T b a) = T a b), ∃ β : F, T = (fun _ _ => algebraMap F E β) ∧ (T.det ≠ 0 → β ≠ 0) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], hermOf R σ T hT = hermScal R σ (algebraMap F R β) := by
  first | exact @GlobalTheory.CompanionTheory.SW.hermOne_eq_scal | exact GlobalTheory.CompanionTheory.SW.hermOne_eq_scal | (intros; apply GlobalTheory.CompanionTheory.SW.hermOne_eq_scal <;> assumption)
end _root_.GlobalTheory.T
