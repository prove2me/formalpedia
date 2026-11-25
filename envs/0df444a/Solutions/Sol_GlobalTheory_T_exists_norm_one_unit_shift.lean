-- Prove2me | solution 1 for GlobalTheory.T.exists_norm_one_unit_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:53.998338+00:00
-- url     : https://prove2.me/submissions/9378e2cc-41c1-43c3-a692-7c3f7f761a6e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsNormOneUnitShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsNormOneUnitShiftStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LamUnit_exists_norm_one_sub_isUnit


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (t : R ⊗[F] E) (β : Rˣ), ∃ lam : R ⊗[F] E, lam * sigR R σ lam = 1 ∧ IsUnit (algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LamUnit.exists_norm_one_sub_isUnit | exact GlobalTheory.CompanionTheory.SW.LamUnit.exists_norm_one_sub_isUnit | (intros; apply GlobalTheory.CompanionTheory.SW.LamUnit.exists_norm_one_sub_isUnit <;> assumption)
end _root_.GlobalTheory.T
