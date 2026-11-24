-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MassTest.exists_unit_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:13.83271+00:00
-- url     : https://prove2.me/submissions/dbe3d92c-eb5b-4078-9156-6b77b37588cb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TestFunctionExists
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_gramR_ratTup_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MassTest
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
namespace GlobalTheory.CompanionTheory.SW.MassTest
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {J : Matrix (Fin 2) (Fin 2) E}
    (hA : Aniso σ J) : ∃ X : Fin 1 → Fin 2 → R ⊗[F] E, IsUnit (gramR R σ J X).det := by
  have hx : hE σ J (fun _ => 1) (fun _ => 1) ≠ 0 := fun h => one_ne_zero (congrFun (hA _ h) 0)
  refine ⟨ratTup R fun _ _ => 1, ?_⟩
  rw [Matrix.det_fin_one, gramR_ratTup_apply]
  exact (IsUnit.mk0 _ hx).map (inclR R)
end GlobalTheory.CompanionTheory.SW.MassTest
