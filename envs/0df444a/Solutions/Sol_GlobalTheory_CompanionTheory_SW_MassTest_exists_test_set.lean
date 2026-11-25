-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MassTest.exists_test_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:04.359438+00:00
-- url     : https://prove2.me/submissions/27e5a70f-334b-4572-8e07-665f36ca2b39

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TestFunctionExists
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_exists_compactOpen
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_exists_unit_vector
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MassTest_isOpen_unit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopK_topTens_props
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_coord_measures_haar


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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace GlobalTheory.CompanionTheory.SW.MassTest
theorem _root_.solution (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hA : Aniso σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    [TotallyDisconnectedSpace R] (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hl : lam.IsAddHaarMeasure) :
    ∃ A : Set (Fin 1 → Fin 2 → R ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR R σ J X).det} ∧ coordW R b lam 1 2 A ≠ 0 ∧ coordW R b lam 1 2 A ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 2
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 2
  haveI : TotallyDisconnectedSpace (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.totallyDisconnectedSpace
  obtain ⟨X, hX⟩ := exists_unit_vector R hA
  exact exists_compactOpen _ (isOpen_unit hcm R hloc J) hX
end GlobalTheory.CompanionTheory.SW.MassTest
