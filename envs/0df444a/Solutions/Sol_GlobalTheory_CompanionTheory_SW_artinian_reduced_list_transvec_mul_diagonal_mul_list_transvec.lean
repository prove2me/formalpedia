-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:22:02.574434+00:00
-- url     : https://prove2.me/submissions/2c924158-b364-43c8-8173-e9f019f8f6ee

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_factor_of_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution
    (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (D : ι → K),
      A = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
  classical
  letI : Fintype (MaximalSpectrum K) := Fintype.ofFinite _
  refine ArtinElem.factor_of_pi (F := fun m : MaximalSpectrum K => K ⧸ m.asIdeal)
    (IsArtinianRing.equivPi K).toRingEquiv (fun m B => ?_) A
  letI : Field (K ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec B
end GlobalTheory.CompanionTheory.SW
