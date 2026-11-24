-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_prod_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:26:46.551995+00:00
-- url     : https://prove2.me/submissions/0e4c89a4-d33a-412c-bed2-78790ea35bb8

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_mapMatrix_liftT_same

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArtinElem
variable {K K' : Type*} [CommRing K] [CommRing K'] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [DecidableEq M] {F : M → Type*} [∀ m, CommRing (F m)]
namespace GlobalTheory.CompanionTheory.SW.ArtinElem
theorem _root_.solution (e : K ≃+* ∀ m, F m) (m : M) (T : List (TransvectionStruct ι (F m))) :
    (coord e m).mapMatrix (((T.map (liftT e m)).map TransvectionStruct.toMatrix).prod) =
      (T.map TransvectionStruct.toMatrix).prod := by
  induction T with
  | nil => simp
  | cons t T ih => simp only [List.map_cons, List.prod_cons, map_mul, ih, mapMatrix_liftT_same]
end GlobalTheory.CompanionTheory.SW.ArtinElem
