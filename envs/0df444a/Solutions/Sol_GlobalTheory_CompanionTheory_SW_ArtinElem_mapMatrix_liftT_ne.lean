-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_liftT_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:35.966655+00:00
-- url     : https://prove2.me/submissions/33361626-3c43-4697-88a4-a5eaeb257e89

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_coord_symm_single
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_mapMatrix_single
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_liftT_toMatrix

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
theorem _root_.solution (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (t : TransvectionStruct ι (F m)) :
    (coord e m').mapMatrix (liftT e m t).toMatrix = 1 := by
  rw [liftT_toMatrix, map_add, map_one, mapMatrix_single, coord_symm_single,
    Pi.single_eq_of_ne h, single_zero, add_zero]
end GlobalTheory.CompanionTheory.SW.ArtinElem
