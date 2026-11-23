-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArtinElem.coord_symm_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:41.767698+00:00
-- url     : https://prove2.me/submissions/414a040f-d54e-4c0c-9c50-445e0584cf4b

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition

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
theorem _root_.solution (e : K ≃+* ∀ m, F m) (m m' : M) (c : F m) :
    coord e m' (e.symm (Pi.single m c)) = (Pi.single m c : ∀ m, F m) m' := by
  simp [coord]
end GlobalTheory.CompanionTheory.SW.ArtinElem
