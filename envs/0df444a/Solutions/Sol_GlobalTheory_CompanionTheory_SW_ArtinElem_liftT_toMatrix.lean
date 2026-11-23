-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArtinElem.liftT_toMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:41.893676+00:00
-- url     : https://prove2.me/submissions/95aabe3e-a62a-497b-a0d7-e4370ccfd6ed

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
theorem _root_.solution (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (liftT e m t).toMatrix = 1 + single t.i t.j (e.symm (Pi.single m t.c)) := rfl
end GlobalTheory.CompanionTheory.SW.ArtinElem
