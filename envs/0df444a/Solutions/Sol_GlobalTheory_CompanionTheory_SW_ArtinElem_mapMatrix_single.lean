-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:42.620856+00:00
-- url     : https://prove2.me/submissions/cbd38a92-592b-42e3-bb90-8879590c383c

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
theorem _root_.solution (f : K →+* K') (a b : ι) (c : K) :
    f.mapMatrix (single a b c) = single a b (f c) := by
  ext x y
  simp only [RingHom.mapMatrix_apply, map_apply, single_apply]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.SW.ArtinElem
