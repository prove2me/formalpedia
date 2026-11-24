-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.NormOneHaar.char_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:28.323333+00:00
-- url     : https://prove2.me/submissions/05bafcad-3d2d-4d29-9749-b3beeb0123b8

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulEqOfNormOne

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NormOneHaar
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.NormOneHaar
theorem _root_.solution (u v : K) (h : u * v = 1) (h' : v * u = 1) :
    addEquivAddHaarChar (mulEquiv u v h) * addEquivAddHaarChar (mulEquiv v u h') = 1 := by
  have e : (mulEquiv u v h).trans (mulEquiv v u h') = ContinuousAddEquiv.refl K := by
    ext y
    show v * (u * y) = y
    rw [← mul_assoc, h', one_mul]
  rw [← addEquivAddHaarChar_trans, e, addEquivAddHaarChar_refl]
end GlobalTheory.CompanionTheory.SW.NormOneHaar
