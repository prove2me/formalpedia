-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.NormOneHaar.char_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:27.65685+00:00
-- url     : https://prove2.me/submissions/7d77a1e0-c797-4565-8c1a-9df33d9895aa

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
theorem _root_.solution (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) (u v : K)
    (h : u * v = 1) (h' : σ u * σ v = 1) :
    addEquivAddHaarChar (mulEquiv (σ u) (σ v) h') = addEquivAddHaarChar (mulEquiv u v h) := by
  set s := invEquiv σ hc hi
  have e : mulEquiv (σ u) (σ v) h' = (s.trans (mulEquiv u v h)).trans s.symm := by
    ext y
    show σ u * y = σ (u * σ y)
    rw [map_mul, hi]
  rw [e, addEquivAddHaarChar_trans, addEquivAddHaarChar_trans, addEquivAddHaarChar_symm,
    mul_comm (addEquivAddHaarChar s), mul_assoc,
    mul_inv_cancel₀ (addEquivAddHaarChar_pos s).ne', mul_one]
end GlobalTheory.CompanionTheory.SW.NormOneHaar
