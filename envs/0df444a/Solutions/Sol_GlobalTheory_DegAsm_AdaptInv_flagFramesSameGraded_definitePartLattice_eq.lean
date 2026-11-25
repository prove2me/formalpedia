-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.flagFramesSameGraded_definitePartLattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:57:52.212469+00:00
-- url     : https://prove2.me/submissions/0b32f6f2-f905-4259-b9a6-c9b4a62c61bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_sitesCommonSpace_v0_eq_Vp
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_latL_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.DegAsm.AdaptInv
namespace _root_.GlobalTheory.DegAsm.AdaptInv
theorem _root_.solution {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (Λ : Submodule R V) :
    _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice G G' Λ = _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice F F' Λ := by
  unfold _root_.GlobalTheory.HermLat.flagPairDefinitePartLattice _root_.GlobalTheory.HermLat.wSp
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.latL_eq h h',
    _root_.GlobalTheory.DegAsm.AdaptInv.sitesCommonSpace_v0_eq_Vp h h']
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
