-- Prove2me | solution 1 for GlobalTheory.UnipStab.Xa_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:08.204285+00:00
-- url     : https://prove2.me/submissions/253c4bed-0028-4f75-8f23-d3d82afa6c44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnipStab
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (F : FlagD H r)
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r)
namespace GlobalTheory.UnipStab
namespace _root_.GlobalTheory.UnipStab
theorem _root_.solution {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  refine Submodule.span_mono (Set.image_mono fun c hc => ?_)
  have hc' : (c : ℕ) < a := hc
  exact lt_of_lt_of_le hc' h
end _root_.GlobalTheory.UnipStab
end GlobalTheory.UnipStab
