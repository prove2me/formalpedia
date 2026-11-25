-- Prove2me | solution 1 for GlobalTheory.UnipStab.hermFlagUnipotent_anisotropic_vector_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:39.836379+00:00
-- url     : https://prove2.me/submissions/b6e80269-a229-485a-972a-011794614a38

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
variable {F}
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r)
variable {F}
namespace GlobalTheory.UnipStab
namespace _root_.GlobalTheory.UnipStab
theorem _root_.solution {g : V →ₗ[K] V} (hg : F.InN g) :
    g F.z - F.z ∈ F.X := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hg
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.z
  exact hg.2.2.2 _ F.zperp
end _root_.GlobalTheory.UnipStab
end GlobalTheory.UnipStab
