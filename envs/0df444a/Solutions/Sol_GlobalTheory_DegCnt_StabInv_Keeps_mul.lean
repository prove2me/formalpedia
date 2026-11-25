-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.Keeps.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:47.708936+00:00
-- url     : https://prove2.me/submissions/633fe728-bcdf-4a70-93f3-1a19f1cb9072

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_Keeps_flagX
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.StabInv
namespace Keeps
theorem _root_.solution {F : FlagD H r} {s t : V ≃ₗ[K] V} (hs : Keeps F s) (ht : Keeps F t) :
    Keeps F (s * t) := by
  refine ⟨fun x y => ?_, fun a x => ?_, fun a => ?_, fun y hy => ?_⟩
  · simp [hs.iso, ht.iso]
  · simp [hs.flag, ht.flag]
  · have h1 := (hs.flag _ _).2 (ht.vec a)
    have h2 := add_mem h1 (hs.vec a)
    simpa using h2
  · have h1 := (hs.flagX _).2 (ht.mid y hy)
    have h2 := add_mem h1 (hs.mid y hy)
    simpa using h2
end Keeps
end GlobalTheory.DegCnt.StabInv
