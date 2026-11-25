-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.mem_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:36.431005+00:00
-- url     : https://prove2.me/submissions/9d711ebc-1dc5-4ce3-89ea-87aa0ba5a2eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (a : Fin r) (t : K) :
    t ∈ lead F Λ a.castSucc ↔ ∃ x ∈ Λ, x - t • F.e a.castSucc ∈ F.Xa a.val := by
  change t • F.e a.castSucc ∈ Λ ⊔ rs (𝓞 K) (F.Xa a.val) ↔ _
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx, y, hy, e⟩
    exact ⟨x, hx, by rw [← e]; simpa using (F.Xa a.val).neg_mem hy⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, _, (F.Xa a.val).neg_mem h, by abel⟩
end GlobalTheory.DegCnt.SplitIdx
