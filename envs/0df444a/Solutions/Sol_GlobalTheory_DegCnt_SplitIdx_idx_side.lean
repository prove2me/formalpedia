-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.idx_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:54.210681+00:00
-- url     : https://prove2.me/submissions/e9a293ea-7dcc-45f1-834c-e5eaf927a9f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_idx_congr
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_Xa_mono
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_sup
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
theorem _root_.solution (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) {j : ℕ} (hj : j ≤ r) {P : Submodule (𝓞 K) V}
    (h1 : P ≤ rs (𝓞 K) F'.X) (h2 : rs (𝓞 K) (II F F') ≤ P) :
    idx ((Λ ⊓ rs (𝓞 K) F.X) ⊔ P) (latF F Λ j ⊔ P) = bOne F F' Λ j := by
  rw [idx_sup le_sup_right]
  refine idx_congr (le_antisymm ?_ (inf_le_inf_left _ (sup_le_sup_left (inf_le_right.trans h2) _)))
  rintro x ⟨hx, h⟩
  obtain ⟨y, hy, p, hp, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨hx, Submodule.add_mem_sup hy ⟨by simpa using Λ.sub_mem hx.1 hy.1, ?_, h1 hp⟩⟩
  simpa using F.X.sub_mem hx.2 (Xa_mono F hj hy.2)
end GlobalTheory.DegCnt.SplitIdx
