-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.mem_Xa_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:31:51.374348+00:00
-- url     : https://prove2.me/submissions/5af1ae7e-7bdc-4e64-bf7e-5fda71516d45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_e_mem
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
omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution (F : FlagD H r) (a : Fin r) {x : V} (hx : x ∈ F.Xa (a.val + 1)) :
    ∃ t : K, x - t • F.e a.castSucc ∈ F.Xa a.val := by
  have : F.Xa (a.val + 1) ≤ F.Xa a.val ⊔ Submodule.span K {F.e a.castSucc} := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | h
    · exact Submodule.mem_sup_left (e_mem F h)
    · obtain rfl : b = a := Fin.ext h
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (this hx)
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨t, by simpa using hy⟩
end GlobalTheory.DegCnt.SplitIdx
