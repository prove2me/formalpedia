-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.exists_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:25.320532+00:00
-- url     : https://prove2.me/submissions/f35e9310-6283-407f-aead-6e3e9dca0239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero


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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (x : V) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K) • x ∈ Λ := by
  refine ⟨_, idxN_ne_zero hΛ (Submodule.fg_span_singleton x), ?_⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem Λ.toAddSubgroup
    (K := (Submodule.span (𝓞 K) {x}).toAddSubgroup) (Submodule.mem_span_singleton_self x)
end GlobalTheory.DegCnt.SplitIdx
