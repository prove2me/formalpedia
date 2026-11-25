-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.span_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:31:56.098952+00:00
-- url     : https://prove2.me/submissions/6291fa52-0e1d-4a74-9d7d-11dc8c91ed48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_exists_mul

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
theorem _root_.solution {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (S : Submodule K V) :
    Submodule.span K ((Λ ⊓ rs (𝓞 K) S : Submodule (𝓞 K) V) : Set V) = S := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun x hx => ?_
  obtain ⟨n, hn, h⟩ := exists_mul hΛ x
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
  have : x = (n : K)⁻¹ • ((n : K) • x) := by rw [smul_smul, inv_mul_cancel₀ hn', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, S.smul_mem _ hx⟩)
end GlobalTheory.DegCnt.SplitIdx
