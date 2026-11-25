-- Prove2me | solution 1 for GlobalTheory.DegCnt.Glue.span_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:25.134846+00:00
-- url     : https://prove2.me/submissions/e279a41b-821b-4388-ba07-ef385a1cc729

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
import Theorems.Thm_GlobalTheory_UnimodQuot_exists_smul_mem


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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Glue
open TensorProduct
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.Glue
theorem _root_.solution {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (S : Submodule K V) :
    Submodule.span K ((L ⊓ rs (𝓞 K) S : Submodule (𝓞 K) V) : Set V) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun x hx => hx.2
  · intro v hv
    obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem hL v
    have hc := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) s.2
    rw [← Submodule.smul_mem_iff _ hc]
    refine Submodule.subset_span ⟨?_, S.smul_mem _ hv⟩
    rw [algebraMap_smul]
    exact hs
end GlobalTheory.DegCnt.Glue
