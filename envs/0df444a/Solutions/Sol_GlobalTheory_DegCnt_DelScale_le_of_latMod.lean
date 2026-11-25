-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.le_of_latMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:39.08432+00:00
-- url     : https://prove2.me/submissions/34ba1a60-d81a-4670-b019-ed94a0e41647

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DelScale
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {S I C : Submodule K V} (p : V →ₗ[K] V) (hCS : C ≤ S) (hpC : ∀ x ∈ S, p x ∈ C)
  (hpI : ∀ x, x - p x ∈ I) (hI : ∀ x ∈ I, p x = 0) (hC : ∀ x ∈ C, p x = x)
omit [NumberField K] [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.DelScale
theorem _root_.solution {M : Submodule (𝓞 K) V} (hM : IsLatMod M S I) :
    rs (𝓞 K) I ≤ M ∧ M ≤ rs (𝓞 K) S := by
  obtain ⟨⟨N, -, hN⟩, hs⟩ := hM
  exact ⟨hN ▸ le_sup_right, fun x hx => hs ▸ Submodule.subset_span hx⟩
end GlobalTheory.DegCnt.DelScale
