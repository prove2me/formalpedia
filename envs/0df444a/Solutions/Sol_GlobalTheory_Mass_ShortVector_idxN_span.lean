-- Prove2me | solution 1 for GlobalTheory.Mass.ShortVector.idxN_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:42:53.604714+00:00
-- url     : https://prove2.me/submissions/b2450b56-4d18-45a7-9a3b-2cb2de828c97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ShortVector
open GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.ShortVector
theorem _root_.solution (x : V) (S : Submodule (𝓞 K) V) :
    idxN (Submodule.span (𝓞 K) {x}) S =
      Ideal.absNorm (S.comap (LinearMap.toSpanSingleton (𝓞 K) V x) : Ideal (𝓞 K)) := by
  have hr : (Submodule.span (𝓞 K) {x}).toAddSubgroup =
      (⊤ : AddSubgroup (𝓞 K)).map (LinearMap.toSpanSingleton (𝓞 K) V x).toAddMonoidHom := by
    ext y
    simp [Submodule.mem_span_singleton]
  unfold idxN
  rw [hr, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl
end GlobalTheory.Mass.ShortVector
