-- Prove2me | solution 1 for GlobalTheory.Mass.LineGlue.sup_span_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:32:24.127054+00:00
-- url     : https://prove2.me/submissions/d1cac4f4-e13b-43ce-aa20-972b4953ee6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LineGlue
namespace GlobalTheory.Mass.LineGlue
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (B : Submodule R W) {y z : W} (hyz : y - z ∈ B) :
    B ⊔ Submodule.span R {y} = B ⊔ Submodule.span R {z} := by
  have key : ∀ {y z : W}, y - z ∈ B → B ⊔ Submodule.span R {y} ≤ B ⊔ Submodule.span R {z} := by
    intro y z hyz
    refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    have := add_mem (Submodule.mem_sup_left hyz : y - z ∈ B ⊔ Submodule.span R {z})
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
    simpa using this
  exact le_antisymm (key hyz) (key (by simpa using B.neg_mem hyz))
end GlobalTheory.Mass.LineGlue
