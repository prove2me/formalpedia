-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.isLattice_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:53:26.277859+00:00
-- url     : https://prove2.me/submissions/8e1f3358-ad2b-4d27-a0c6-86975214021c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan

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
noncomputable section
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SemiBasis
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.SemiBasis
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (M : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (Submodule.span (A K hd) (M : Set V)) where
  fg := by
    obtain ⟨s, hs⟩ := hM.fg
    refine ⟨s, ?_⟩
    rw [← hs, Submodule.span_span_of_tower]
  span_eq_top := by
    rw [Submodule.span_span_of_tower, hM.span_eq_top]
end GlobalTheory.Mass.SemiBasis
