-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.mem_iff_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:10:28.758937+00:00
-- url     : https://prove2.me/submissions/28a728e5-134a-4160-b4d8-f15b76abe940

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
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) {ι : Type} (L : Submodule (A K hd) V)
    [Submodule.IsLattice K L] (c : Module.Basis ι (A K hd) L) (x : V) :
    x ∈ L ↔ ∀ i, (c.extendOfIsLattice K).repr x i ∈ A K hd := by
  have h : Submodule.span (A K hd) (Set.range (c.extendOfIsLattice K)) = L := by
    have : Set.range (c.extendOfIsLattice K) = L.subtype '' Set.range c := by
      rw [← Set.range_comp]; congr 1; funext i; simp
    rw [this, Submodule.span_image, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  conv_lhs => rw [← h]
  rw [Module.Basis.mem_span_iff_repr_mem]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2
end GlobalTheory.Mass.SemiBasis
