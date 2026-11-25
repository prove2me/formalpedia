-- Prove2me | solution 1 for GlobalTheory.Mass.PrimDisc.idx_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:52:08.866938+00:00
-- url     : https://prove2.me/submissions/d24bd39a-ca1a-4a81-a255-0df9e41c924e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimDisc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V] [NumberField K]
namespace GlobalTheory.Mass.PrimDisc
theorem _root_.solution (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) :
    idxN (L.map (p.restrictScalars (𝓞 K))) (latIn A L) =
      idxN (L.map (q.restrictScalars (𝓞 K))) (latIn B L) := by
  unfold idxN
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right]
  conv_rhs => rw [← AddSubgroup.inf_relIndex_right]
  congr 1
  ext x
  change ((p x : V) ∈ L ∧ x ∈ L) ↔ ((q x : V) ∈ L ∧ x ∈ L)
  refine and_congr_left fun hx => ?_
  rw [← hpq x] at hx
  exact ⟨fun H => (L.add_mem_iff_right H).1 hx, fun H => (L.add_mem_iff_left H).1 hx⟩
end GlobalTheory.Mass.PrimDisc
