-- Prove2me | solution 1 for GlobalTheory.Mass.PrimMove.smul_mem_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:31:17.714872+00:00
-- url     : https://prove2.me/submissions/29f0e929-63a9-49b5-a1b3-e250b6e0623d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveSublatticesMoveWithIsometries

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimMove
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.Mass.PrimMove
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V) (x : V) :
    (g : V ≃ₗ[K] V) x ∈ g • L ↔ x ∈ L := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    have : w = x := (g : V ≃ₗ[K] V).injective hwx
    exact this ▸ hw
  · intro hx
    exact ⟨x, hx, rfl⟩
end GlobalTheory.Mass.PrimMove
