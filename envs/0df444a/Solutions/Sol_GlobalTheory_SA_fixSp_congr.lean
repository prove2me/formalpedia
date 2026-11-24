-- Prove2me | solution 1 for GlobalTheory.SA.fixSp_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:18.334341+00:00
-- url     : https://prove2.me/submissions/10e8c7f5-2ca3-4188-8b62-1690e9e75c49

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
variable {F F' F'' : FlagD H r} {Λ : Submodule R V} {g : R} {β : V ≃ₗ[K] V}
namespace GlobalTheory.SA
theorem _root_.solution {β₁ : V ≃ₗ[K] V} (he : ∀ x ∈ perp H F'.X, β₁ x - β x ∈ F''.X) :
    fixSp F F' F'' β₁ = fixSp F F' F'' β := by
  ext x
  refine and_congr_right fun hx => exists_congr fun y => and_congr_right fun _ => and_congr_right fun _ => ?_
  have h1 := he x (perp_anti (S := F'.X) (S' := V0 F F') (le_sup_of_le_left le_sup_right) hx)
  rw [← Submodule.add_mem_iff_right _ h1 (y := β x - y), sub_add_sub_cancel]
end GlobalTheory.SA
