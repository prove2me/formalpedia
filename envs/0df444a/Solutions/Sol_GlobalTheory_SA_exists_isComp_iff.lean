-- Prove2me | solution 1 for GlobalTheory.SA.exists_isComp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:04.53097+00:00
-- url     : https://prove2.me/submissions/1dfff497-1b0f-483c-9418-614dc3894487

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
namespace GlobalTheory.SA
theorem _root_.solution (F F' : FlagD H r) (u : V) : (∃ a a', IsComp F F' u a a') ↔ u ∈ V0 F F' := by
  constructor
  · rintro ⟨a, a', h⟩
    exact Submodule.mem_sup.2 ⟨_, h, a • F.z + a' • F'.z, Submodule.mem_span_pair.2 ⟨a, a', rfl⟩, by abel⟩
  · intro h
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, a', rfl⟩ := Submodule.mem_span_pair.1 hy
    refine ⟨a, a', ?_⟩
    unfold IsComp
    convert hx using 1
    abel
end GlobalTheory.SA
