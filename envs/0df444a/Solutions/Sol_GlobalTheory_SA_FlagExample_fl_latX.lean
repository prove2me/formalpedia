-- Prove2me | solution 1 for GlobalTheory.SA.FlagExample.fl_latX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:15.053289+00:00
-- url     : https://prove2.me/submissions/789b3d34-70c9-42db-bf87-4447fa737360

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_mem_latX
import Theorems.Thm_GlobalTheory_SA_FlagExample_mem_lat
import Theorems.Thm_GlobalTheory_SA_FlagExample_vec_mem

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
open GlobalTheory.SA.FlagExample
open NumberField Formalism.BasicNotions.Examples₂
variable (E : Type) [Field E] [NumberField E] [StarRing E]
variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)
namespace GlobalTheory.SA.FlagExample
theorem _root_.solution : latX (fl E m s h1 h2) (wittSpace E 2 1).L0 =
    Submodule.span (𝓞 E) {vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m]} := by
  ext x
  rw [mem_latX, fl_X, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hx, a, rfl⟩
    obtain ⟨c, hc⟩ := (mem_lat E _).1 hx 2
    have e : co E (a • vec E ![1 + 2 * m, 0, 1, 2 * s, 2 * m]) 2 = a * ((1 : ℤ) : E) := rfl
    rw [e, Int.cast_one, mul_one] at hc
    exact ⟨c, by rw [← hc, algebraMap_smul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Submodule.smul_mem _ c (vec_mem E _), algebraMap _ E c, by rw [algebraMap_smul]⟩
end GlobalTheory.SA.FlagExample
