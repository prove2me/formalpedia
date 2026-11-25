-- Prove2me | solution 1 for GlobalTheory.UnimodQuot.mem_of_perp_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:05.116986+00:00
-- url     : https://prove2.me/submissions/cb3a85f4-d42f-4b94-894d-d6c456ab1998

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Theorems.Thm_GlobalTheory_UnimodQuot_exists_rep
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff


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
open GlobalTheory GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace GlobalTheory.UnimodQuot
theorem _root_.solution (H : HermSpace K V) (I : Submodule K V) {v : V}
    (hv : ∀ x ∈ perp H I, H.B x v = 0) : v ∈ I := by
  by_contra h
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  obtain ⟨w, hw⟩ := exists_rep H f
  have hwI : w ∈ perp H I := by
    rw [mem_perp_iff]
    intro x hx
    have : f x = 0 := by
      have : f x ∈ I.map f := Submodule.mem_map_of_mem hx
      rwa [hf0, Submodule.mem_bot] at this
    rw [← H.herm, hw, this, star_zero]
  apply hf
  rw [← hw, ← H.herm, hv w hwI, star_zero]
end GlobalTheory.UnimodQuot
