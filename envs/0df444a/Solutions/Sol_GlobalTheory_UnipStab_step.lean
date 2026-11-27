-- Prove2me | solution 1 for GlobalTheory.UnipStab.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:15.48+00:00
-- url     : https://prove2.me/submissions/2b11233b-2152-4fa7-a6c5-d6c39e9ef6af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Theorems.Thm_GlobalTheory_UnipStab_Xa_mono

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
open GlobalTheory GlobalTheory.UnipStab
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (F : FlagD H r)
variable {F}
namespace GlobalTheory.UnipStab
theorem _root_.solution {g : V →ₗ[K] V} (hg : F.InN g) (a : ℕ) {x : V} (hx : x ∈ F.Xa (a + 1)) :
    g x - x ∈ F.Xa a := by
  have : F.Xa (a + 1) ≤ (F.Xa a).comap (g - LinearMap.id) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    exact Xa_mono F (Nat.lt_succ_iff.1 hb) (hg.2.2.1 b)
  exact this hx
end GlobalTheory.UnipStab
