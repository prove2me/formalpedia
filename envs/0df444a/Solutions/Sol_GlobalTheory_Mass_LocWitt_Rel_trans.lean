-- Prove2me | solution 1 for GlobalTheory.Mass.LocWitt.Rel.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:29:27.449954+00:00
-- url     : https://prove2.me/submissions/029c37d0-364e-452e-bfcf-241a06783ca6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.LocWitt
namespace Rel
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {Λ : AddSubgroup V} {x y z : V}
    (a : Rel h Λ x y) (b : Rel h Λ y z) : Rel h Λ x z := by
  obtain ⟨g, hg, g1, g2⟩ := a
  obtain ⟨k, hk, k1, k2⟩ := b
  refine ⟨k * g, (isom h).mul_mem hk hg, fun v => (k1 _).trans (g1 v), ?_⟩
  change k (g x) = z
  rw [g2, k2]
end Rel
end GlobalTheory.Mass.LocWitt
