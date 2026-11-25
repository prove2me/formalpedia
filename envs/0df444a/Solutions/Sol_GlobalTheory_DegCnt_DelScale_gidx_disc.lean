-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.gidx_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:18:27.221932+00:00
-- url     : https://prove2.me/submissions/3d15557e-1c5b-40f3-a100-e434d712a6de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_gidx_mul
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_gidx_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice


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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DelScale
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn
namespace GlobalTheory.DegCnt.DelScale
theorem _root_.solution {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) :
    gidx (Formalism.HermitianLatticesTheory.dual h B) B = gidx A B ^ 2 * gidx (Formalism.HermitianLatticesTheory.dual h A) A := by
  have dl := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  rw [← gidx_mul (dl _ hB).1 (dl _ hA).1 hB, ← gidx_mul (dl _ hA).1 hA hB, gidx_dual h hs hn hB hA]
  ring
end GlobalTheory.DegCnt.DelScale
