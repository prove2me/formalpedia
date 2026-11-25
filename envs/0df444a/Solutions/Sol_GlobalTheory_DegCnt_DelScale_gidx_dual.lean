-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.gidx_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:21.105643+00:00
-- url     : https://prove2.me/submissions/3d1478eb-3c19-499b-beb0-09a15537c116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_eq
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_gidx_of_le
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_gidx_of_ge
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_dual
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero


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
    gidx (Formalism.HermitianLatticesTheory.dual h A) (Formalism.HermitianLatticesTheory.dual h B) = gidx B A := by
  have dl := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hn Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  have an := (Formalism.HermitianLatticesTheory.dualBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).1
  have hL : Submodule.IsLattice K (A ⊔ B) := Submodule.IsLattice.sup K A B
  rw [gidx_of_le (an _ _ (le_sup_left : A ≤ A ⊔ B)) (an _ _ (le_sup_right : B ≤ A ⊔ B))
      (idxN_ne_zero (dl _ hL).1 (dl _ hA).1.fg),
    gidx_of_ge (le_sup_right : B ≤ A ⊔ B) (le_sup_left : A ≤ A ⊔ B) (idxN_ne_zero hB hL.fg)
      (idxN_ne_zero hB hA.fg)]
  rw [idx_eq (Formalism.HermitianLatticesTheory.dual h A), idx_eq (Formalism.HermitianLatticesTheory.dual h B), idxN_dual h hs hn hA _ _ hL le_sup_left rfl,
    idxN_dual h hs hn hB _ _ hL le_sup_right rfl]
  rfl
end GlobalTheory.DegCnt.DelScale
