-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.gidx_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:34.059199+00:00
-- url     : https://prove2.me/submissions/c9ebbdf1-5dcc-4316-b565-2c74a35b3d90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_inf_left
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_inf_right
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_mul

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
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace GlobalTheory.DegCnt.DelScale
theorem _root_.solution {A B N : Submodule R W} (h1 : N ≤ A) (h2 : N ≤ B) (hA : idx A N ≠ 0) :
    gidx A B = (idx A N : ℝ) / idx B N := by
  have a := idx_mul (le_inf h1 h2) (inf_le_left : A ⊓ B ≤ A)
  have b := idx_mul (le_inf h1 h2) (inf_le_right : A ⊓ B ≤ B)
  rw [idx_inf_left] at a
  rw [idx_inf_right] at b
  have h0 : idx (A ⊓ B) N ≠ 0 := fun e => hA (by rw [← a, e, zero_mul])
  rw [gidx, ← a, ← b]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast h0)]
end GlobalTheory.DegCnt.DelScale
