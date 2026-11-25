-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.gidx_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:40.695918+00:00
-- url     : https://prove2.me/submissions/e33c14b8-32bc-4cd5-8640-b2f715ee074d

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
theorem _root_.solution {A B L : Submodule R W} (h1 : A ≤ L) (h2 : B ≤ L) (hA : idx L A ≠ 0)
    (hB : idx B A ≠ 0) : gidx A B = (idx L B : ℝ) / idx L A := by
  have a := idx_mul (inf_le_left : A ⊓ B ≤ A) h1
  have b := idx_mul (inf_le_right : A ⊓ B ≤ B) h2
  rw [idx_inf_left] at a
  rw [idx_inf_right, ← a] at b
  rw [gidx, div_eq_div_iff (by exact_mod_cast hB) (by exact_mod_cast hA)]
  rw [mul_comm (idx L B : ℝ)]
  exact_mod_cast b.symm
end GlobalTheory.DegCnt.DelScale
