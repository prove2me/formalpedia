-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.idx_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:11:50.322057+00:00
-- url     : https://prove2.me/submissions/f997139b-4e46-488b-aa4c-def16a9bfac0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_inf_left

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
theorem _root_.solution {X B I : Submodule R W} (h : I ≤ B) : idx (X ⊔ I) B = idx X B := by
  have e : X ⊔ I = X ⊔ ((X ⊔ I) ⊓ B) :=
    le_antisymm (sup_le le_sup_left (le_sup_of_le_right (le_inf le_sup_right h)))
      (sup_le le_sup_left inf_le_left)
  rw [← idx_inf_left]
  set T := (X ⊔ I) ⊓ B with hT
  have e2 : X ⊓ T = X ⊓ B := by rw [hT, ← inf_assoc, inf_sup_self]
  rw [e, ← idx_inf_left X B, ← e2, idx_inf_left]
  unfold idx
  rw [Submodule.sup_toAddSubgroup]
  exact AddSubgroup.relIndex_sup_right _ _
end GlobalTheory.DegCnt.DelScale
