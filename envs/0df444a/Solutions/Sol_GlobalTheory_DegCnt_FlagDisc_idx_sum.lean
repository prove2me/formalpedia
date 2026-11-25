-- Prove2me | solution 1 for GlobalTheory.DegCnt.FlagDisc.idx_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:21.620607+00:00
-- url     : https://prove2.me/submissions/5446e821-48bc-4a42-be13-4fa76f38378b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinor
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_inf_left
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_mul
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_sup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FlagDisc
open GlobalTheory.DegCnt.DelScale GlobalTheory.DegCnt.Absorb
namespace GlobalTheory.DegCnt.FlagDisc
theorem _root_.solution {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] {A A' B B' : Submodule R W}
    (h : B ≤ A) (h' : B' ≤ A') (hd : A ⊓ A' = ⊥) : idx (A ⊔ A') (B ⊔ B') = idx A B * idx A' B' := by
  have e1 : idx (A ⊔ A') (B ⊔ A') = idx A B := by
    rw [idx_sup le_sup_right, ← idx_inf_left, inf_comm, sup_inf_assoc_of_le _ h, inf_comm, hd, sup_bot_eq]
  have hd' : B ⊓ A' = ⊥ := le_bot_iff.1 (hd ▸ inf_le_inf_right _ h)
  have e2 : idx (B ⊔ A') (B ⊔ B') = idx A' B' := by
    rw [sup_comm B A', idx_sup le_sup_left, ← idx_inf_left, inf_comm, sup_comm B, sup_inf_assoc_of_le _ h', hd',
      sup_bot_eq]
  rw [← idx_mul (sup_le_sup_left h' B) (sup_le_sup_right h A'), e1, e2, mul_comm]
end GlobalTheory.DegCnt.FlagDisc
