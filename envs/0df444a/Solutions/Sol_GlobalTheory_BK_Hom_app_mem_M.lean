-- Prove2me | solution 1 for GlobalTheory.BK.Hom.app_mem_M
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:18.611531+00:00
-- url     : https://prove2.me/submissions/ee4e390d-cf60-4df0-8499-0afb487a00c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_Hom_app_mem_Mext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
variable {O K l e a ι} [Fact l.Prime] {κ μ : Type} [Fintype κ] [DecidableEq κ] [Fintype μ]
  [DecidableEq μ]
open GlobalTheory.BK.Hom
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
namespace GlobalTheory.BK.Hom
theorem _root_.solution (F : Hom P Q) {v : Vec K a ι} (hv : v ∈ P.M) : F.app v ∈ Q.M :=
  F.app_mem_Mext le_rfl hv
end GlobalTheory.BK.Hom
