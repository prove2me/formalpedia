-- Prove2me | solution 1 for GlobalTheory.BK.Hom.app_mem_Mext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:52:49.795272+00:00
-- url     : https://prove2.me/submissions/0d48a4e5-4fc3-4d26-94ef-205ca70adc19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_mem_tot

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
theorem _root_.solution (F : Hom P Q) {B : Subalgebra O K⟦X⟧} (hB : A O K ≤ B) {v : Vec K a ι}
    (hv : v ∈ P.Mext B) : F.app v ∈ Q.Mext B :=
  mem_tot.2 fun τ i => Subalgebra.sum_mem _ fun j _ =>
    mul_mem (hB (F.mem τ i j)) (mem_tot.1 hv τ j)
end GlobalTheory.BK.Hom
