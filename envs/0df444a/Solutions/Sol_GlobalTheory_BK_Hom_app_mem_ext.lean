-- Prove2me | solution 1 for GlobalTheory.BK.Hom.app_mem_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:42.299823+00:00
-- url     : https://prove2.me/submissions/a35af494-76cf-4371-82e7-057e54ee4980

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_mem_tot
import Theorems.Thm_GlobalTheory_BK_Hom_app_apply
import Theorems.Thm_GlobalTheory_BK_frob_mem_A


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
    (hv : v ∈ P.ext B) : F.app v ∈ Q.ext B := by
  refine mem_tot.2 fun τ => ?_
  obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 hv τ)
  rw [app_apply, h, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec]
  exact Q.mem_extc.2 ⟨_, fun i => Subalgebra.sum_mem _ fun j _ =>
    mul_mem (hB (frob_mem_A l (F.mem _ i j))) (hm j), rfl⟩
end GlobalTheory.BK.Hom
