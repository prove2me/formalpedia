-- Prove2me | solution 1 for GlobalTheory.BK.Descent.act_mem_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:30:04.471448+00:00
-- url     : https://prove2.me/submissions/e8116458-d149-416e-a71d-803f25fa4ad9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_mem_M
import Theorems.Thm_GlobalTheory_BK_PhiMod_eq_sum_phi_bas
import Theorems.Thm_GlobalTheory_BK_PhiMod_ext_mono
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_mem_L
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_tot_mem_ext
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a)
namespace GlobalTheory.BK.Descent
theorem _root_.solution {B : Subalgebra O K⟦X⟧} (hA : A O K ≤ B) (hB : Rot e B) {v : Vec K a ι}
    (hv : v ∈ P.ext B) : Δ.act g v ∈ P.ext B := by
  rw [P.eq_sum_phi_bas v, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [act_smul_tot, act_phi]
  exact P.smul_tot_mem_ext (hB.ringAct_mem g fun τ => P.mem_extc_iff.1 (mem_tot.1 hv τ) i)
    (P.ext_mono hA (P.phi_mem_L (Δ.act_mem_M g _ (P.bas_mem_M i))))
end GlobalTheory.BK.Descent
