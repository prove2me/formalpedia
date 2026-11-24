-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.smul_mem_ext_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:43.420271+00:00
-- url     : https://prove2.me/submissions/8e6ce191-4932-475e-a336-323897aeb159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_PhiMod_ext_mono
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_tot_mem_ext
import Theorems.Thm_GlobalTheory_BK_eq_sum_bas
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
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.PhiMod
omit [NeZero a] [TameDescentExponentData K l e a]
variable (P : PhiMod O K l e a ι)
omit [NormedAlgebra ℚ_[l] K] [NeZero e] [Fact l.Prime]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {c : K⟦X⟧} (h : ∀ i, c • bas i ∈ P.L) {B : Subalgebra O K⟦X⟧}
    (hB : A O K ≤ B) {m : Vec K a ι} (hm : m ∈ P.Mext B) : c • m ∈ P.ext B := by
  rw [eq_sum_bas m, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact P.smul_tot_mem_ext (fun τ => mem_tot.1 hm τ i) (P.ext_mono hB (h i))
end GlobalTheory.BK.PhiMod
