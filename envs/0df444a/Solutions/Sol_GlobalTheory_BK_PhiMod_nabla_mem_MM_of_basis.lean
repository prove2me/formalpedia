-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.nabla_mem_MM_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:03.327701+00:00
-- url     : https://prove2.me/submissions/678822af-19a1-4194-bf09-a0468e49c7d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_PhiMod_eq_sum_phi_bas
import Theorems.Thm_GlobalTheory_BK_PhiMod_nabla_smul_tot
import Theorems.Thm_GlobalTheory_BK_PhiMod_smul_tot_mem_ext
import Theorems.Thm_GlobalTheory_BK_derivative_mem_S
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
omit [NormedAlgebra ℚ_[l] K] [NeZero e]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (h : ∀ i, P.nabla (P.phi (bas i)) ∈ P.MM)
    (h' : ∀ i, P.phi (bas i) ∈ P.MM) {m : Vec K a ι} (hm : m ∈ P.MM) : P.nabla m ∈ P.MM := by
  rw [P.eq_sum_phi_bas m, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc (τ) := P.mem_extc_iff.1 (mem_tot.1 hm τ) i
  rw [nabla_smul_tot]
  exact add_mem (P.smul_tot_mem_ext (fun τ => derivative_mem_S (hc τ)) (h' i))
    (P.smul_tot_mem_ext hc (h i))
end GlobalTheory.BK.PhiMod
