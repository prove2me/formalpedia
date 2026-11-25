-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.exists_exponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:37.382883+00:00
-- url     : https://prove2.me/submissions/f21ae943-0e08-4ae4-a56e-1795e6976ab9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_mem_tot
import Theorems.Thm_GlobalTheory_BK_PhiMod_mx_mem
import Theorems.Thm_GlobalTheory_BK_PhiMod_mxInv_mem

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
open GlobalTheory.BK.PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution [NeZero a] : ∃ α β : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) ∧
    ∀ v ∈ P.M, E K l e ^ β • v ∈ P.L := by
  have key (Y : ZMod a → Matrix ι ι K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) :
      ∃ n : ℕ, ∀ τ, ∀ m ∈ vecs ι (A O K), E K l e ^ n • (Y τ *ᵥ m) ∈ vecs ι (A O K) := by
    choose n hn using fun p : ZMod a × ι × ι => hY p.1 p.2.1 p.2.2
    refine ⟨Finset.univ.sup n, fun τ m hm i => ?_⟩
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
    rw [hc, pow_add, mul_assoc, ← mul_assoc (E K l e ^ n _)]
    exact mul_mem (pow_mem (E_mem l e _) c) (mul_mem (hn (τ, i, j)) (hm j))
  obtain ⟨α, hα⟩ := key P.mx P.mx_mem
  obtain ⟨β, hβ⟩ := key P.mxInv P.mxInv_mem
  refine ⟨α, β, fun v hv => mem_tot.2 fun τ => ?_, fun v hv => mem_tot.2 fun τ => ?_⟩
  · obtain ⟨m, hm, h⟩ := P.mem_extc.1 (mem_tot.1 hv τ)
    rw [Pi.smul_apply, h]
    exact hα τ m hm
  · rw [mem_extc_iff, Pi.smul_apply, Matrix.mulVec_smul]
    exact hβ τ _ (mem_tot.1 hv τ)
end GlobalTheory.BK.PhiMod
