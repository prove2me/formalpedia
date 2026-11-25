-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.hatSpan_extc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:28:45.754239+00:00
-- url     : https://prove2.me/submissions/4b8f9fbb-97ce-4a1b-b091-bd3e0970a751

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_PhiMod_mx_mem
import Theorems.Thm_GlobalTheory_BK_hat_of_mem
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_invE_A_le_RpiE
import Theorems.Thm_GlobalTheory_BK_toHatE_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.hat_coe

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
variable {O K}
variable {ι}
open GlobalTheory.BK.PhiMod
variable {l e a} (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution {B : Subalgebra O K⟦X⟧} (hB : B ≤ Rpi O K l e) (τ : ZMod a) :
    hatSpan O l e (P.extc B τ) =
      Submodule.span _ (Set.range fun j => hatV O l e ((P.mx τ).col j)) := by
  have hX (i j : ι) : P.mx τ i j ∈ RpiE O K l e := invE_A_le_RpiE l e (P.mx_mem τ i j)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨v, ⟨hv, -⟩, rfl⟩
    obtain ⟨m, hm, rfl⟩ := P.mem_extc.1 hv
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun j => toHat O K l e ⟨m j, hB (hm j)⟩, funext fun i => ?_⟩
    have : (P.mx τ *ᵥ m) i = ((∑ j, ⟨m j, le_away _ _ (hB (hm j))⟩ * ⟨P.mx τ i j, hX i j⟩ :
        RpiE O K l e) : K⟦X⟧) := by
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [hatV, this, hat_coe, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Pi.smul_apply, Algebra.smul_def, hatV, Matrix.col_apply, hat_of_mem l e (hX i j),
      toHatE_eq l e (f := ⟨m j, le_away _ _ (hB (hm j))⟩) (g := ⟨m j, hB (hm j)⟩) rfl]
  · rintro _ ⟨j, rfl⟩
    exact ⟨_, ⟨Submodule.subset_span ⟨j, rfl⟩, fun i => hX i j⟩, rfl⟩
end GlobalTheory.BK.PhiMod
