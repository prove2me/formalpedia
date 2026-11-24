-- Prove2me | solution 1 for GlobalTheory.BK.mem_A_of_E_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:28.48897+00:00
-- url     : https://prove2.me/submissions/0a64169e-244d-4039-825e-63d5f6061435

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul

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
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
namespace GlobalTheory.BK
theorem _root_.solution {h : K⟦X⟧} (hh : h ∈ Rpi O K l e) (hE : E K l e * h ∈ A O K) :
    h ∈ A O K := by
  obtain ⟨b, hb⟩ := (mem_invL_A_iff l).1 (mem_invL_A_of_E_mul l e hh (le_away _ _ hE))
  have hbdd : BddAbove (Set.range fun n => ‖coeff n h‖) := ⟨b, by rintro _ ⟨n, rfl⟩; exact hb n⟩
  have hle (n : ℕ) : ‖coeff n h‖ ≤ ⨆ n, ‖coeff n h‖ := le_ciSup hbdd n
  have h1 : ⨆ n, ‖coeff n h‖ ≤ max 1 (‖(l : K)‖ * ⨆ n, ‖coeff n h‖) := ciSup_le fun n => by
    have : coeff n h = coeff (n + e) (E K l e * h) + -(l * coeff (n + e) h) := by
      rw [coeff_E_mul]; ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hE _) ?_)
    rw [norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)
  intro n
  refine (hle n).trans ?_
  rcases le_max_iff.1 h1 with h2 | h2
  · exact h2
  · nlinarith [norm_l_lt_one (K := K) l]
end GlobalTheory.BK
