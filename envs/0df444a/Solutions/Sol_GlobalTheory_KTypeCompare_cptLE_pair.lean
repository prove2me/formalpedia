-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.cptLE_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:12.182267+00:00
-- url     : https://prove2.me/submissions/750b1d18-572b-46b7-befb-31b3cbd77f9f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.KTypeCompare
theorem _root_.solution {ε : Fin n → Bool} {ω Λ : Fin n → ℝ} (h : HarishChandraRootData.CptLE ε ω Λ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - ω) i ≤ 0 := by
  obtain ⟨c, hc⟩ := h
  rw [hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro x hx
  have hlt : x.1 < x.2 := (Finset.mem_filter.mp hx).2.1
  have hne : x.2 ≠ x.1 := (ne_of_lt hlt).symm
  have key : ∑ i : Fin n, ((i : ℕ) : ℝ) * ((c x : ℝ) * HarishChandraRootData.root x.1 x.2 i) =
      (c x : ℝ) * (((x.1 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)) := by
    simp only [HarishChandraRootData.root, Pi.sub_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [key]
  apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
  have : ((x.1 : ℕ) : ℝ) < ((x.2 : ℕ) : ℝ) := by exact_mod_cast hlt
  linarith
end GlobalTheory.KTypeCompare
