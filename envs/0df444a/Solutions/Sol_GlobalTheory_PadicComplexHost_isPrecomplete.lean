-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.isPrecomplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:33:22.120061+00:00
-- url     : https://prove2.me/submissions/f535c0e4-a239-4bee-8b1b-977c0c25aaf0

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Theorems.Thm_GlobalTheory_PadicComplexHost_inv_p_lt_one
import Theorems.Thm_GlobalTheory_PadicComplexHost_mem_iff_norm
import Theorems.Thm_GlobalTheory_PadicComplexHost_smodEq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
open GlobalTheory GlobalTheory.PadicComplexHost
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.PadicComplexHost
theorem _root_.solution : IsPrecomplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun f hf => ?_⟩
  have h : ∀ {m n : ℕ}, m ≤ n → ‖(f m : ℂ_[p]) - (f n : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ m :=
    fun hmn => (smodEq_iff p _ _ _).1 (hf hmn)
  have hc : CauchySeq fun n => (f n : ℂ_[p]) := by
    refine cauchySeq_of_le_geometric (p : ℝ)⁻¹ 1 (inv_p_lt_one p) fun n => ?_
    rw [dist_eq_norm, one_mul]
    exact h (Nat.le_succ n)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hm : ∀ m : ℕ, ‖(f m : ℂ_[p]) - L‖ ≤ (p : ℝ)⁻¹ ^ m := fun m =>
    le_of_tendsto ((tendsto_const_nhds.sub hL).norm)
      ((Filter.eventually_ge_atTop m).mono fun n hn => h hn)
  have hLO : L ∈ 𝓞_ℂ_[p] := by
    rw [mem_iff_norm]
    exact le_of_tendsto hL.norm
      (Filter.Eventually.of_forall fun n => (mem_iff_norm p _).1 (f n).2)
  exact ⟨⟨L, hLO⟩, fun n => (smodEq_iff p n _ _).2 (hm n)⟩
end GlobalTheory.PadicComplexHost
