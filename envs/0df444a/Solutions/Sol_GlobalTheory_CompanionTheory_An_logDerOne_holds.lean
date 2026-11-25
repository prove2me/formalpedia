-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.An.logDerOne_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:37.958156+00:00
-- url     : https://prove2.me/submissions/e5db5367-7655-47fc-a414-a03734e720c7

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__LogDerOne_a1ce1da79bfc3842
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_OneLeNormOneSub
import Theorems.Thm_GlobalTheory_CompanionTheory_An_one_le_norm_one_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_An_norm_sub_two_le
import Theorems.Thm_GlobalTheory_LWide_logDeriv_LFunction_strip


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.An
open GlobalTheory.Mem.An
namespace GlobalTheory.CompanionTheory.An
theorem _root_.solution : LogDerOne := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hχ => ?_⟩
  have h1 : χ ≠ 1 := by
    rintro rfl
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero h1
  obtain ⟨hW, hcount, hmain⟩ := H q χ h1 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hW hcount hmain
  set W : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hWdef
  set B : Set ℂ := zerosIn χ 0 1 with hBdef
  set g : ℂ → ℂ := fun w => (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) with hg
  have hBW : B ⊆ W := fun w hw => ⟨norm_sub_two_le hw, hw.2.2.2⟩
  have hz : zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) = ∑ᶠ w ∈ B, g w := by
    unfold zsum zmult
    refine finsum_mem_congr rfl fun w _ => ?_
    simp only [hg, mul_one_div]
  have hsplit : ∑ᶠ w ∈ B, g w + ∑ᶠ w ∈ W \ B, g w = ∑ᶠ w ∈ W, g w :=
    finsum_mem_add_sdiff hBW hW
  have hD : ‖∑ᶠ w ∈ W \ B, g w‖ ≤ ∑ᶠ w ∈ W, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    have hfin : (W \ B).Finite := hW.subset Set.diff_subset
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hW]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ w ∈ hfin.toFinset, ‖g w‖
        ≤ ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw' : w ∈ W \ B := by simpa using hw
          have h2 := one_le_norm_one_sub h1 hw'.1.2 hw'.2
          simp only [hg, norm_div, Complex.norm_natCast]
          exact div_le_self (Nat.cast_nonneg _) h2
      _ ≤ ∑ w ∈ hW.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
          intro x hx
          simp only [Set.Finite.mem_toFinset] at hx ⊢
          exact hx.1
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    exact Real.log_le_log (by positivity) (by linarith)
  rw [hz]
  have hmain' : ‖deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w‖ ≤ C * Real.log (q * 2) := hmain
  have e : deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ B, g w =
      (deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w) + ∑ᶠ w ∈ W \ B, g w := by
    rw [← hsplit]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h3 := hD.trans hcount
  have h4 := mul_le_mul_of_nonneg_left hlog hC.le
  linarith
end GlobalTheory.CompanionTheory.An
