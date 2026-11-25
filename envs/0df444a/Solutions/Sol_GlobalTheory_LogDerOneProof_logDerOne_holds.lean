-- Prove2me | solution 1 for GlobalTheory.LogDerOneProof.logDerOne_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:09.984408+00:00
-- url     : https://prove2.me/submissions/8c95fdc4-c484-427e-b611-9a7abec309fd

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__LogDerOne_a1ce1da79bfc3842
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogDerOneHolds
import Theorems.Thm_GlobalTheory_LWide_logDeriv_LFunction_strip


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex DirichletCharacter
open GlobalTheory GlobalTheory.LogDerOneProof
namespace GlobalTheory.LogDerOneProof
theorem _root_.solution : GlobalTheory.Mem.An.LogDerOne := by
  classical
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hp => ?_⟩
  have hne : χ ≠ 1 := by
    intro h
    have h1 : χ.conductor = q := hp
    rw [h, DirichletCharacter.conductor_one] at h1
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simp)
  obtain ⟨hfin, hcount, hmain⟩ := H q χ hne 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, abs_zero, zero_add, Complex.ofReal_zero, zero_mul, add_zero] at hfin hcount hmain
  set D : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hD
  set Z : Set ℂ := GlobalTheory.Mem.An.zerosIn χ 0 1 with hZ
  have hsub : Z ⊆ D := by
    rintro w ⟨h0, h1, h2, h3⟩
    refine ⟨?_, h3⟩
    have h4 := Complex.norm_le_abs_re_add_abs_im (w - 2)
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero] at h4 h2
    have h5 : |w.re - 2| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hZfin : Z.Finite := hfin.subset hsub
  have hsub' : hZfin.toFinset ⊆ hfin.toFinset := by
    intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    exact hsub hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hmain
  have hz : GlobalTheory.Mem.An.zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) =
      ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) := by
    unfold GlobalTheory.Mem.An.zsum
    rw [← hZ, finsum_mem_eq_finite_toFinset_sum _ hZfin]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [GlobalTheory.Mem.An.zmult]
    ring
  rw [hz]
  rw [← Finset.sum_sdiff hsub'] at hmain
  have hrest : ‖∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)‖ ≤
      ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => Nat.cast_nonneg _))
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset] at hw
    obtain ⟨⟨_, hw0⟩, hwn⟩ := hw
    have hre : w.re < 1 := by
      by_contra h
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (not_lt.1 h) hw0
    have h1 : 1 ≤ ‖1 - w‖ := by
      by_cases h0 : 0 < w.re
      · have him : 1 < |w.im| := by
          by_contra h
          exact hwn ⟨h0, hre, by simpa using not_lt.1 h, hw0⟩
        have h4 := Complex.abs_im_le_norm (1 - w)
        simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h4
        linarith
      · have h4 := Complex.re_le_norm (1 - w)
        simp only [Complex.sub_re, Complex.one_re] at h4
        linarith [not_lt.1 h0]
    rw [norm_div, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg _) h1
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : C * Real.log (q * 2) ≤ C * Real.log (3 * q) := mul_le_mul_of_nonneg_left hlog hC.le
  set A := deriv (LFunction χ) 1 / LFunction χ 1
  set R := ∑ w ∈ hfin.toFinset \ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  set S := ∑ w ∈ hZfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w)
  have e : A - S = (A - (R + S)) + R := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith
end GlobalTheory.LogDerOneProof
