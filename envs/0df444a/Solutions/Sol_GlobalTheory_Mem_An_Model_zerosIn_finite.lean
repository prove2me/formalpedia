-- Prove2me | solution 1 for GlobalTheory.Mem.An.Model.zerosIn_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:00:27.819588+00:00
-- url     : https://prove2.me/submissions/00267a9f-0998-4665-9956-bc3b1da8f838

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.An.Model
private theorem finite_zeros_in_strip_box_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) (t T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ f ρ = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).reProdIm (isCompact_Icc (a := t - T) (b := t + T))) (by
      rintro ρ ⟨h1, h2, h3, -⟩
      rw [abs_le] at h3
      exact ⟨⟨h1.le, h2.le⟩, ⟨by linarith, by linarith⟩⟩)
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ x)
    (frequently_nhdsWithin_iff.mpr ((accPt_iff_frequently.mp hx).mono fun y hy => ⟨hy.2.2.2.2, hy.1⟩))
  obtain ⟨z, hz⟩ := hne
  exact hz (hzero (Set.mem_univ z))
end GlobalTheory.Mem.An.Model
end
end

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model
namespace GlobalTheory.Mem.An.Model
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t T : ℝ) :
    (zerosIn χ t T).Finite :=
  finite_zeros_in_strip_box_of_differentiable (DirichletCharacter.differentiable_LFunction hχ)
    ⟨2, DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2) (Or.inl hχ) (by norm_num)⟩ t T
end GlobalTheory.Mem.An.Model
