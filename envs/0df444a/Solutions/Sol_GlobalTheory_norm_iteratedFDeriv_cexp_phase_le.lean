-- Prove2me | solution 1 for GlobalTheory.norm_iteratedFDeriv_cexp_phase_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:33.766245+00:00
-- url     : https://prove2.me/submissions/d2795ed4-f86b-4985-b74e-5148aebb901a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivCexpPhaseLe
import Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_real_cexp
import Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_succ_clm_add_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open scoped Nat
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (B : V →L[ℝ] E →L[ℝ] ℂ) (h : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
      (∀ y t, (B y t + h t).re = 0) → ∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ y t, ‖t‖ ≤ R →
      ‖iteratedFDeriv ℝ n (fun t => Complex.exp (B y t + h t)) t‖ ≤ C * (1 + ‖y‖) ^ n := by
  intro V E _ _ _ _ _ _ B h hh hre n R
  set F : E → ℝ := fun t => ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j h t‖ with hF
  have hFc : Continuous F := by
    refine continuous_finset_sum _ (fun j _ => ?_)
    exact (hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨(n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n, fun y t ht => ?_⟩
  have htb : t ∈ Metric.closedBall (0 : E) R := by simpa using ht
  have hKj : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j h t‖ ≤ |K| := by
    intro j hj
    have h1 : ‖iteratedFDeriv ℝ j h t‖ ≤ F t :=
      Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j h t‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h2 : F t ≤ K := (le_abs_self _).trans ((Real.norm_eq_abs (F t)) ▸ hK t htb)
    exact (h1.trans h2).trans (le_abs_self K)
  set D : ℝ := (1 + ‖B‖ + |K|) * (1 + ‖y‖) with hD
  have hy0 := norm_nonneg y
  have hB0 := norm_nonneg B
  have hK0 := abs_nonneg K
  have hD1 : 1 ≤ D := by
    rw [hD]; nlinarith
  have hDge : ‖B‖ * ‖y‖ + |K| ≤ D := by
    rw [hD]; nlinarith
  have hphi : ContDiff ℝ ∞ (fun t => B y t + h t) := (B y).contDiff.add hh
  have hcomp : (fun t => Complex.exp (B y t + h t)) = Complex.exp ∘ (fun t => B y t + h t) := rfl
  rw [hcomp]
  have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (g := Complex.exp) (f := fun t => B y t + h t)
    (n := n) (N := ∞) Complex.contDiff_exp hphi (by exact_mod_cast le_top) t (C := 1) (D := D)
    (fun i _ => by rw [norm_iteratedFDeriv_real_cexp, hre y t, Real.exp_zero])
    (fun i hi1 hin => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      calc ‖iteratedFDeriv ℝ (j + 1) (fun t => B y t + h t) t‖
          ≤ ‖B y‖ + ‖iteratedFDeriv ℝ (j + 1) h t‖ :=
            norm_iteratedFDeriv_succ_clm_add_le (B y) h hh j t
        _ ≤ ‖B‖ * ‖y‖ + |K| := add_le_add (B.le_opNorm y) (hKj _ hin)
        _ ≤ D := hDge
        _ ≤ D ^ (j + 1) := le_self_pow₀ hD1 (by omega))
  calc _ ≤ (n ! : ℝ) * 1 * D ^ n := key
    _ = (n ! : ℝ) * (1 + ‖B‖ + |K|) ^ n * (1 + ‖y‖) ^ n := by rw [hD, mul_pow]; ring
end GlobalTheory
