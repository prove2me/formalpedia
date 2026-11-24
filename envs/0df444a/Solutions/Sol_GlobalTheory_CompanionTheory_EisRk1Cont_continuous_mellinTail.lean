-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisRk1Cont.continuous_mellinTail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:56.899374+00:00
-- url     : https://prove2.me/submissions/b678c059-b8ed-4dc0-bc90-877a2bf69e8a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSetIntegralIoiOne
import Theorems.Thm_GlobalTheory_CompanionTheory_EisRk1Cont_continuous_setIntegral_Ioi_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisRk1Cont
namespace GlobalTheory.CompanionTheory.EisRk1Cont
theorem _root_.solution {X : Type*} [TopologicalSpace X] (φ : X → ℝ → ℂ)
    (hφ : ContinuousOn (fun q : X × ℝ ↦ φ q.1 q.2) (univ ×ˢ Ioi 0))
    (hb : ∀ p₀ : X, ∀ r : ℝ, ∃ U ∈ 𝓝 p₀, ∃ M : ℝ, ∀ p ∈ U, ∀ x : ℝ, 1 ≤ x →
      ‖φ p x‖ ≤ M * x ^ (-r)) :
    Continuous fun q : ℂ × X ↦ ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (q.1 - 1) * φ q.2 x := by
  refine GlobalTheory.CompanionTheory.EisRk1Cont.continuous_setIntegral_Ioi_one
    (fun (q : ℂ × X) (x : ℝ) => (x : ℂ) ^ (q.1 - 1) * φ q.2 x) ?_ ?_
  · intro q y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
    have h1 : ContinuousAt (fun w : (ℂ × X) × ℝ => ((w.2 : ℝ) : ℂ) ^ (w.1.1 - 1)) (q, y) :=
      ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_snd).continuousAt
        ((continuous_fst.comp continuous_fst).sub continuous_const).continuousAt
        (Complex.ofReal_mem_slitPlane.mpr hy0)
    have h2 : ContinuousAt (fun w : (ℂ × X) × ℝ => φ w.1.2 w.2) (q, y) :=
      ContinuousAt.comp_of_eq
        (hφ.continuousAt (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds hy0)))
        (by fun_prop : Continuous fun w : (ℂ × X) × ℝ => (w.1.2, w.2)).continuousAt rfl
    exact h1.mul h2
  · rintro ⟨s₀, p₀⟩
    obtain ⟨U, hU, M, hM⟩ := hb p₀ (s₀.re + 3)
    refine ⟨{s : ℂ | s.re < s₀.re + 1} ×ˢ U,
      prod_mem_nhds ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds
        (show s₀.re < s₀.re + 1 by linarith)) hU, max M 0, le_max_right _ _, ?_⟩
    rintro ⟨s, p⟩ ⟨hs, hp⟩ x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hs1 : s.re < s₀.re + 1 := hs
    have hs' : (s - 1).re ≤ s₀.re := by
      rw [Complex.sub_re, Complex.one_re]; linarith
    calc ‖(x : ℂ) ^ (s - 1) * φ p x‖ = x ^ (s - 1).re * ‖φ p x‖ := by
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      _ ≤ x ^ s₀.re * (max M 0 * x ^ (-(s₀.re + 3))) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx hs')
            ((hM p hp x hx).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)))
            (norm_nonneg _) (Real.rpow_nonneg hx0.le _)
      _ = max M 0 * x ^ (-3 : ℝ) := by
          rw [mul_left_comm, ← Real.rpow_add hx0]; congr 2; ring
end GlobalTheory.CompanionTheory.EisRk1Cont
