-- Prove2me | solution 1 for GlobalTheory.map_I_smul_of_cauchyRiemann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:51.443881+00:00
-- url     : https://prove2.me/submissions/a7a7dbb4-314e-4432-b0f0-af7e871f9437

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix
open scoped ContDiff BigOperators Real
namespace GlobalTheory
private lemma pi_single_eq_re_smul_add_im_smul {g : ℕ} (a : Fin g) (w : ℂ) :
    (Pi.single a w : Fin g → ℂ) =
      (w.re : ℝ) • (Pi.single a 1 : Fin g → ℂ) + (w.im : ℝ) • (I • (Pi.single a 1 : Fin g → ℂ)) := by
  ext j
  by_cases hj : j = a
  · subst hj
    apply Complex.ext <;> simp
  · simp [hj]
end GlobalTheory
end

set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} (L : (Fin g → ℂ) →L[ℝ] ℂ)
    (h : ∀ a, L (Pi.single a 1 : Fin g → ℂ) + I * L (I • (Pi.single a 1 : Fin g → ℂ)) = 0)
    (c : ℂ) (v : Fin g → ℂ) : L (c • v) = c • L v := by

  have hI : ∀ a, L (I • (Pi.single a 1 : Fin g → ℂ)) = I * L (Pi.single a 1) := by
    intro a
    linear_combination (-I) * h a + L (I • (Pi.single a 1 : Fin g → ℂ)) * I_sq
  have hline : ∀ a (w : ℂ), L (Pi.single a w : Fin g → ℂ) = w * L (Pi.single a 1) := by
    intro a w
    rw [pi_single_eq_re_smul_add_im_smul a w, map_add, map_smul, map_smul, hI a]
    conv_rhs => rw [← Complex.re_add_im w]
    simp only [Complex.real_smul]
    ring
  have hsum : ∀ u : Fin g → ℂ, L u = ∑ a, u a * L (Pi.single a 1) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => hline a (u a))
  rw [hsum, hsum v, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end GlobalTheory
