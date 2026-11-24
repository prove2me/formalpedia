-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLeft.digamma_sub_digamma_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:17.874431+00:00
-- url     : https://prove2.me/submissions/7dc8217c-aea2-4cef-9046-5f8c3d6c7c3f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLeft
namespace GlobalTheory.CompanionTheory.DigammaLeft
theorem _root_.solution (w : ℂ) (hw : ∀ n : ℤ, w ≠ n) :
    Complex.digamma w - Complex.digamma (1 - w) =
      -((Real.pi : ℂ) * Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) := by
  have hw1 : ∀ m : ℕ, w ≠ -(m : ℂ) := fun m h => hw (-(m : ℤ)) (by rw [h]; push_cast; rfl)
  have hw2 : ∀ m : ℕ, 1 - w ≠ -(m : ℂ) := fun m h => hw ((m : ℤ) + 1) (by
    push_cast
    linear_combination -h)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : Complex.sin (Real.pi * w) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    apply hw k
    apply mul_left_cancel₀ hpi
    rw [hk]; ring
  have ha : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw1
  have hb : Complex.Gamma (1 - w) ≠ 0 := Complex.Gamma_ne_zero hw2
  have hG1 : HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w hw1).hasDerivAt
  have hG2' : HasDerivAt Complex.Gamma (deriv Complex.Gamma (1 - w)) (1 - w) :=
    (Complex.differentiableAt_Gamma (1 - w) hw2).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have hG2 : HasDerivAt (fun z : ℂ => Complex.Gamma (1 - z))
      (deriv Complex.Gamma (1 - w) * (-1)) w :=
    HasDerivAt.comp w hG2' hlin
  have hprod := hG1.mul hG2
  have hsin : HasDerivAt (fun z : ℂ => Complex.sin (Real.pi * z))
      (Complex.cos (Real.pi * w) * Real.pi) w := by
    have h1 : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z) Real.pi w := by
      simpa using (hasDerivAt_id w).const_mul (Real.pi : ℂ)
    exact (Complex.hasDerivAt_sin _).comp w h1
  have hquot := (hasDerivAt_const w (Real.pi : ℂ)).div hsin hs
  have hfun : ((fun _ : ℂ => (Real.pi : ℂ)) / fun z : ℂ => Complex.sin (Real.pi * z)) =
      (Complex.Gamma * fun z : ℂ => Complex.Gamma (1 - z)) := by
    funext z
    simp only [Pi.mul_apply, Pi.div_apply]
    exact (Complex.Gamma_mul_Gamma_one_sub z).symm
  rw [hfun] at hquot
  have huniq := hprod.unique hquot
  have hab : Complex.Gamma w * Complex.Gamma (1 - w) = Real.pi / Complex.sin (Real.pi * w) :=
    Complex.Gamma_mul_Gamma_one_sub w
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply]
  have e1 : deriv Complex.Gamma w / Complex.Gamma w -
      deriv Complex.Gamma (1 - w) / Complex.Gamma (1 - w) =
      (deriv Complex.Gamma w * Complex.Gamma (1 - w) +
        Complex.Gamma w * (deriv Complex.Gamma (1 - w) * -1)) /
      (Complex.Gamma w * Complex.Gamma (1 - w)) := by
    field_simp
    ring
  rw [e1, huniq, hab]
  field_simp
  ring
end GlobalTheory.CompanionTheory.DigammaLeft
