-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:10.263111+00:00
-- url     : https://prove2.me/submissions/f5783232-1796-4914-b20e-e290454499fb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SesquilinearEqZeroOfDiagZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Sesquilinear
namespace GlobalTheory.CompanionTheory.Sesquilinear
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (h : ∀ v, B v v = 0) : B = 0 := by
  ext v w
  have h1 := h (v + w)
  have h2 := h (v + Complex.I • w)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    h v, h w, smul_eq_mul, zero_add, add_zero, Complex.conj_I, RingHom.id_apply,
    mul_zero] at h1 h2
  have h3 : B v w = B w v := by
    have : Complex.I * (B w v - B v w) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h4 | h4
    · exact absurd h4 Complex.I_ne_zero
    · exact (sub_eq_zero.mp h4).symm
  have h5 : (2 : ℂ) * B v w = 0 := by linear_combination h1 + h3
  simpa using h5
end GlobalTheory.CompanionTheory.Sesquilinear
