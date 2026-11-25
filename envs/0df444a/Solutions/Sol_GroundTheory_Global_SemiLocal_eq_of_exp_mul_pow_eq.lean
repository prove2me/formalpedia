-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.eq_of_exp_mul_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:57.89605+00:00
-- url     : https://prove2.me/submissions/d787bc09-2085-42fe-a52b-3b73dc7be184

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution {e i i' : ℕ} (hi : i < e) (hi' : i' < e) {a b : ℤᵐ⁰} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : exp (-(i : ℤ)) * a ^ e = exp (-(i' : ℤ)) * b ^ e) : i = i' := by
  rw [← exp_log ha, ← exp_log hb, ← exp_nsmul, ← exp_nsmul, ← exp_add, ← exp_add, exp_inj] at h
  simp only [nsmul_eq_mul] at h
  have hdvd : (e : ℤ) ∣ (i : ℤ) - i' := ⟨log a - log b, by rw [mul_sub]; linarith⟩
  have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
  omega
end GroundTheory.Global.SemiLocal
