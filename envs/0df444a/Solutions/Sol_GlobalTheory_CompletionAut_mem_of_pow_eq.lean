-- Prove2me | solution 1 for GlobalTheory.CompletionAut.mem_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:36.512693+00:00
-- url     : https://prove2.me/submissions/f5d48c1e-54f9-4c2a-a4d3-65bbc56c3b0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RingEquivAdicCompletionMemIntegersIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial
open GlobalTheory GlobalTheory.CompletionAut
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.CompletionAut
theorem _root_.solution {p e : ℕ} (he : 0 < e)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-(e : ℤ))) (hp0 : p ≠ 0)
    {x y : v.adicCompletion F} (h : y ^ (p * e + 1) = 1 + p * x ^ (p * e + 1)) :
    x ∈ v.adicCompletionIntegers F := by
  rw [mem_adicCompletionIntegers]
  by_contra hx
  push Not at hx
  have hx0 : Valued.v x ≠ 0 := (zero_lt_one.trans hx).ne'
  set l := p * e + 1 with hl
  have hle : e < l := by
    have : e ≤ p * e := Nat.le_mul_of_pos_left e (Nat.pos_of_ne_zero hp0)
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hx0).symm⟩
  have hm0 : 0 < m := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx; exact hx
  have h1 : Valued.v ((p : v.adicCompletion F) * x ^ l) = WithZero.exp (-(e : ℤ) + l * m) := by
    rw [map_mul, map_pow, hp, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul]
  have hpos : 0 < -(e : ℤ) + l * m := by
    have : (e : ℤ) < l := by exact_mod_cast hle
    nlinarith
  have h2 : Valued.v (1 + (p : v.adicCompletion F) * x ^ l) = WithZero.exp (-(e : ℤ) + l * m) := by
    rw [← h1]
    apply Valuation.map_add_eq_of_lt_right
    rw [h1, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact hpos
  rw [← h, map_pow] at h2
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h2
    exact WithZero.exp_ne_zero h2.symm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v y = WithZero.exp k := ⟨_, (WithZero.exp_log hy0).symm⟩
  rw [hk, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  have hd : (l : ℤ) ∣ (e : ℤ) := ⟨m - k, by linear_combination h2⟩
  have := Nat.le_of_dvd he (Int.natCast_dvd_natCast.1 hd)
  omega
end GlobalTheory.CompletionAut
