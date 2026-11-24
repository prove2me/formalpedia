-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:37:19.744352+00:00
-- url     : https://prove2.me/submissions/bc56eedb-43a4-4827-88f5-820657f83479

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimePowerNotDvdDifferent
import Theorems.Thm_GlobalTheory_T_trace_idempotent_not_divisible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob
namespace GlobalTheory.CompanionTheory.Glob
theorem _root_.solution (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime]
    (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 E) ∈ P) (hPJ : ¬ P ∣ J)
    (hspan : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J) :
    ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  intro hdiv
  set d := Module.finrank ℚ E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact hp0 hpP
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPbot
  have hpd : ((p : 𝓞 E)) ^ d ∈ P := Ideal.pow_mem_of_mem P hpP d hdpos
  have hspanP : Ideal.span {((p : 𝓞 E)) ^ d} ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hpd
  have hJP : ¬ J ≤ P := fun h => hPJ (Ideal.dvd_iff_le.2 h)
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.one_eq_top, Ideal.top_mul] at hspan
    exact hJP (hspan ▸ hspanP)
  have hcop : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact hPmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hJP (h ▸ le_sup_right))
  obtain ⟨y, hy, x, hx, hyx⟩ := Ideal.isCoprime_iff_exists.1 (hcop.pow_left (m := k))
  have hxy : x * y ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
    rw [hspan, mul_comm x y]
    exact Ideal.mul_mem_mul hy hx
  have hidem : x * x - x ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
    have : x * x - x = -(x * y) := by
      have : x = 1 - y := by rw [← hyx]; ring
      rw [this]; ring
    rw [this]
    exact neg_mem hxy
  have hnot : x ∉ Ideal.span {((p : 𝓞 E)) ^ d} := by
    intro h
    have h1 : x ∈ P := hspanP h
    have h2 : y ∈ P := Ideal.pow_le_self hk hy
    exact hPmax.ne_top ((Ideal.eq_top_iff_one _).2 (hyx ▸ add_mem h2 h1))
  have hlt : Module.finrank ℤ (𝓞 E) < p ^ d := by
    rw [RingOfIntegers.rank]
    exact Nat.lt_pow_self hp.one_lt
  refine GlobalTheory.T.trace_idempotent_not_divisible (𝓞 E) x p d hp hlt hidem hnot ?_

  have hpdE : ((p : E)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  have hD0 : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hz : (x : E) / ((p : E)) ^ d ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
        ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
    rw [hdual, FractionalIdeal.mem_inv_iff hD0]
    intro w hw
    obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hw
    have hδP : δ ∈ P ^ k := Ideal.dvd_iff_le.1 hdiv hδ
    have hmem : δ * x ∈ Ideal.span {((p : 𝓞 E)) ^ d} := by
      rw [hspan]
      exact Ideal.mul_mem_mul hδP hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨a, ?_⟩
    have h2 : algebraMap (𝓞 E) E a * ((p : E)) ^ d = algebraMap (𝓞 E) E δ * (x : E) := by
      have := congrArg (algebraMap (𝓞 E) E) ha
      simpa using this
    field_simp
    rw [h2]
    ring
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have htr := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h10).1 hz 1 (FractionalIdeal.one_mem_one _)
  obtain ⟨n, hn⟩ := htr
  rw [Algebra.traceForm_apply, mul_one] at hn
  have hzs : (x : E) / ((p : E)) ^ d = (((p : ℚ) ^ d)⁻¹) • (x : E) := by
    rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]
  rw [hzs, map_smul, smul_eq_mul, ← Algebra.coe_trace_int] at hn
  have hpq : ((p : ℚ)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨n, ?_⟩
  have : ((Algebra.trace ℤ (𝓞 E) x : ℤ) : ℚ) = ((p : ℚ)) ^ d * (n : ℚ) := by
    have h3 : (algebraMap ℤ ℚ n) = (n : ℚ) := rfl
    rw [h3] at hn
    rw [hn]
    field_simp
  exact_mod_cast this
end GlobalTheory.CompanionTheory.Glob
