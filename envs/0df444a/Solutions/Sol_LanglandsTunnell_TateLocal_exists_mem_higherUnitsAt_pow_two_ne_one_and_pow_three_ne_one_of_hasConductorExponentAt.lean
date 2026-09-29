-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/df6d1435-72a4-5f38-af55-0e7ab3f41bc8

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_RatIdele_Normalizer
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.higherUnitsAt TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "higherUnitsAt mem_higherUnitsAt_iff higherUnitsAt_antitone HasConductorExponentAt"
namespace PowerLev
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

open Polynomial Rat.HeightOneSpectrum

theorem exists_pow_eq_of_norm_sub_one_le (q : ℕ) [hq : Fact q.Prime] (k : ℕ) (y : ℤ_[q]) (r : ℕ) (hr : 3 ≤ r)
    (hy : ‖y - 1‖ ≤ ((q : ℝ)⁻¹) ^ r) (hk : (q : ℝ)⁻¹ ≤ ‖(k : ℤ_[q])‖)
    (hΦ : ∀ z : ℤ_[q], ‖z - 1‖ < ‖(k : ℤ_[q])‖ → ‖(Finset.range k).sum (fun i => z ^ i)‖ = ‖(k : ℤ_[q])‖) :
    ∃ z : ℤ_[q], z ^ k = y ∧ ‖z - 1‖ ≤ ((q : ℝ)⁻¹) ^ (r - 1) := by
  have hqpos : (0 : ℝ) < ((q : ℕ) : ℝ)⁻¹ := by
    have : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast hq.out.pos
    positivity
  have hqlt1 : ((q : ℕ) : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.out.one_lt)
  have hkpos : 0 < ‖(k : ℤ_[q])‖ := lt_of_lt_of_le hqpos hk
  set F : Polynomial ℤ_[q] := X ^ k - C y with hF
  have hF1 : F.aeval (1 : ℤ_[q]) = 1 - y := by
    simp [hF, Polynomial.coe_aeval_eq_eval]
  have hF'1 : F.derivative.aeval (1 : ℤ_[q]) = (k : ℤ_[q]) := by
    simp [hF, Polynomial.coe_aeval_eq_eval, Polynomial.derivative_X_pow]
  have hn : ‖F.aeval (1 : ℤ_[q])‖ < ‖F.derivative.aeval (1 : ℤ_[q])‖ ^ 2 := by
    rw [hF1, hF'1, ← norm_neg, neg_sub]
    calc ‖y - 1‖ ≤ ((q : ℝ)⁻¹) ^ r := hy
      _ ≤ ((q : ℝ)⁻¹) ^ 3 := pow_le_pow_of_le_one hqpos.le hqlt1.le hr
      _ < ((q : ℝ)⁻¹) ^ 2 := pow_lt_pow_right_of_lt_one₀ hqpos hqlt1 (by norm_num)
      _ ≤ ‖(k : ℤ_[q])‖ ^ 2 := pow_le_pow_left₀ hqpos.le hk 2
  obtain ⟨z, hz, hdist, -⟩ := hensels_lemma hn
  rw [hF'1] at hdist
  have hzk : z ^ k = y := by
    have := hz
    simp only [hF, Polynomial.coe_aeval_eq_eval, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at this
    exact this
  refine ⟨z, hzk, ?_⟩

  have hgeom : (Finset.range k).sum (fun i => z ^ i) * (z - 1) = y - 1 := by
    rw [geom_sum_mul, hzk]
  have hnorm : ‖(Finset.range k).sum (fun i => z ^ i)‖ * ‖z - 1‖ = ‖y - 1‖ := by
    rw [← norm_mul, hgeom]
  rw [hΦ z hdist] at hnorm
  have h1 : ‖z - 1‖ = ‖y - 1‖ / ‖(k : ℤ_[q])‖ := by
    field_simp
    linarith [hnorm]
  rw [h1, div_le_iff₀ hkpos]
  calc ‖y - 1‖ ≤ ((q : ℝ)⁻¹) ^ r := hy
    _ = ((q : ℝ)⁻¹) ^ (r - 1) * (q : ℝ)⁻¹ := by
        rw [← pow_succ]
        congr 1
        omega
    _ ≤ ((q : ℝ)⁻¹) ^ (r - 1) * ‖(k : ℤ_[q])‖ := by gcongr

theorem norm_geom_two (q : ℕ) [Fact q.Prime] (z : ℤ_[q]) (hz : ‖z - 1‖ < ‖(2 : ℤ_[q])‖) :
    ‖(Finset.range 2).sum (fun i => z ^ i)‖ = ‖((2 : ℕ) : ℤ_[q])‖ := by
  have hsum : (Finset.range 2).sum (fun i => z ^ i) = 2 + (z - 1) := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum, Nat.cast_ofNat]
  have hne : ‖(2 : ℤ_[q])‖ ≠ ‖z - 1‖ := (ne_of_lt hz).symm
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left hz.le]

theorem norm_geom_three (q : ℕ) [Fact q.Prime] (z : ℤ_[q]) (hz : ‖z - 1‖ < ‖(3 : ℤ_[q])‖) :
    ‖(Finset.range 3).sum (fun i => z ^ i)‖ = ‖((3 : ℕ) : ℤ_[q])‖ := by
  have hsum : (Finset.range 3).sum (fun i => z ^ i) = 3 + (z - 1) * ((z - 1) + 3) := by
    simp [Finset.sum_range_succ]
    ring
  rw [hsum, Nat.cast_ofNat]
  have hsmall : ‖(z - 1) * ((z - 1) + 3)‖ < ‖(3 : ℤ_[q])‖ := by
    rw [norm_mul]
    calc ‖z - 1‖ * ‖(z - 1) + 3‖ ≤ ‖z - 1‖ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖z - 1‖ := mul_one _
      _ < ‖(3 : ℤ_[q])‖ := hz
  have hne : ‖(3 : ℤ_[q])‖ ≠ ‖(z - 1) * ((z - 1) + 3)‖ := (ne_of_lt hsmall).symm
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left hsmall.le]

theorem inv_le_norm_natCast_of_prime (q : ℕ) [hq : Fact q.Prime] (k : ℕ) (hk : k.Prime) :
    (q : ℝ)⁻¹ ≤ ‖(k : ℤ_[q])‖ := by
  by_cases hqk : q = k
  · subst hqk
    rw [PadicInt.norm_p]
  · have hcop : q.Coprime k := (Nat.coprime_primes hq.out hk).mpr hqk
    rw [PadicInt.norm_natCast_eq_one_iff.mpr hcop]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hq.out.one_lt.le)

theorem exists_pow_eq_and_mem_higherUnitsAt (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) (hk23 : k = 2 ∨ k = 3)
    (r : ℕ) (hr : 3 ≤ r) (t : (v.adicCompletion ℚ)ˣ) (ht : t ∈ higherUnitsAt ℚ v r) :
    ∃ z : (v.adicCompletion ℚ)ˣ, z ^ k = t ∧ z ∈ higherUnitsAt ℚ v (r - 1) := by
  classical
  obtain ⟨ht1, htr⟩ := (mem_higherUnitsAt_iff ℚ v).mp ht
  have hle : Valued.v ((t : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(r : ℤ)) := htr.resolve_left (by omega)
  set q : Nat.Primes := primesEquiv (R := 𝓞 ℚ) v with hq
  haveI hqF : Fact (q : ℕ).Prime := ⟨q.2⟩
  set E := adicCompletion.padicEquiv (R := 𝓞 ℚ) v with hE
  set π : v.adicCompletion ℚ := algebraMap ℚ (v.adicCompletion ℚ) ((q : ℕ) : ℚ) with hπ
  have hvq : Valued.v π = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((q : ℕ) : ℚ)).trans (RatIdele.valuation_natGenerator v)
  have hq0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hvq
    exact WithZero.exp_ne_zero hvq.symm
  have hEq : E π = ((q : ℕ) : ℚ_[q]) := by
    rw [hπ, AlgHomClass.commutes E, map_natCast]

  set w : v.adicCompletion ℚ := ((t : v.adicCompletion ℚ) - 1) / π ^ r with hw
  have hpowr : Valued.v (π ^ r) = WithZero.exp (-(r : ℤ)) := by
    rw [map_pow, hvq, ← WithZero.exp_nsmul]
    simp
  have hwint : w ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hw, map_div₀, hpowr]
    exact div_le_one_of_le₀ hle zero_le'
  have htint : (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ht1]
  have hdecomp : (t : v.adicCompletion ℚ) - 1 = π ^ r * w := by
    rw [hw, mul_div_cancel₀ _ (pow_ne_zero r hq0)]
  have hEt : ‖E t‖ ≤ 1 := (adicCompletion.padicEquiv_bijOn (R := 𝓞 ℚ) v).mapsTo htint
  have hEw : ‖E w‖ ≤ 1 := (adicCompletion.padicEquiv_bijOn (R := 𝓞 ℚ) v).mapsTo hwint
  set y : ℤ_[q] := ⟨E t, hEt⟩ with hy
  have hy1 : ‖y - 1‖ ≤ ((q : ℝ)⁻¹) ^ r := by
    have h : E t - 1 = ((q : ℕ) : ℚ_[q]) ^ r * E w := by
      have h := congrArg E hdecomp
      rw [map_sub, map_one, map_mul, map_pow, hEq] at h
      exact h
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
    show ‖E t - 1‖ ≤ _
    rw [h, norm_mul, norm_pow, Padic.norm_p]
    exact mul_le_of_le_one_right (by positivity) hEw

  obtain ⟨z₀, hz₀k, hz₀d⟩ : ∃ z₀ : ℤ_[q], z₀ ^ k = y ∧ ‖z₀ - 1‖ ≤ ((q : ℝ)⁻¹) ^ (r - 1) := by
    rcases hk23 with rfl | rfl
    · exact exists_pow_eq_of_norm_sub_one_le q 2 y r hr hy1 (inv_le_norm_natCast_of_prime q 2 Nat.prime_two)
        (fun z hz => by
          have h := norm_geom_two q z (by rw [← Nat.cast_ofNat]; exact hz)
          exact h)
    · exact exists_pow_eq_of_norm_sub_one_le q 3 y r hr hy1 (inv_le_norm_natCast_of_prime q 3 Nat.prime_three)
        (fun z hz => by
          have h := norm_geom_three q z (by rw [← Nat.cast_ofNat]; exact hz)
          exact h)

  set z : v.adicCompletion ℚ := E.symm (z₀ : ℚ_[q]) with hz
  have hzk : z ^ k = (t : v.adicCompletion ℚ) := by
    have h : ((z₀ : ℚ_[q])) ^ k = E t := by
      have h' := congrArg (fun w : ℤ_[q] => (w : ℚ_[q])) hz₀k
      simpa [hy] using h'
    rw [hz, ← map_pow, h, ContinuousAlgEquiv.symm_apply_apply]
  have hzne : z ≠ 0 := by
    intro h
    apply t.ne_zero
    rw [← hzk, h, zero_pow (by omega)]
  refine ⟨Units.mk0 z hzne, Units.ext (by simp [hzk]), ?_⟩

  rw [mem_higherUnitsAt_iff]
  have hzval : Valued.v z = 1 := by
    have h := congrArg Valued.v hzk
    rw [map_pow, ht1] at h
    rcases pow_eq_one_iff.mp h with h' | h'
    · exact h'
    · omega
  refine ⟨by simpa using hzval, Or.inr ?_⟩
  have hmem : z₀ - 1 ∈ Ideal.span {((q : ℕ) : ℤ_[q]) ^ (r - 1)} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    simpa [inv_pow, zpow_neg, zpow_natCast] using hz₀d
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem

  have hcint : ‖(c : ℚ_[q])‖ ≤ 1 := c.norm_le_one
  obtain ⟨x, hxint, hxc⟩ := (adicCompletion.padicEquiv_bijOn (R := 𝓞 ℚ) v).surjOn hcint
  have hz1 : z - 1 = π ^ (r - 1) * x := by
    have h := congrArg (fun w : ℤ_[q] => (w : ℚ_[q])) hc
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_sub, PadicInt.coe_one] at h
    have hx : x = E.symm (c : ℚ_[q]) := by rw [← hxc, ContinuousAlgEquiv.symm_apply_apply]
    have hπ' : π = E.symm ((q : ℕ) : ℚ_[q]) := by rw [← hEq, ContinuousAlgEquiv.symm_apply_apply]
    rw [hz, hx, hπ', ← map_pow, ← map_mul, ← map_one E.symm, ← map_sub, ← h, mul_comm]
  show Valued.v (z - 1) ≤ WithZero.exp (-((r - 1 : ℕ) : ℤ))
  rw [hz1, map_mul, map_pow, hvq, ← WithZero.exp_nsmul]
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hxint
  calc WithZero.exp ((r - 1 : ℕ) • (-1 : ℤ)) * Valued.v x ≤ WithZero.exp ((r - 1 : ℕ) • (-1 : ℤ)) * 1 :=
        mul_le_mul_right hx1 _
    _ = WithZero.exp (-((r - 1 : ℕ) : ℤ)) := by rw [mul_one]; simp

end LanglandsTunnell.TateLocal.PowerLev

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (kp : ℕ)
    (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (m : ℕ) (hm : m + 4 ≤ kp) :
    (∃ s ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ s ^ 2 ≠ 1) ∧
    (∃ s ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ s ^ 3 ≠ 1) := by
  classical
  have hr : 3 ≤ m + 3 := by omega
  have hlt : m + 3 < kp := by omega
  have hmin := hkp.2 (m + 3) hlt

  have key : ∀ k : ℕ, (k = 2 ∨ k = 3) → (∀ s ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m, χ s ^ k = 1) →
      ∀ t ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (m + 3), χ t = 1 := by
    intro k hk h t ht
    obtain ⟨z, hzk, hzm⟩ := LanglandsTunnell.TateLocal.PowerLev.exists_pow_eq_and_mem_higherUnitsAt p k hk (m + 3) hr t ht
    have hzm' : z ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p m :=
      LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ p (by omega) hzm
    rw [← hzk, map_pow]
    exact h z hzm'
  obtain ⟨u, hu, hune⟩ := hmin
  constructor
  · by_contra h
    push Not at h
    exact hune (key 2 (Or.inl rfl) (fun s hs => by simpa using h s hs) u hu)
  · by_contra h
    push Not at h
    exact hune (key 3 (Or.inr rfl) (fun s hs => by simpa using h s hs) u hu)

end S_LanglandsTunnell_TateLocal_exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt (solution)
