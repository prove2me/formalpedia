-- Prove2me | solution 1 for MvPowerSeries.mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3ca6426a-0fec-5699-8921-996a3c2d2869

import Mathlib
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow

set_option autoImplicit false

namespace MvPowerSeries
p2m_export "MvPowerSeries" "coeff coeff_monomial X_dvd_iff subst C subst_mul X constantCoeff monomial_zero_eq_C_apply subst_pow hasSubst_of_constantCoeff_zero X_pow_dvd_iff monomial_mul_monomial coeff_zero_eq_constantCoeff_apply coe_substAlgHom monomial coeff_subst X_pow_eq ext HasSubst subst_C mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt"
namespace PowPureAux
p2m_open "MvPowerSeries"

section Graded

variable (W : Type) [CommRing W]

noncomputable abbrev nd (e i : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e - i)

omit W in
@[scoped simp] theorem nd_zero (e i : ℕ) : nd e i 0 = i := by simp [nd]

omit W in
@[scoped simp] theorem nd_one (e i : ℕ) : nd e i 1 = e - i := by simp [nd]

omit W in
theorem eq_nd (n : Fin 2 →₀ ℕ) : n = nd (n 0 + n 1) (n 0) := by
  ext j
  fin_cases j <;> simp [nd]

omit W in
theorem nd_injOn (e : ℕ) : Set.InjOn (nd e) ↑(Finset.range (e + 1)) := by
  intro i _ j _ h
  have := congrArg (fun n : Fin 2 →₀ ℕ => n 0) h
  simpa using this

theorem coeff_eq_zero_of_mem_pow (e : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e)
    (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 < e) : MvPowerSeries.coeff n g = 0 :=
  (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W e g).mp hg n hn

theorem mem_pow_of_coeff_eq_zero (e : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0) :
    g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e :=
  (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W e g).mpr hg

theorem mem_span_X_of_coeff_zero (g : MvPowerSeries (Fin 2) W)
    (hg : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) g = 0) :
    g ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
  rw [← pow_one (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1})]
  refine mem_pow_of_coeff_eq_zero W 1 g fun n hn => ?_
  have : n = 0 := by
    ext j; fin_cases j <;> simp <;> omega
  rw [this]; exact hg

theorem pow_mul_pow_mem_pow (x y : MvPowerSeries (Fin 2) W)
    (hx : x ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1})
    (hy : y ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1})
    (i j e : ℕ) (he : i + j = e) :
    x ^ i * y ^ j ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e := by
  have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hx i) (Ideal.pow_mem_pow hy j)
  rwa [← pow_add, he] at this

noncomputable def low (e : ℕ) (g : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  ∑ i ∈ Finset.range (e + 1), MvPowerSeries.monomial (nd e i) (MvPowerSeries.coeff (nd e i) g)

theorem coeff_low (e : ℕ) (g : MvPowerSeries (Fin 2) W) (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n (low W e g) = if n 0 + n 1 = e then MvPowerSeries.coeff n g else 0 := by
  classical
  rw [low, map_sum]
  simp only [MvPowerSeries.coeff_monomial]
  by_cases h : n 0 + n 1 = e
  · rw [if_pos h, Finset.sum_eq_single (n 0)]
    · have hn : n = nd e (n 0) := by
        have := eq_nd n; rwa [h] at this
      rw [if_pos hn, ← hn]
    · intro i _ hne
      rw [if_neg]
      intro hni
      apply hne
      have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) hni
      simp at this
      exact this.symm
    · intro hn0
      exfalso; apply hn0
      simp only [Finset.mem_range]; omega
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg]
    intro hni
    apply h
    simp only [Finset.mem_range] at hi
    rw [hni, nd_zero, nd_one]; omega

theorem sub_low_mem_pow (e : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0) :
    g - low W e g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (e + 1) := by
  refine mem_pow_of_coeff_eq_zero W (e + 1) _ fun n hn => ?_
  rw [map_sub, coeff_low]
  split_ifs with h
  · exact sub_self _
  · rw [hg n (by omega), sub_zero]

theorem low_mem_pow (e : ℕ) (g : MvPowerSeries (Fin 2) W) :
    low W e g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e := by
  refine mem_pow_of_coeff_eq_zero W e _ fun n hn => ?_
  rw [coeff_low, if_neg (by omega)]

theorem monomial_nd_eq (e i : ℕ) (c : W) :
    MvPowerSeries.monomial (nd e i) c =
      MvPowerSeries.C c * MvPowerSeries.X 0 ^ i * MvPowerSeries.X 1 ^ (e - i) := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]
  simp [nd]

theorem low_eq_sum_C_mul (e : ℕ) (g : MvPowerSeries (Fin 2) W) :
    low W e g = ∑ i ∈ Finset.range (e + 1),
      MvPowerSeries.C (MvPowerSeries.coeff (nd e i) g) * MvPowerSeries.X 0 ^ i * MvPowerSeries.X 1 ^ (e - i) := by
  unfold low
  exact Finset.sum_congr rfl fun i _ => monomial_nd_eq W e i _

end Graded

section Line

variable (W : Type) [CommRing W]

noncomputable def lineSubst (a b : W) : Fin 2 → PowerSeries W :=
  fun s => PowerSeries.C (if s = 0 then a else b) * PowerSeries.X

theorem hasSubst_lineSubst (a b : W) : MvPowerSeries.HasSubst (lineSubst W a b) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  show PowerSeries.constantCoeff (PowerSeries.C (if s = 0 then a else b) * PowerSeries.X) = 0
  simp

noncomputable def lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) : PowerSeries W :=
  MvPowerSeries.subst (lineSubst W a b) G

theorem lineEval_mul (a b : W) (G H : MvPowerSeries (Fin 2) W) :
    lineEval W a b (G * H) = lineEval W a b G * lineEval W a b H :=
  MvPowerSeries.subst_mul (hasSubst_lineSubst W a b) G H

theorem lineEval_pow (a b : W) (G : MvPowerSeries (Fin 2) W) (n : ℕ) :
    lineEval W a b (G ^ n) = lineEval W a b G ^ n :=
  MvPowerSeries.subst_pow (hasSubst_lineSubst W a b) G n

theorem lineEval_sum (a b : W) (s : Finset ℕ) (G : ℕ → MvPowerSeries (Fin 2) W) :
    lineEval W a b (∑ i ∈ s, G i) = ∑ i ∈ s, lineEval W a b (G i) := by
  unfold lineEval
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_lineSubst W a b), map_sum]

theorem lineEval_C (a b w : W) :
    lineEval W a b (MvPowerSeries.C w) = PowerSeries.C w := by
  unfold lineEval
  rw [MvPowerSeries.subst_C]
  rfl

theorem mvcoeff_C_mul_X_pow (c : W) (e m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single () e) (PowerSeries.C c * PowerSeries.X ^ m) = if e = m then c else 0 :=
  PowerSeries.coeff_C_mul_X_pow c m e

theorem coeff_lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) (e : ℕ) :
    PowerSeries.coeff e (lineEval W a b G) =
      ∑ i ∈ Finset.range (e + 1), MvPowerSeries.coeff (nd e i) G * a ^ i * b ^ (e - i) := by
  classical
  show MvPowerSeries.coeff (Finsupp.single () e) (MvPowerSeries.subst (lineSubst W a b) G) = _
  rw [MvPowerSeries.coeff_subst (hasSubst_lineSubst W a b)]
  have hterm : ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d G • MvPowerSeries.coeff (Finsupp.single () e)
          (d.prod fun s n => lineSubst W a b s ^ n) =
        if d 0 + d 1 = e then MvPowerSeries.coeff d G * a ^ d 0 * b ^ d 1 else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    have : lineSubst W a b 0 ^ d 0 * lineSubst W a b 1 ^ d 1 =
        PowerSeries.C (a ^ d 0 * b ^ d 1) * PowerSeries.X ^ (d 0 + d 1) := by
      simp only [lineSubst, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0), map_mul, map_pow]
      ring
    rw [this, mvcoeff_C_mul_X_pow, smul_eq_mul]
    by_cases h : d 0 + d 1 = e
    · rw [if_pos h.symm, if_pos h, mul_assoc]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (e + 1)).image (nd e)) ?_]
  · rw [Finset.sum_image (nd_injOn e)]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [nd_zero, nd_one, if_pos (by omega)]
  · intro d hd
    rw [Function.mem_support] at hd
    have h : d 0 + d 1 = e := by
      by_contra h; exact hd (if_neg h)
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨d 0, by omega, by rw [(eq_nd d), h, nd_zero]⟩

theorem constantCoeff_lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) :
    PowerSeries.constantCoeff (lineEval W a b G) = MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) G := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lineEval]
  simp [nd]

theorem coeff_one_lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) :
    PowerSeries.coeff 1 (lineEval W a b G) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) G * a +
        MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) G * b := by
  rw [coeff_lineEval, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [nd, add_comm]

theorem coeff_pow_mul_pow (φ χ : PowerSeries W) (hφ : PowerSeries.constantCoeff φ = 0)
    (hχ : PowerSeries.constantCoeff χ = 0) (j k : ℕ) :
    PowerSeries.coeff (j + k) (φ ^ j * χ ^ k) = PowerSeries.coeff 1 φ ^ j * PowerSeries.coeff 1 χ ^ k := by
  obtain ⟨φ', rfl⟩ := PowerSeries.X_dvd_iff.mpr hφ
  obtain ⟨χ', rfl⟩ := PowerSeries.X_dvd_iff.mpr hχ
  have h1 : (PowerSeries.X * φ') ^ j * (PowerSeries.X * χ') ^ k =
      PowerSeries.X ^ (j + k) * (φ' ^ j * χ' ^ k) := by ring
  have h2 := PowerSeries.coeff_X_pow_mul (φ' ^ j * χ' ^ k) (j + k) 0
  rw [zero_add] at h2
  rw [h1, h2]
  have h3 : ∀ ψ : PowerSeries W, PowerSeries.coeff 1 (PowerSeries.X * ψ) = PowerSeries.coeff 0 ψ :=
    fun ψ => PowerSeries.coeff_succ_X_mul 0 ψ
  rw [h3, h3]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow]

end Line

end MvPowerSeries.PowPureAux
p2m_reactivate "P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.MvPowerSeries P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.MvPowerSeries.PowPureAux"
p2m_reactivate "P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.MvPowerSeries"

open MvPowerSeries.PowPureAux in
theorem solution
    (W : Type) [CommRing W] (G h : MvPowerSeries (Fin 2) W) (d k : ℕ)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d) (a b : W) :
    G * h ^ k ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (d * k) ∧
      (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) (G * h ^ k)
              * a ^ i * b ^ (d * k - i)) =
        MvPowerSeries.constantCoeff G *
          (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i)) ^ k := by
  classical
  refine ⟨?_, ?_⟩
  · have h1 := Ideal.pow_mem_pow hh k
    rw [← pow_mul] at h1
    exact Ideal.mul_mem_left _ _ h1
  ·
    have eL : (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) (G * h ^ k)
              * a ^ i * b ^ (d * k - i)) = PowerSeries.coeff (d * k) (lineEval W a b (G * h ^ k)) := by
      rw [coeff_lineEval]
    have eR : (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i)) = PowerSeries.coeff d (lineEval W a b h) := by
      rw [coeff_lineEval]
    rw [eL, eR, lineEval_mul, lineEval_pow]

    have hdiv : (PowerSeries.X : PowerSeries W) ^ d ∣ lineEval W a b h := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [coeff_lineEval]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [coeff_eq_zero_of_mem_pow W d h hh (nd m i) (by
        simp only [Finset.mem_range] at hi; rw [nd_zero, nd_one]; omega), zero_mul, zero_mul]
    obtain ⟨ψ, hψ⟩ := hdiv
    have hψ0 : PowerSeries.coeff d (lineEval W a b h) = PowerSeries.constantCoeff ψ := by
      rw [hψ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have := PowerSeries.coeff_X_pow_mul ψ d 0
      rwa [zero_add] at this
    rw [hψ0, hψ]
    have e1 : lineEval W a b G * (PowerSeries.X ^ d * ψ) ^ k = PowerSeries.X ^ (d * k) * (lineEval W a b G * ψ ^ k) := by
      rw [mul_pow, ← pow_mul]; ring
    rw [e1]
    have h2 := PowerSeries.coeff_X_pow_mul (lineEval W a b G * ψ ^ k) (d * k) 0
    rw [zero_add] at h2
    rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, constantCoeff_lineEval,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

end S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow
end P2MW
export P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow (solution)
