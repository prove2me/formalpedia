-- Prove2me | solution 1 for NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f25b5f50-85cf-5ed3-8c17-6f823eb95a7b

import Mathlib
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul

set_option autoImplicit false

noncomputable section

open NumberField Filter Complex IsDedekindDomain
open scoped Topology Classical

namespace Ws41
namespace EulerZeta

universe u

variable (K : Type u) [Field K] [NumberField K]

def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

theorem dedekindZeta_eq_LSeries (z : ℂ) :
    dedekindZeta K z = LSeries (fun n => (idealCount K n : ℂ)) z := rfl

scoped instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOf_absNorm_eq n).to_subtype

theorem idealCount_zero : idealCount K 0 = 1 := by
  rw [idealCount]
  have : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} :=
    { default := ⟨⊥, Ideal.absNorm_eq_zero_iff.mpr rfl⟩
      uniq := fun I => Subtype.ext (Ideal.absNorm_eq_zero_iff.mp I.2) }
  exact Nat.card_unique

theorem tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  rw [dedekindZeta_residue]
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = idealCount K 0 from (idealCount_zero K).symm,
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le)]
  simp only [idealCount]
  rw [← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem isBigO_sum_idealCount :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  have h1 : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop] fun n => (n : ℝ) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ _ (tendsto_sum_idealCount_div K)
    filter_upwards [eventually_ne_atTop 0] with n hn h0
    exact absurd h0 (Nat.cast_ne_zero.mpr hn)
  exact h1.congr_right fun n => (Real.rpow_one _).symm

theorem LSeriesSummable_idealCount {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) z := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
    (isBigO_sum_idealCount K) (fun n => Nat.cast_nonneg _) zero_le_one hz
  simpa only [Complex.ofReal_natCast] using h

theorem tsum_fiber_const {M : Type} [AddCommMonoid M] [TopologicalSpace M] [T2Space M] (n : ℕ) (c : M) :
    ∑' _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, c = idealCount K n • c := by
  haveI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := Fintype.ofFinite _
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, idealCount, Nat.card_eq_fintype_card]

theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
  set e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ) with he
  rw [← e.summable_iff]
  have hnn : ∀ p, 0 ≤ ((fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∘ e) p := fun p =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfib : ∀ (n : ℕ) (c : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}),
      ((fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∘ e) ⟨n, c⟩ = (n : ℝ) ^ (-σ) := fun n c => by
    simp only [Function.comp_apply, he, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, c.2]
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun n => ?_, ?_⟩
  · exact Summable.of_finite
  · simp_rw [hfib, tsum_fiber_const, nsmul_eq_mul]
    have hL : Summable fun n => ‖LSeries.term (fun n => (idealCount K n : ℂ)) σ n‖ :=
      summable_norm_iff.mpr (LSeriesSummable_idealCount K (z := σ) (by simpa using hσ))
    refine hL.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · rw [h0, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr (by linarith : σ ≠ 0)), mul_zero]
    · rw [Complex.norm_natCast, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem summable_norm_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)‖ := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hz; linarith
  refine (summable_absNorm_rpow K hz).congr fun I => ?_
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h | h
  · rw [h, Nat.cast_zero, Nat.cast_zero, Complex.zero_cpow hz0, norm_zero,
      Real.zero_rpow (neg_ne_zero.mpr (by linarith : z.re ≠ 0))]
  · rw [Complex.norm_natCast_cpow_of_pos h, Complex.neg_re]

theorem summable_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) :=
  (summable_norm_absNorm_cpow K hz).of_norm

theorem tsum_absNorm_cpow_eq_dedekindZeta {z : ℂ} (hz : 1 < z.re) :
    ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) = dedekindZeta K z := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hz; linarith
  set e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ) with he
  have hs : Summable ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e) :=
    e.summable_iff.mpr (summable_absNorm_cpow K hz)
  have hfib : ∀ (n : ℕ) (c : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}),
      ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e) ⟨n, c⟩ = (n : ℂ) ^ (-z) :=
    fun n c => by simp only [Function.comp_apply, he, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, c.2]
  rw [← e.tsum_eq, show (fun c => (fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) (e c))
      = (fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)) ∘ e from rfl, hs.tsum_sigma,
    dedekindZeta_eq_LSeries, LSeries]
  refine tsum_congr fun n => ?_
  simp_rw [hfib]
  rw [tsum_fiber_const, nsmul_eq_mul, LSeries.term_def]
  split_ifs with h0
  · rw [h0, Nat.cast_zero, Complex.zero_cpow hz0, mul_zero]
  · rw [Complex.cpow_neg, div_eq_mul_inv]

abbrev Primes : Type u := {Q : Ideal (𝓞 K) // Prime Q}

def primeSet (T : Finset (Primes K)) : Set (Ideal (𝓞 K)) :=
  {I | I ≠ 0 ∧ ∀ Q : Primes K, Q.1 ∣ I → Q ∈ T}

theorem primeSet_empty : primeSet K ∅ = {⊤} := by
  ext I
  simp only [primeSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hI0, hprime⟩
    by_contra hne
    have hnu : ¬IsUnit I := fun h => hne (Ideal.isUnit_iff.mp h)
    obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_factors hI0 hnu
    exact absurd (hprime ⟨P, UniqueFactorizationMonoid.prime_of_factor P hP⟩
      (UniqueFactorizationMonoid.dvd_of_mem_factors hP)) (Finset.notMem_empty _)
  · rintro rfl
    refine ⟨?_, fun Q hdvd => ?_⟩
    · intro h
      rw [← Ideal.one_eq_top] at h
      exact one_ne_zero h
    · exact absurd (Ideal.isUnit_iff.mpr (top_le_iff.mp (Ideal.dvd_iff_le.mp hdvd))) Q.2.not_unit

theorem two_le_absNorm (Q : Primes K) : 2 ≤ Ideal.absNorm Q.1 := by
  have h0 : Ideal.absNorm Q.1 ≠ 0 := fun h =>
    Q.2.ne_zero (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm Q.1 ≠ 1 := fun h =>
    Q.2.not_unit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  omega

theorem norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    ‖((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have h2 := two_le_absNorm K Q
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  have h1 : (1 : ℝ) < (Ideal.absNorm Q.1 : ℕ) := by exact_mod_cast h2
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem one_sub_absNorm_cpow_ne_zero {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    (1 : ℂ) - ((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hlt := norm_absNorm_cpow_neg_lt_one K hs Q
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

theorem cpow_pow_natCast (m k : ℕ) (v : ℂ) :
    ((m ^ k : ℕ) : ℂ) ^ v = (((m : ℕ) : ℂ) ^ v) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

theorem tsum_primeSet_insert {s : ℂ} (hs : 1 < s.re) (P : Primes K)
    {T : Finset (Primes K)} (hPT : P ∉ T) :
    ∑' I : primeSet K (insert P T), ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
          * ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hP0 : P.1 ≠ 0 := P.2.ne_zero
  have hmemF : ∀ kc : ℕ × primeSet K T, P.1 ^ kc.1 * kc.2.1 ∈ primeSet K (insert P T) := by
    rintro ⟨k, ⟨c, hc0, hcmem⟩⟩
    refine ⟨mul_ne_zero (pow_ne_zero k hP0) hc0, fun Q hdvd => ?_⟩
    rcases (Prime.dvd_mul Q.2).mp hdvd with hQP | hQc
    · have : Q = P := Subtype.ext
        (associated_iff_eq.mp (Prime.associated_of_dvd Q.2 P.2 (Q.2.dvd_of_dvd_pow hQP)))
      rw [this]; exact Finset.mem_insert_self P T
    · exact Finset.mem_insert_of_mem (hcmem Q hQc)
  let F : ℕ × primeSet K T → primeSet K (insert P T) := fun kc => ⟨P.1 ^ kc.1 * kc.2.1, hmemF kc⟩
  have hkey : ∀ (k k' : ℕ) (c c' : Ideal (𝓞 K)), c ∈ primeSet K T → c' ∈ primeSet K T →
      k ≤ k' → P.1 ^ k * c = P.1 ^ k' * c' → k = k' ∧ c = c' := by
    intro k k' c c' hc hc' hkk h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk
    rw [pow_add, mul_assoc] at h
    have hcc : c = P.1 ^ d * c' := mul_left_cancel₀ (pow_ne_zero k hP0) h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [pow_zero, one_mul] at hcc; exact ⟨by simp, hcc⟩
    · exfalso; exact hPT (hc.2 P (hcc ▸ dvd_mul_of_dvd_left (dvd_pow_self P.1 hd.ne') c'))
  have hFbij : Function.Bijective F := by
    constructor
    · rintro ⟨k, c⟩ ⟨k', c'⟩ hab
      have hval : P.1 ^ k * c.1 = P.1 ^ k' * c'.1 := congrArg Subtype.val hab
      rcases le_total k k' with hkk | hkk
      · obtain ⟨h1, h2⟩ := hkey k k' c.1 c'.1 c.2 c'.2 hkk hval
        exact Prod.ext h1 (Subtype.ext h2)
      · obtain ⟨h1, h2⟩ := hkey k' k c'.1 c.1 c'.2 c.2 hkk hval.symm
        exact Prod.ext h1.symm (Subtype.ext h2.symm)
    · rintro ⟨J, hJ0, hJmem⟩
      have hfin : FiniteMultiplicity P.1 J := FiniteMultiplicity.of_not_isUnit P.2.not_unit hJ0
      obtain ⟨c, hc, hPc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
      have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hJ0 hc
      have hcmem : c ∈ primeSet K T := by
        refine ⟨hc0, fun Q hQc => ?_⟩
        have hQJ : Q.1 ∣ J := hc ▸ dvd_mul_of_dvd_right hQc _
        rcases Finset.mem_insert.mp (hJmem Q hQJ) with rfl | hQT
        · exact absurd hQc hPc
        · exact hQT
      exact ⟨⟨multiplicity P.1 J, ⟨c, hcmem⟩⟩, Subtype.ext hc.symm⟩
  have hgeo : Summable (fun k : ℕ => ‖(((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ k‖) :=
    (summable_geometric_of_norm_lt_one (norm_absNorm_cpow_neg_lt_one K hs0 P)).norm
  have hsub : Summable (fun J : primeSet K T => ‖((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)‖) :=
    (summable_norm_absNorm_cpow K hs).subtype _
  calc
    ∑' I : primeSet K (insert P T), ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
        = ∑' kc : ℕ × primeSet K T,
            ((Ideal.absNorm ((Equiv.ofBijective F hFbij) kc).1 : ℕ) : ℂ) ^ (-s) :=
      ((Equiv.ofBijective F hFbij).tsum_eq
        (fun I : primeSet K (insert P T) => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))).symm
    _ = ∑' kc : ℕ × primeSet K T,
          ((((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ kc.1
            * ((Ideal.absNorm kc.2.1 : ℕ) : ℂ) ^ (-s)) := by
      refine tsum_congr fun kc => ?_
      have hval : ((Equiv.ofBijective F hFbij) kc).1 = P.1 ^ kc.1 * kc.2.1 := rfl
      rw [hval, map_mul, map_pow, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, cpow_pow_natCast]
    _ = (∑' k : ℕ, (((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) ^ k)
          * ∑' J : primeSet K T, ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) :=
      (tsum_mul_tsum_of_summable_norm hgeo hsub).symm
    _ = (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
          * ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
      rw [tsum_geometric_of_norm_lt_one (norm_absNorm_cpow_neg_lt_one K hs0 P)]

theorem tsum_primeSet_eq_prod {s : ℂ} (hs : 1 < s.re) (T : Finset (Primes K)) :
    ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
  induction T using Finset.induction_on with
  | empty =>
    rw [primeSet_empty,
      tsum_singleton ⊤ (fun J : Ideal (𝓞 K) => ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)),
      Finset.prod_empty, Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow]
  | insert P T hPT ih =>
    rw [tsum_primeSet_insert K hs P hPT, Finset.prod_insert hPT, ih]

theorem mem_primeSet_of_factors {I : Ideal (𝓞 K)} (hI : I ≠ 0) {T : Finset (Primes K)}
    (hT : ∀ Q : Primes K, Q.1 ∈ UniqueFactorizationMonoid.factors I → Q ∈ T) :
    I ∈ primeSet K T := by
  refine ⟨hI, fun Q hdvd => ?_⟩
  obtain ⟨R, hR, hQR⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI Q.2.irreducible hdvd
  have hQ : Q.1 = R := associated_iff_eq.mp hQR
  exact hT Q (hQ ▸ hR)

theorem tendsto_tsum_primeSet_of_summable {f : Ideal (𝓞 K) → ℂ}
    (hf : Summable fun I => ‖f I‖) (hf0 : f 0 = 0) :
    Tendsto (fun T : Finset (Primes K) => ∑' I : primeSet K T, f I) atTop (𝓝 (∑' I, f I)) := by
  have hfs : Summable f := hf.of_norm

  have htail : Tendsto (fun F : Finset (Ideal (𝓞 K)) =>
      ∑' I, ((↑F : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I) atTop (𝓝 0) := by
    refine (tendsto_tsum_compl_atTop_zero (fun I => ‖f I‖)).congr fun F => ?_
    exact tsum_subtype ((↑F : Set (Ideal (𝓞 K)))ᶜ) (fun I => ‖f I‖)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F₀, hF₀⟩ := Metric.tendsto_atTop.mp htail ε hε
  refine ⟨F₀.biUnion (fun I =>
      ((UniqueFactorizationMonoid.factors I).toFinset).subtype (fun Q => Prime Q)), fun T hT => ?_⟩

  have hin : ∀ I ∈ F₀, I ≠ 0 → I ∈ primeSet K T := by
    intro I hI hI0
    refine mem_primeSet_of_factors K hI0 fun Q hQ => hT ?_
    exact Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_subtype.mpr (Multiset.mem_toFinset.mpr hQ)⟩

  have hdom : ∀ I : Ideal (𝓞 K), ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I
      ≤ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I := by
    intro I
    by_cases hI0 : I = 0
    · have hfI : ‖f I‖ = 0 := by rw [hI0, hf0, norm_zero]
      calc ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I
          ≤ ‖f I‖ := Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => norm_nonneg _)
        _ = 0 := hfI
        _ ≤ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I :=
          Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    · by_cases hmem : I ∈ primeSet K T
      · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]
        exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
      · have hIF : I ∈ ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ) :=
          Set.mem_compl fun h => hmem (hin I (Finset.mem_coe.mp h) hI0)
        rw [Set.indicator_of_mem (Set.mem_compl hmem), Set.indicator_of_mem hIF]
  have hbound := hF₀ F₀ le_rfl
  rw [Real.dist_0_eq_abs, abs_of_nonneg (tsum_nonneg fun I =>
    Set.indicator_nonneg (fun _ _ => norm_nonneg _) I)] at hbound
  have hsplit := hfs.tsum_subtype_add_tsum_subtype_compl (primeSet K T)
  rw [dist_eq_norm, show (∑' I : primeSet K T, f I) - ∑' I, f I = -∑' I : ↥(primeSet K T)ᶜ, f I by
    rw [← hsplit]; ring, norm_neg]
  calc ‖∑' I : ↥(primeSet K T)ᶜ, f I‖
      ≤ ∑' I : ↥(primeSet K T)ᶜ, ‖f I‖ := norm_tsum_le_tsum_norm (hf.subtype _)
    _ = ∑' I, ((primeSet K T)ᶜ).indicator (fun I => ‖f I‖) I :=
      tsum_subtype ((primeSet K T)ᶜ) (fun I => ‖f I‖)
    _ ≤ ∑' I, ((↑F₀ : Set (Ideal (𝓞 K)))ᶜ).indicator (fun I => ‖f I‖) I :=
      Summable.tsum_le_tsum hdom (hf.indicator _) (hf.indicator _)
    _ < ε := hbound

theorem hasProd_primes {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : Primes K => (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) (dedekindZeta K s) := by
  have hsz : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hs; linarith
  have h := tendsto_tsum_primeSet_of_summable K
    (f := fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s))
    (summable_norm_absNorm_cpow K hs)
    (by show ((Ideal.absNorm (0 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 0
        rw [map_zero, Nat.cast_zero, Complex.zero_cpow hsz])
  rw [tsum_absNorm_cpow_eq_dedekindZeta K hs] at h
  show Tendsto _ atTop _
  exact h.congr fun T => tsum_primeSet_eq_prod K hs T

def primesEquiv : HeightOneSpectrum (𝓞 K) ≃ Primes K where
  toFun v := ⟨v.asIdeal, v.prime⟩
  invFun Q := ⟨Q.1, Ideal.isPrime_of_prime Q.2, fun h => Q.2.ne_zero (by rw [Ideal.zero_eq_bot]; exact h)⟩
  left_inv v := rfl
  right_inv Q := rfl

theorem hasProd_spectrum {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (dedekindZeta K s) :=
  (primesEquiv K).hasProd_iff.mpr (hasProd_primes K hs)

theorem summable_spectrum {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) :=
  (summable_absNorm_cpow K hs).comp_injective fun _ _ h => HeightOneSpectrum.ext h

theorem two_le_absNorm_spectrum (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal :=
  two_le_absNorm K (primesEquiv K v)

theorem norm_cpow_le_half {s : ℂ} (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have h2 := two_le_absNorm_spectrum K v
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  have h2' : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast h2
  calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re)
      ≤ (2 : ℝ) ^ (-s.re) := Real.rpow_le_rpow_of_nonpos (by norm_num) h2' (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem norm_inv_factor_le_two {s : ℂ} (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ 2 := by
  have hx := norm_cpow_le_half K hs v
  have hlow : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  calc ‖(1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
        inv_anti₀ (by norm_num) hlow
    _ = 2 := by norm_num

theorem multipliable_inv_factor_subtype {s : ℂ} (hs : 1 < s.re) (p : HeightOneSpectrum (𝓞 K) → Prop) :
    Multipliable fun v : {v // p v} => (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  have hxs : Summable fun v : {v // p v} => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) :=
    (summable_spectrum K hs).subtype _
  have hne : ∀ v : {v // p v}, (1 : ℂ) - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 := by
    intro v h
    have hx := norm_cpow_le_half K hs.le v.1
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hx
    norm_num at hx
  have hg : Summable fun v : {v // p v} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) / (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded (g := fun v => 2 * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖)
      (hxs.norm.mul_left 2) fun v => ?_
    have hx := norm_cpow_le_half K hs.le v.1
    have hlow : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
      rw [norm_one] at this
      linarith
    rw [norm_div]
    calc ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ / ‖(1 : ℂ) - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖
        ≤ ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ / (1 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hlow
      _ = 2 * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by ring
  refine (Complex.multipliable_one_add_of_summable hg).congr fun v => ?_
  field_simp [hne v]
  ring

theorem dedekindZeta_eq_prod_mul_tprod {s : ℂ} (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    dedekindZeta K s = (∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) *
      ∏' v : {v // v ∉ T}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  have hall := hasProd_spectrum K hs
  have hT := Finset.hasProd T (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
  have hC : HasProd ((fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ∘
      ((↑) : ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set (HeightOneSpectrum (𝓞 K))) → HeightOneSpectrum (𝓞 K)))
      (∏' v : {v // v ∉ T}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) :=
    (multipliable_inv_factor_subtype K hs (fun v => v ∉ T)).hasProd
  exact hall.unique (hT.mul_compl hC)

theorem tendsto_norm_dedekindZeta_atTop :
    Tendsto (fun σ : ℝ => ‖dedekindZeta K (σ : ℂ)‖) (𝓝[>] 1) atTop := by
  have hres := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hr : 0 < dedekindZeta_residue K := dedekindZeta_residue_pos K

  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      dedekindZeta_residue K / 2 < ‖((σ : ℂ) - 1) * dedekindZeta K (σ : ℂ)‖ := by
    have h := hres.norm
    have hlt : dedekindZeta_residue K / 2 < ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hr.le]; linarith
    exact h.eventually (lt_mem_nhds hlt)

  have hshift : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun σ : ℝ => σ - 1) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) := tendsto_id.sub_const 1
      rw [sub_self] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hσ))
  have hdiv : Tendsto (fun σ : ℝ => dedekindZeta_residue K / 2 * (σ - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop :=
    (tendsto_inv_nhdsGT_zero.comp hshift).const_mul_atTop (half_pos hr)
  refine tendsto_atTop_mono' _ ?_ hdiv
  filter_upwards [hev, self_mem_nhdsWithin] with σ hσ hσ1
  have hpos : 0 < σ - 1 := sub_pos.mpr hσ1
  rw [norm_mul, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg hpos.le] at hσ
  rw [← div_eq_mul_inv, div_le_iff₀ hpos, mul_comm]
  exact hσ.le

theorem tendsto_norm_tprod_atTop (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun σ : ℝ => ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖) (𝓝[>] 1) atTop := by
  have hζ := tendsto_norm_dedekindZeta_atTop K
  have hpow : (0 : ℝ) < 2 ^ T.card := by positivity
  refine tendsto_atTop_mono' _ ?_ (hζ.atTop_div_const hpow)
  filter_upwards [self_mem_nhdsWithin] with σ hσ1
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ1
  rw [dedekindZeta_eq_prod_mul_tprod K hs T, norm_mul, div_le_iff₀ hpow, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖
      ≤ ∏ v ∈ T, ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _v ∈ T, (2 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun v _ => norm_inv_factor_le_two K hs.le v)
    _ = 2 ^ T.card := Finset.prod_const 2

end Ws41.EulerZeta
p2m_reactivate "P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41 P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41.EulerZeta"
p2m_reactivate "P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41"

namespace Ws41
namespace N1bProof

open NumberField.InfinitePlace Ws41.EulerZeta

variable (K : Type) [Field K] [NumberField K]

def Dinv (s : ℂ) : ℂ :=
  ((Gammaℝ s)⁻¹) ^ nrRealPlaces K * ((Gammaℝ s)⁻¹ * (Gammaℝ (s + 1))⁻¹) ^ nrComplexPlaces K *
    (((|discr K| : ℤ) : ℂ)) ^ (-(s / 2))

theorem discrC_ne_zero : (((|discr K| : ℤ) : ℂ)) ≠ 0 :=
  Int.cast_ne_zero.mpr (abs_ne_zero.mpr (discr_ne_zero K))

theorem differentiable_Dinv : Differentiable ℂ (Dinv K) := by
  have h1 : Differentiable ℂ fun s : ℂ => (Gammaℝ s)⁻¹ := differentiable_Gammaℝ_inv
  have h2 : Differentiable ℂ fun s : ℂ => (Gammaℝ (s + 1))⁻¹ :=
    differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
  have h3 : Differentiable ℂ fun s : ℂ => (((|discr K| : ℤ) : ℂ)) ^ (-(s / 2)) :=
    Differentiable.const_cpow ((differentiable_id.div_const 2).neg) (Or.inl (discrC_ne_zero K))
  exact ((h1.pow _).mul ((h1.mul h2).pow _)).mul h3

theorem D_mul_Dinv {s : ℂ} (hs : 0 < s.re) :
    (((|discr K| : ℤ) : ℂ)) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * Dinv K s
      = 1 := by
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hG1 : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hd : (((|discr K| : ℤ) : ℂ)) ^ (s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl (discrC_ne_zero K)
  have hA : Gammaℝ s ^ nrRealPlaces K ≠ 0 := pow_ne_zero _ hG
  have hB : (Gammaℝ s * Gammaℝ (s + 1)) ^ nrComplexPlaces K ≠ 0 := pow_ne_zero _ (mul_ne_zero hG hG1)
  rw [Dinv, ← Gammaℝ_mul_Gammaℝ_add_one, Complex.cpow_neg, ← mul_inv, inv_pow, inv_pow]
  calc (((|discr K| : ℤ) : ℂ)) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * (Gammaℝ s * Gammaℝ (s + 1)) ^ nrComplexPlaces K
        * ((Gammaℝ s ^ nrRealPlaces K)⁻¹ * ((Gammaℝ s * Gammaℝ (s + 1)) ^ nrComplexPlaces K)⁻¹
          * ((((|discr K| : ℤ) : ℂ)) ^ (s / 2))⁻¹)
      = ((((|discr K| : ℤ) : ℂ)) ^ (s / 2) * ((((|discr K| : ℤ) : ℂ)) ^ (s / 2))⁻¹)
        * (Gammaℝ s ^ nrRealPlaces K * (Gammaℝ s ^ nrRealPlaces K)⁻¹)
        * ((Gammaℝ s * Gammaℝ (s + 1)) ^ nrComplexPlaces K * ((Gammaℝ s * Gammaℝ (s + 1)) ^ nrComplexPlaces K)⁻¹) := by
        ring
    _ = 1 := by rw [mul_inv_cancel₀ hd, mul_inv_cancel₀ hA, mul_inv_cancel₀ hB]; ring

theorem differentiable_finset_prod {ι : Type*} (u : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ u, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun s => ∏ i ∈ u, f i s) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiable_const _
  | insert a u ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem differentiable_finprod_factor (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ (fun s : ℂ => ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) :=
  differentiable_finset_prod T _ fun v _ =>
    (differentiable_const _).sub (differentiable_id.neg.const_cpow (Or.inl (by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))))

theorem one_sub_cpow_ne_zero' {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 :=
  one_sub_absNorm_cpow_ne_zero K hs (primesEquiv K v)

theorem finprod_factor_ne_zero {s : ℂ} (hs : 0 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => one_sub_cpow_ne_zero' K hs v

theorem exists_continuation (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L ({s : ℂ | 1 / 2 < s.re} \ {1}) ∧
      (∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ Tendsto (fun s : ℂ => (s - 1) * L s) (𝓝[≠] 1) (𝓝 κ) := by
  obtain ⟨Λ, hΛd, -, hΛeq, ⟨ξ, hξd, hξeq, -⟩, hξne, -⟩ := NumberField.exists_completedDedekindZeta_package K
  have hξ1 : ξ 1 ≠ 0 := (hξne ξ hξd hξeq).2
  set P : ℂ → ℂ := fun s => ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) with hP
  have hPd : Differentiable ℂ P := differentiable_finprod_factor K T
  refine ⟨fun s => Λ s * Dinv K s * P s, ?_, ?_, ?_⟩
  ·
    refine ((hΛd.mono ?_).mul (differentiable_Dinv K).differentiableOn).mul hPd.differentiableOn
    intro s hs
    have hs1 : 1 / 2 < s.re := hs.1
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h => ?_, fun h => hs.2 (by simpa using h)⟩
    rw [h, Complex.zero_re] at hs1
    norm_num at hs1
  ·
    intro s hs
    have hs0 : 0 < s.re := by linarith
    show Λ s * Dinv K s * P s = _
    rw [hΛeq s hs, show (((|discr K| : ℤ) : ℂ)) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * dedekindZeta K s * Dinv K s
        = ((((|discr K| : ℤ) : ℂ)) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K * Dinv K s)
          * dedekindZeta K s by ring, D_mul_Dinv K hs0, one_mul, dedekindZeta_eq_prod_mul_tprod K hs T, hP]
    rw [mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun v _ => ?_, one_mul]
    exact mul_inv_cancel₀ (one_sub_cpow_ne_zero' K hs0 v)
  ·
    refine ⟨ξ 1 * Dinv K 1 * P 1, ?_, ?_⟩
    · refine mul_ne_zero (mul_ne_zero hξ1 ?_) (finprod_factor_ne_zero K (by norm_num) T)
      intro h
      have := D_mul_Dinv K (s := 1) (by norm_num)
      rw [h, mul_zero] at this
      exact zero_ne_one this
    · have hG : ContinuousAt (fun s : ℂ => ξ s / s * Dinv K s * P s) 1 :=
        (((hξd.continuous.continuousAt).div continuousAt_id one_ne_zero).mul
          (differentiable_Dinv K).continuous.continuousAt).mul hPd.continuous.continuousAt
      have hlim := hG.tendsto
      simp only [div_one] at hlim
      refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
      have h0 : ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), s ≠ 0 :=
        nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero)
      filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hs1
      have hs1' : s ≠ 1 := hs1
      show ξ s / s * Dinv K s * P s = (s - 1) * (Λ s * Dinv K s * P s)
      rw [hξeq s hs0 hs1']
      field_simp

end Ws41.N1bProof
p2m_reactivate "P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41 P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41.EulerZeta"
p2m_reactivate "P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41 P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41.EulerZeta"

end
p2m_reactivate "P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41 P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.Ws41.EulerZeta"

open IsDedekindDomain NumberField Filter Topology in
theorem solution (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L ({s : ℂ | 1 / 2 < s.re} \ {1}) ∧
      (∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ Tendsto (fun s : ℂ => (s - 1) * L s) (𝓝[≠] 1) (𝓝 κ) :=
  Ws41.N1bProof.exists_continuation K T

end S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul
end P2MW
export P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul (solution)
