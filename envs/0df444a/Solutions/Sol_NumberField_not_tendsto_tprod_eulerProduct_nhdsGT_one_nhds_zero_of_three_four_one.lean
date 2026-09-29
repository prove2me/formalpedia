-- Prove2me | solution 1 for NumberField.not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7551f7a7-8cba-511d-b944-db4e5dd3082d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one

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

section L0

variable {K}

theorem absNorm_cast_ne_zero (v : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

theorem absNorm_pos' (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {z : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ}

theorem norm_term_le (hz : ∀ v, ‖z v‖ ≤ 1) (s : ℂ) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    ‖z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hz v)

theorem norm_term_le_half (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    ‖z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
  (norm_term_le hz s v).trans (norm_cpow_le_half K hs v.1)

theorem half_le_re_one_sub_term (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    (1 : ℝ) / 2 ≤ ((1 : ℂ) - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)).re := by
  have h := norm_term_le_half hz hs v
  have hre := abs_re_le_norm (z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
  rw [Complex.sub_re, Complex.one_re]
  have := le_abs_self ((z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)).re)
  linarith

theorem one_sub_term_ne_zero (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    (1 : ℂ) - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have := half_le_re_one_sub_term hz hs v
  rw [h, Complex.zero_re] at this
  norm_num at this

theorem arg_one_sub_term_ne_pi (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    ((1 : ℂ) - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)).arg ≠ Real.pi := by
  rw [Ne, Complex.arg_eq_pi_iff, not_and_or]
  left
  have := half_le_re_one_sub_term hz hs v
  linarith

theorem norm_log_inv_one_sub_le (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    ‖log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)‖
      ≤ (3 / 2) * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
  rw [Complex.log_inv _ (arg_one_sub_term_ne_pi hz hs v), norm_neg, sub_eq_add_neg]
  refine (Complex.norm_log_one_add_half_le_self ?_).trans ?_
  · rw [norm_neg]; exact norm_term_le_half hz hs v
  · rw [norm_neg]; exact mul_le_mul_of_nonneg_left (norm_term_le hz s v) (by norm_num)

theorem summable_log_inv_one_sub (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) := by
  have hxs : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) := (summable_spectrum K hs).subtype _
  exact Summable.of_norm_bounded (g := fun v => (3 / 2) * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖)
    (hxs.norm.mul_left _) fun v => norm_log_inv_one_sub_le hz hs.le v

theorem multipliable_factor (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ :=
  Complex.multipliable_of_summable_log (summable_log_inv_one_sub hz hs)

theorem tprod_eq_cexp (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
      = cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) :=
  (Complex.cexp_tsum_eq_tprod (fun v => inv_ne_zero (one_sub_term_ne_zero hz hs.le v))
    (summable_log_inv_one_sub hz hs)).symm

theorem differentiableAt_log_term (hz : ∀ v, ‖z v‖ ≤ 1) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (fun s : ℂ => log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) s := by
  have hN : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ≠ 0 := absNorm_cast_ne_zero v.1
  have h1 : DifferentiableAt ℂ (fun s : ℂ => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hN)
  have h2 : DifferentiableAt ℂ
      (fun s : ℂ => (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) s :=
    ((differentiableAt_const _).sub (h1.const_mul _)).inv (one_sub_term_ne_zero hz hs v)
  refine h2.clog (Complex.mem_slitPlane_iff.mpr (Or.inl ?_))
  rw [Complex.inv_re]
  exact div_pos (lt_of_lt_of_le (by norm_num) (half_le_re_one_sub_term hz hs v))
    (Complex.normSq_pos.mpr (one_sub_term_ne_zero hz hs v))

theorem differentiableOn_tsum_log_delta (hz : ∀ v, ‖z v‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ (fun s : ℂ => ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) {s : ℂ | 1 + δ < s.re} := by
  have hσ : 1 < 1 + δ := by linarith
  have hu : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      (3 / 2 : ℝ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(1 + δ)) := by
    have h := (summable_absNorm_rpow K hσ).comp_injective
      (fun (a b : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (h : a.1.asIdeal = b.1.asIdeal) =>
        Subtype.ext (HeightOneSpectrum.ext h))
    exact h.mul_left _
  refine differentiableOn_tsum_of_summable_norm hu
    (fun v s hs => (differentiableAt_log_term hz v ?_).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re) ?_
  · have hs' : 1 + δ < s.re := hs
    linarith
  · intro v s hs
    have hs' : 1 + δ < s.re := hs
    refine (norm_log_inv_one_sub_le hz (by linarith) v).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Complex.norm_natCast_cpow_of_pos (absNorm_pos' v.1), Complex.neg_re]
    have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.1.asIdeal : ℕ) := by exact_mod_cast two_le_absNorm_spectrum K v.1
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem differentiableOn_tsum_log (hz : ∀ v, ‖z v‖ ≤ 1) :
    DifferentiableOn ℂ (fun s : ℂ => ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs' : 1 < s.re := hs
  have hδ0 : 0 < (s.re - 1) / 2 := by linarith
  have hmem : s ∈ {w : ℂ | 1 + (s.re - 1) / 2 < w.re} := by
    show 1 + (s.re - 1) / 2 < s.re
    linarith
  exact ((differentiableOn_tsum_log_delta hz hδ0).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem differentiableOn_tprod (hz : ∀ v, ‖z v‖ ≤ 1) :
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) {s : ℂ | 1 < s.re} :=
  (differentiableOn_tsum_log hz).cexp.congr fun _ hs => tprod_eq_cexp hz hs

end L0

section N2

variable {K}
variable {T : Finset (HeightOneSpectrum (𝓞 K))}

theorem cpow_neg_ofReal_eq (v : HeightOneSpectrum (𝓞 K)) (σ : ℝ) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, Complex.ofReal_neg]

theorem rpow_neg_lt_one (v : HeightOneSpectrum (𝓞 K)) {σ : ℝ} (hσ : 1 < σ) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) < 1 := by
  have h2 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (two_le_absNorm_spectrum K v)
  exact Real.rpow_lt_one_of_one_lt_of_neg h2 (by linarith)

theorem re_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

theorem re_log_comb_nonneg_zero {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) {b : ℂ} (hb : ‖b‖ ≤ 1) :
    0 ≤ 3 * (-log (1 - (x : ℂ))).re + 4 * (-log (1 - 0 * (x : ℂ))).re + (-log (1 - b * x)).re := by
  have h1 : (-log (1 - (x : ℂ))).re = -Real.log (1 - x) := by
    rw [neg_re, show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring, Complex.log_ofReal_re]
  have h2 : (-log (1 - b * (x : ℂ))).re = -Real.log ‖1 - b * (x : ℂ)‖ := by rw [neg_re, Complex.log_re]
  have h3 : (-log (1 - 0 * (x : ℂ))).re = 0 := by simp
  rw [h1, h2, h3]
  have hlog1 : Real.log (1 - x) ≤ -x := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - x); linarith
  have hbx : ‖b * (x : ℂ)‖ ≤ x := by
    rw [norm_mul, Complex.norm_of_nonneg hx₀]
    exact mul_le_of_le_one_left hx₀ hb
  have hnorm : ‖1 - b * (x : ℂ)‖ ≤ 1 + x := by
    calc ‖1 - b * (x : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖b * (x : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + x := by rw [norm_one]; linarith
  have hpos : 0 < ‖1 - b * (x : ℂ)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (b * x)
    rw [norm_one] at this
    linarith
  have hlog2 : Real.log ‖1 - b * (x : ℂ)‖ ≤ x := by
    calc Real.log ‖1 - b * (x : ℂ)‖ ≤ Real.log (1 + x) := Real.log_le_log hpos hnorm
      _ ≤ x := by have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x); linarith
  linarith

theorem log_inv_one_sub {w : ℂ} (hw : ‖w‖ < 1) : log ((1 - w)⁻¹) = -log (1 - w) := by
  refine Complex.log_inv _ ?_
  rw [Ne, Complex.arg_eq_pi_iff, not_and_or]
  left
  have := abs_re_le_norm w
  have := le_abs_self w.re
  rw [Complex.sub_re, Complex.one_re]
  linarith

theorem termwise_nonneg {a b : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ}
    (hab : ∀ v, (‖a v‖ = 1 ∧ b v = a v ^ 2) ∨ (a v = 0 ∧ ‖b v‖ ≤ 1))
    {σ : ℝ} (hσ : 1 < σ) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    0 ≤ 3 * (log ((1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)).re
      + 4 * (log ((1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)).re
      + (log ((1 - b v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)).re := by
  set x : ℝ := ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ) with hx
  have hx₀ : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hx₁ : x < 1 := rpow_neg_lt_one v.1 hσ
  have hxC : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)) = (x : ℂ) := cpow_neg_ofReal_eq v.1 σ
  have hxn : ‖(x : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg hx₀]; exact hx₁
  have ha1 : ‖a v‖ ≤ 1 := by
    rcases hab v with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.le
    · rw [h, norm_zero]; exact zero_le_one
  have hb1 : ‖b v‖ ≤ 1 := by
    rcases hab v with ⟨h, h'⟩ | ⟨-, h'⟩
    · rw [h', norm_pow, h, one_pow]
    · exact h'
  have hwa : ‖a v * (x : ℂ)‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha1) hxn
  have hwb : ‖b v * (x : ℂ)‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hb1) hxn
  rw [hxC, log_inv_one_sub hxn, log_inv_one_sub hwa, log_inv_one_sub hwb]
  rcases hab v with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [hb, mul_comm (a v), mul_comm (a v ^ 2)]
    exact re_log_comb_nonneg' hx₀ hx₁ ha
  · rw [ha]
    exact re_log_comb_nonneg_zero hx₀ hx₁ hb

theorem norm_tprod_eq_exp {c : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - c v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖
      = Real.exp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (log ((1 - c v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)).re) := by
  rw [tprod_eq_cexp hc hs, Complex.norm_exp, Complex.re_tsum (summable_log_inv_one_sub hc hs)]

theorem summable_re_log {c : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      (log ((1 - c v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)).re :=
  (Complex.hasSum_re (summable_log_inv_one_sub hc hs).hasSum).summable

theorem one_le_norm_prod {a b : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ}
    (hab : ∀ v, (‖a v‖ = 1 ∧ b v = a v ^ 2) ∨ (a v = 0 ∧ ‖b v‖ ≤ 1))
    {σ : ℝ} (hσ : 1 < σ) :
    1 ≤ ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ^ 3
        * ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ^ 4
        * ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - b v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have ha1 : ∀ v, ‖a v‖ ≤ 1 := fun v => by
    rcases hab v with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.le
    · rw [h, norm_zero]; exact zero_le_one
  have hb1 : ∀ v, ‖b v‖ ≤ 1 := fun v => by
    rcases hab v with ⟨h, h'⟩ | ⟨-, h'⟩
    · rw [h', norm_pow, h, one_pow]
    · exact h'
  have h1 : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, ‖(fun _ => (1 : ℂ)) v‖ ≤ 1 := fun v => by simp
  have hone : (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)
      = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (fun _ => (1 : ℂ)) v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ :=
    tprod_congr fun v => by rw [one_mul]
  rw [hone, norm_tprod_eq_exp h1 hs, norm_tprod_eq_exp ha1 hs, norm_tprod_eq_exp hb1 hs,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Real.one_le_exp_iff]
  have S1 := summable_re_log h1 hs
  have Sa := summable_re_log ha1 hs
  have Sb := summable_re_log hb1 hs
  rw [← tsum_mul_left, ← tsum_mul_left, ← (S1.mul_left _).tsum_add (Sa.mul_left _),
    ← ((S1.mul_left _).add (Sa.mul_left _)).tsum_add Sb]
  refine tsum_nonneg fun v => ?_
  have := termwise_nonneg hab hσ v
  simp only [one_mul] at this ⊢
  push_cast
  linarith

end N2

end Ws41.EulerZeta
p2m_reactivate "P2MW.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one.Ws41 P2MW.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one.Ws41.EulerZeta"
p2m_reactivate "P2MW.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one.Ws41"

end
p2m_reactivate "P2MW.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one.Ws41 P2MW.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one.Ws41.EulerZeta"

open IsDedekindDomain NumberField Filter Topology in
theorem solution (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (a b : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ)
    (hab : ∀ v, (‖a v‖ = 1 ∧ b v = a v ^ 2) ∨ (a v = 0 ∧ ‖b v‖ ≤ 1))
    (hζ : ∃ C δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ C / (σ - 1))
    (ha : ∃ U ∈ 𝓝 (1 : ℂ), ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      ∀ s ∈ U, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
    (hb : ∃ B δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - b v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ B) :
    ¬ Tendsto
        (fun σ : ℝ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)
        (𝓝[>] 1) (𝓝 0) := by
  intro h0
  obtain ⟨C, δ₁, hδ₁, hC⟩ := hζ
  obtain ⟨U, hU, L, hLd, hLE⟩ := ha
  obtain ⟨B, δ₂, hδ₂, hB⟩ := hb

  have ht1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 1) (𝓝 1) := by
    simpa using Complex.continuous_ofReal.tendsto (1 : ℝ)
  have heq : (fun σ : ℝ => L σ) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun σ : ℝ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹) := by
    filter_upwards [nhdsWithin_le_nhds (ht1.eventually hU), self_mem_nhdsWithin] with σ h1 h2
    exact hLE _ h1 (by simpa using h2)
  have hlim : Tendsto (fun σ : ℝ => L σ) (𝓝[>] (1 : ℝ)) (𝓝 (L 1)) :=
    ((hLd.continuousOn.continuousAt hU).tendsto.comp ht1).mono_left nhdsWithin_le_nhds
  have hL1 : L 1 = 0 := tendsto_nhds_unique (hlim.congr' heq) h0
  obtain ⟨C', hC'0, hC'⟩ := ((hLd.differentiableAt hU).isBigO_sub).exists_pos
  have hev1 : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ C' * (σ - 1) := by
    filter_upwards [nhdsWithin_le_nhds (ht1.eventually hC'.bound), heq, self_mem_nhdsWithin]
      with σ h1 h2 h3
    have h3' : 1 < σ := h3
    rw [hL1, sub_zero, h2, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ σ - 1)] at h1
    exact h1
  have hev2 : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), σ ∈ Set.Ioo 1 (1 + min δ₁ δ₂) :=
    Ioo_mem_nhdsGT (by have := lt_min hδ₁ hδ₂; linarith)
  have hev3 : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), C ^ 3 * C' ^ 4 * B * (σ - 1) < 1 := by
    have ht0 : Tendsto (fun σ : ℝ => C ^ 3 * C' ^ 4 * B * (σ - 1)) (𝓝 (1 : ℝ))
        (𝓝 (C ^ 3 * C' ^ 4 * B * (1 - 1))) := (tendsto_id.sub_const 1).const_mul _
    rw [sub_self, mul_zero] at ht0
    exact (ht0.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds one_pos)
  obtain ⟨σ, h1, ⟨hσ1, hσδ⟩, h3⟩ := (hev1.and (hev2.and hev3)).exists
  have hσpos : 0 < σ - 1 := by linarith
  have hE1 := hC σ hσ1 (by linarith [min_le_left δ₁ δ₂])
  have hEb := hB σ hσ1 (by linarith [min_le_right δ₁ δ₂])
  have hC0 : 0 ≤ C := by
    by_contra h
    push Not at h
    have : C / (σ - 1) < 0 := div_neg_of_neg_of_pos h hσpos
    linarith [norm_nonneg (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hEb
  have key := Ws41.EulerZeta.one_le_norm_prod hab hσ1
  have hup : ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ^ 3
        * ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ^ 4
        * ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - b v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖
      ≤ (C / (σ - 1)) ^ 3 * (C' * (σ - 1)) ^ 4 * B :=
    mul_le_mul (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hE1 3) (pow_le_pow_left₀ (norm_nonneg _) h1 4)
      (by positivity) (pow_nonneg (div_nonneg hC0 hσpos.le) 3)) hEb (norm_nonneg _)
      (mul_nonneg (pow_nonneg (div_nonneg hC0 hσpos.le) 3) (by positivity))
  have heqv : (C / (σ - 1)) ^ 3 * (C' * (σ - 1)) ^ 4 * B = C ^ 3 * C' ^ 4 * B * (σ - 1) := by
    field_simp
  linarith

end S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one
end P2MW
export P2MW.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one (solution)
