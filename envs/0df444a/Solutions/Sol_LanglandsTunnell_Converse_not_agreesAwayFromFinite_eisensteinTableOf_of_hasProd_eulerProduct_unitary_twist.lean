-- Prove2me | solution 1 for LanglandsTunnell.Converse.not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7e93a8a1-cdd1-51f5-a25e-bc18af54f78f

import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

noncomputable section

open NumberField Filter Complex
open scoped Topology Classical

namespace Q15PLK

namespace Zeta

universe u

variable (K : Type u) [Field K] [NumberField K]

private def idealCount (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

private theorem dedekindZeta_eq_LSeries (z : ℂ) :
    dedekindZeta K z = LSeries (fun n => (idealCount K n : ℂ)) z := rfl

private scoped instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOf_absNorm_eq n).to_subtype

private theorem idealCount_zero : idealCount K 0 = 1 := by
  rw [idealCount]
  have : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} :=
    { default := ⟨⊥, Ideal.absNorm_eq_zero_iff.mpr rfl⟩
      uniq := fun I => Subtype.ext (Ideal.absNorm_eq_zero_iff.mp I.2) }
  exact Nat.card_unique

private theorem tendsto_sum_idealCount_div :
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

private theorem isBigO_sum_idealCount :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
  have h1 : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) =O[atTop] fun n => (n : ℝ) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ _ (tendsto_sum_idealCount_div K)
    filter_upwards [eventually_ne_atTop 0] with n hn h0
    exact absurd h0 (Nat.cast_ne_zero.mpr hn)
  exact h1.congr_right fun n => (Real.rpow_one _).symm

private theorem LSeriesSummable_idealCount {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) z := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
    (isBigO_sum_idealCount K) (fun n => Nat.cast_nonneg _) zero_le_one hz
  simpa only [Complex.ofReal_natCast] using h

private theorem tsum_fiber_const {M : Type} [AddCommMonoid M] [TopologicalSpace M] [T2Space M] (n : ℕ) (c : M) :
    ∑' _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, c = idealCount K n • c := by
  haveI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := Fintype.ofFinite _
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, idealCount, Nat.card_eq_fintype_card]

private theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
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

private theorem summable_norm_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-z)‖ := by
  have hz0 : -z ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hz; linarith
  refine (summable_absNorm_rpow K hz).congr fun I => ?_
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with h | h
  · rw [h, Nat.cast_zero, Nat.cast_zero, Complex.zero_cpow hz0, norm_zero,
      Real.zero_rpow (neg_ne_zero.mpr (by linarith : z.re ≠ 0))]
  · rw [Complex.norm_natCast_cpow_of_pos h, Complex.neg_re]

private theorem summable_absNorm_cpow {z : ℂ} (hz : 1 < z.re) :
    Summable fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-z) :=
  (summable_norm_absNorm_cpow K hz).of_norm

private theorem tsum_absNorm_cpow_eq_dedekindZeta {z : ℂ} (hz : 1 < z.re) :
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

private abbrev Primes : Type u := {Q : Ideal (𝓞 K) // Prime Q}

private def primeSet (T : Finset (Primes K)) : Set (Ideal (𝓞 K)) :=
  {I | I ≠ 0 ∧ ∀ Q : Primes K, Q.1 ∣ I → Q ∈ T}

private theorem primeSet_empty : primeSet K ∅ = {⊤} := by
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

private theorem two_le_absNorm (Q : Primes K) : 2 ≤ Ideal.absNorm Q.1 := by
  have h0 : Ideal.absNorm Q.1 ≠ 0 := fun h =>
    Q.2.ne_zero (by rw [Ideal.zero_eq_bot]; exact Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm Q.1 ≠ 1 := fun h =>
    Q.2.not_unit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  omega

private theorem norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    ‖((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have h2 := two_le_absNorm K Q
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  have h1 : (1 : ℝ) < (Ideal.absNorm Q.1 : ℕ) := by exact_mod_cast h2
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

private theorem one_sub_absNorm_cpow_ne_zero {s : ℂ} (hs : 0 < s.re) (Q : Primes K) :
    (1 : ℂ) - ((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hlt := norm_absNorm_cpow_neg_lt_one K hs Q
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

private theorem cpow_pow_natCast (m k : ℕ) (v : ℂ) :
    ((m ^ k : ℕ) : ℂ) ^ v = (((m : ℕ) : ℂ) ^ v) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

private theorem tsum_primeSet_insert {s : ℂ} (hs : 1 < s.re) (P : Primes K)
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

private theorem tsum_primeSet_eq_prod {s : ℂ} (hs : 1 < s.re) (T : Finset (Primes K)) :
    ∑' I : primeSet K T, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
      = ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
  induction T using Finset.induction_on with
  | empty =>
    rw [primeSet_empty,
      tsum_singleton ⊤ (fun J : Ideal (𝓞 K) => ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)),
      Finset.prod_empty, Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow]
  | insert P T hPT ih =>
    rw [tsum_primeSet_insert K hs P hPT, Finset.prod_insert hPT, ih]

private theorem mem_primeSet_of_factors {I : Ideal (𝓞 K)} (hI : I ≠ 0) {T : Finset (Primes K)}
    (hT : ∀ Q : Primes K, Q.1 ∈ UniqueFactorizationMonoid.factors I → Q ∈ T) :
    I ∈ primeSet K T := by
  refine ⟨hI, fun Q hdvd => ?_⟩
  obtain ⟨R, hR, hQR⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI Q.2.irreducible hdvd
  have hQ : Q.1 = R := associated_iff_eq.mp hQR
  exact hT Q (hQ ▸ hR)

private theorem tendsto_tsum_primeSet_of_summable {f : Ideal (𝓞 K) → ℂ}
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

private theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hsz : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hsum : Summable (fun P : Primes K => ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)) :=
    (summable_absNorm_cpow K hs).comp_injective Subtype.val_injective
  have hne : ∀ P : Primes K, (1 : ℂ) - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    fun P => one_sub_absNorm_cpow_ne_zero K hs0 P
  have hg : Summable (fun P : Primes K => -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))) :=
    hsum.clog_one_sub.neg

  have hlim1 : Tendsto (fun T : Finset (Primes K) =>
      ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (cexp (∑' P : Primes K, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))))) := by
    have h1 : Tendsto (fun T : Finset (Primes K) =>
        ∑ P ∈ T, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))) atTop
        (𝓝 (∑' P : Primes K, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)))) := hg.hasSum
    refine ((Complex.continuous_exp.tendsto _).comp h1).congr fun T => ?_
    show cexp (∑ P ∈ T, -log (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s)))
      = ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun P _ => by rw [exp_neg, exp_log (hne P)]

  have hlim2 : Tendsto (fun T : Finset (Primes K) =>
      ∏ P ∈ T, (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) atTop (𝓝 (dedekindZeta K s)) := by
    have h := tendsto_tsum_primeSet_of_summable K
      (f := fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s))
      (summable_norm_absNorm_cpow K hs)
      (by show ((Ideal.absNorm (0 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 0
          rw [map_zero, Nat.cast_zero, Complex.zero_cpow hsz])
    rw [tsum_absNorm_cpow_eq_dedekindZeta K hs] at h
    exact h.congr fun T => tsum_primeSet_eq_prod K hs T

  rw [tendsto_nhds_unique hlim2 hlim1]
  exact Complex.exp_ne_zero _

private theorem hasProd_primes {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : Primes K => (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) (dedekindZeta K s) := by
  have hsz : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hs; linarith
  have h := tendsto_tsum_primeSet_of_summable K
    (f := fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s))
    (summable_norm_absNorm_cpow K hs)
    (by show ((Ideal.absNorm (0 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 0
        rw [map_zero, Nat.cast_zero, Complex.zero_cpow hsz])
  rw [tsum_absNorm_cpow_eq_dedekindZeta K hs] at h
  exact h.congr fun T => tsum_primeSet_eq_prod K hs T

end Zeta
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta"

open IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

private abbrev Pl : Type := HeightOneSpectrum (𝓞 K)

private def nC (v : Pl K) : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

private theorem prime_asIdeal (v : Pl K) : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime

private def plEquiv : Pl K ≃ Zeta.Primes K where
  toFun v := ⟨v.asIdeal, prime_asIdeal K v⟩
  invFun Q := ⟨Q.1, Ideal.isPrime_of_prime Q.2, fun h => Q.2.ne_zero (by rw [Ideal.zero_eq_bot]; exact h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem _root_.Q15PLK.two_le_absNorm (v : Pl K) : 2 ≤ Ideal.absNorm v.asIdeal := Zeta.two_le_absNorm K (plEquiv K v)

p2m_export "Q15PLK" "two_le_absNorm"
private theorem nC_ne_zero (v : Pl K) : nC K v ≠ 0 := by
  have h := two_le_absNorm K v
  unfold nC; exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)

private theorem norm_nC_cpow_neg (v : Pl K) (s : ℂ) : ‖nC K v ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  have h := two_le_absNorm K v
  unfold nC
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]

private theorem norm_nC_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (v : Pl K) : ‖nC K v ^ (-s)‖ < 1 :=
  Zeta.norm_absNorm_cpow_neg_lt_one K hs (plEquiv K v)

private theorem summable_norm_nC_cpow {s : ℂ} (hs : 1 < s.re) : Summable fun v : Pl K => ‖nC K v ^ (-s)‖ := by
  have h := (Zeta.summable_norm_absNorm_cpow K hs).comp_injective
    (show Function.Injective (fun v : Pl K => v.asIdeal) from fun v w h => HeightOneSpectrum.ext h)
  exact h

private theorem hasProd_zeta {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : Pl K => (1 - nC K v ^ (-s))⁻¹) (dedekindZeta K s) :=
  NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K s hs

variable {K}

private theorem summable_twisted {s : ℂ} (hs : 1 < s.re) (c : Pl K → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (T : Finset (Pl K)) : Summable fun v : {v : Pl K // v ∉ T} => c v.1 * nC K v.1 ^ (-s) := by
  have hn : Summable fun v : Pl K => ‖c v * nC K v ^ (-s)‖ := by
    refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) (summable_norm_nC_cpow K hs)
    rw [norm_mul]
    calc ‖c v‖ * ‖nC K v ^ (-s)‖ ≤ 1 * ‖nC K v ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (hc v) (norm_nonneg _)
      _ = ‖nC K v ^ (-s)‖ := one_mul _
  exact (hn.subtype {v | v ∉ T}).of_norm

private theorem one_sub_twisted_ne_zero {s : ℂ} (hs : 0 < s.re) (c : Pl K → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (v : Pl K) :
    (1 : ℂ) - c v * nC K v ^ (-s) ≠ 0 := by
  intro h
  have hlt : ‖c v * nC K v ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖c v‖ * ‖nC K v ^ (-s)‖ ≤ 1 * ‖nC K v ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (hc v) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact norm_nC_cpow_neg_lt_one K hs v
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

private def logSum (T : Finset (Pl K)) (c : Pl K → ℂ) (s : ℂ) : ℂ :=
  ∑' v : {v : Pl K // v ∉ T}, -log (1 - c v.1 * nC K v.1 ^ (-s))

private theorem hasProd_twisted {s : ℂ} (hs : 1 < s.re) (c : Pl K → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (T : Finset (Pl K)) :
    HasProd (fun v : {v : Pl K // v ∉ T} => (1 - c v.1 * nC K v.1 ^ (-s))⁻¹) (cexp (logSum T c s)) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hne : ∀ v : Pl K, (1 : ℂ) - c v * nC K v ^ (-s) ≠ 0 := one_sub_twisted_ne_zero hs0 c hc
  have hg : Summable fun v : {v : Pl K // v ∉ T} => -log (1 - c v.1 * nC K v.1 ^ (-s)) :=
    (summable_twisted hs c hc T).clog_one_sub.neg
  have h1 : Tendsto (fun F : Finset {v : Pl K // v ∉ T} =>
      ∑ v ∈ F, -log (1 - c v.1 * nC K v.1 ^ (-s))) atTop (𝓝 (logSum T c s)) := hg.hasSum
  have h2 := (Complex.continuous_exp.tendsto _).comp h1
  show Tendsto (fun F : Finset {v : Pl K // v ∉ T} => ∏ v ∈ F, (1 - c v.1 * nC K v.1 ^ (-s))⁻¹)
    atTop (𝓝 (cexp (logSum T c s)))
  refine h2.congr fun F => ?_
  show cexp (∑ v ∈ F, -log (1 - c v.1 * nC K v.1 ^ (-s))) = ∏ v ∈ F, (1 - c v.1 * nC K v.1 ^ (-s))⁻¹
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun v _ => by rw [exp_neg, exp_log (hne v.1)]

private theorem tprod_twisted {s : ℂ} (hs : 1 < s.re) (c : Pl K → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (T : Finset (Pl K)) :
    ∏' v : {v : Pl K // v ∉ T}, (1 - c v.1 * nC K v.1 ^ (-s))⁻¹ = cexp (logSum T c s) :=
  (hasProd_twisted hs c hc T).tprod_eq

private theorem exp_logSum_ne_zero (T : Finset (Pl K)) (c : Pl K → ℂ) (s : ℂ) : cexp (logSum T c s) ≠ 0 :=
  Complex.exp_ne_zero _

private theorem exp_logSum_one {s : ℂ} (hs : 1 < s.re) (T : Finset (Pl K)) :
    cexp (logSum T (fun _ => 1) s) = dedekindZeta K s * ∏ v ∈ T, (1 - nC K v ^ (-s)) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs

  have hE : HasProd ((fun v : Pl K => (1 - nC K v ^ (-s))⁻¹) ∘ (↑) :
      ((↑T : Set (Pl K))ᶜ : Set (Pl K)) → ℂ) (cexp (logSum T (fun _ => 1) s)) := by
    have h := hasProd_twisted hs (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) T
    simp only [one_mul] at h
    exact h

  have hG : HasProd ((fun v : Pl K => (1 - nC K v ^ (-s))⁻¹) ∘ (↑) : (↑T : Set (Pl K)) → ℂ)
      (∏ v ∈ T, (1 - nC K v ^ (-s))⁻¹) := Finset.hasProd T _
  have hall := hG.mul_isCompl isCompl_compl hE
  have heq : (∏ v ∈ T, (1 - nC K v ^ (-s))⁻¹) * cexp (logSum T (fun _ => 1) s) = dedekindZeta K s :=
    HasProd.unique hall (hasProd_zeta K hs)
  have hne : (∏ v ∈ T, (1 - nC K v ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ =>
      (by simpa only [one_mul] using one_sub_twisted_ne_zero hs0 (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) v)
  have hinv : (∏ v ∈ T, (1 - nC K v ^ (-s))⁻¹) = (∏ v ∈ T, (1 - nC K v ^ (-s)))⁻¹ :=
    Finset.prod_inv_distrib _
  rw [hinv] at heq
  calc cexp (logSum T (fun _ => 1) s)
      = (∏ v ∈ T, (1 - nC K v ^ (-s))) * ((∏ v ∈ T, (1 - nC K v ^ (-s)))⁻¹ * cexp (logSum T (fun _ => 1) s)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = (∏ v ∈ T, (1 - nC K v ^ (-s))) * dedekindZeta K s := by rw [heq]
    _ = dedekindZeta K s * ∏ v ∈ T, (1 - nC K v ^ (-s)) := mul_comm _ _

private theorem tendsto_norm_dedekindZeta_atTop :
    Tendsto (fun σ : ℝ => ‖dedekindZeta K (σ : ℂ)‖) (𝓝[>] (1 : ℝ)) atTop := by
  have h := (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have hr : 0 < ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (dedekindZeta_residue_pos K)]
    exact dedekindZeta_residue_pos K

  have hinv : Tendsto (fun σ : ℝ => (σ - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop := by
    have h1 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun σ : ℝ => σ - 1) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) := tendsto_id.sub_const 1
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hσ))
    exact tendsto_inv_nhdsGT_zero.comp h1
  have hprod := h.pos_mul_atTop hr hinv

  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : 0 < σ - 1 := sub_pos.mpr (Set.mem_Ioi.mp hσ)
  have hnorm : ‖((σ : ℂ) - 1) * dedekindZeta K (σ : ℂ)‖ = (σ - 1) * ‖dedekindZeta K (σ : ℂ)‖ := by
    rw [norm_mul, show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hσ1]
  show ‖((σ : ℂ) - 1) * dedekindZeta K (σ : ℂ)‖ * (σ - 1)⁻¹ = ‖dedekindZeta K (σ : ℂ)‖
  rw [hnorm, mul_comm (σ - 1), mul_assoc, mul_inv_cancel₀ hσ1.ne', mul_one]

private theorem tendsto_norm_exp_logSum_one_atTop (T : Finset (Pl K)) :
    Tendsto (fun σ : ℝ => ‖cexp (logSum T (fun _ => 1) (σ : ℂ))‖) (𝓝[>] (1 : ℝ)) atTop := by

  have hcont : ∀ v : Pl K, ContinuousAt (fun σ : ℝ => (1 : ℂ) - nC K v ^ (-(σ : ℂ))) 1 := by
    intro v
    refine continuousAt_const.sub ?_
    refine ContinuousAt.const_cpow (continuous_ofReal.continuousAt.neg) (Or.inl (nC_ne_zero K v))
  have hfin : Tendsto (fun σ : ℝ => ‖∏ v ∈ T, ((1 : ℂ) - nC K v ^ (-(σ : ℂ)))‖) (𝓝[>] (1 : ℝ))
      (𝓝 ‖∏ v ∈ T, ((1 : ℂ) - nC K v ^ (-((1 : ℝ) : ℂ)))‖) :=
    (tendsto_finsetProd T fun v _ => hcont v).norm.mono_left nhdsWithin_le_nhds
  have hpos : 0 < ‖∏ v ∈ T, ((1 : ℂ) - nC K v ^ (-((1 : ℝ) : ℂ)))‖ := by
    rw [norm_pos_iff]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => by
      simpa only [one_mul] using one_sub_twisted_ne_zero (s := ((1 : ℝ) : ℂ))
        (by rw [Complex.ofReal_re]; exact zero_lt_one) (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) v
  have hmul := (tendsto_norm_dedekindZeta_atTop (K := K)).atTop_mul_pos hpos hfin
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ : 1 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact Set.mem_Ioi.mp hσ
  rw [exp_logSum_one hσ T, norm_mul]

end Q15PLK
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

open NumberField IsDedekindDomain AutomorphicForm Polynomial
open NumberField.TateGlobal LanglandsTunnell.Converse
namespace Q15PLK

variable (K : Type) [Field K] [NumberField K]

private theorem eisensteinTableOf_comm (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    eisensteinTableOf K N hN μ₁ μ₂ = eisensteinTableOf K N hN μ₂ μ₁ := by
  unfold eisensteinTableOf
  congr 1
  · funext v
    exact add_comm _ _
  · funext v
    exact mul_comm _ _

private theorem twistFactor_split (c m₁ m₂ : ℂ) :
    (C 1 - C (c * (m₁ + m₂)) * X + C (c ^ 2 * (m₁ * m₂)) * X ^ 2 : ℂ[X])
      = (C 1 - C (c * m₁) * X) * (C 1 - C (c * m₂) * X) := by
  simp only [map_one, map_mul, map_add, map_pow]
  ring

private theorem coe_unit_sq (u : ℂˣ) : ((u ^ 2 : ℂˣ) : ℂ) = ((u : ℂˣ) : ℂ) ^ 2 := by
  simp

private theorem twistFactor_eq_of_eisenstein (Pi : HeckeEigensystem K ℂ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (μ₁ μ₂ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (ha : Pi.a v = (eisensteinTableOf K N hN μ₁ μ₂).a v) (hb : Pi.b v = (eisensteinTableOf K N hN μ₁ μ₂).b v) :
    (C 1 - C (((χ (uniformizerIdele K v) : ℂˣ) : ℂ) * Pi.a v) * X
        + C ((((χ (uniformizerIdele K v)) ^ 2 : ℂˣ) : ℂ) * Pi.b v) * X ^ 2 : ℂ[X])
      = (C 1 - C (((χ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ)) * X)
        * (C 1 - C (((χ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ)) * X) := by
  rw [ha, hb, coe_unit_sq]
  exact twistFactor_split _ _ _

end Q15PLK
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

namespace Q15PLK

private theorem hasProd_compl_of_hasProd_compl_union {ι : Type} [DecidableEq ι] (f : ι → ℂ) (S S₁ : Finset ι) (E : ℂ)
    (hE : HasProd (fun v : {v : ι // v ∉ S ∪ S₁} => f v) E) :
    HasProd (fun v : {v : ι // v ∉ S} => f v) ((∏ v ∈ S₁ \ S, f v) * E) := by
  have hE' : HasProd (({v : ι | v ∉ S ∪ S₁} : Set ι).mulIndicator f) E :=
    (hasProd_subtype_iff_mulIndicator (s := {v : ι | v ∉ S ∪ S₁})).1 hE
  have h1 : ∀ b ∉ S₁ \ S, (↑(S₁ \ S) : Set ι).mulIndicator f b = 1 := fun b hb =>
    Set.mulIndicator_of_notMem (by simpa using hb) f
  have h2 : ∏ b ∈ S₁ \ S, (↑(S₁ \ S) : Set ι).mulIndicator f b = ∏ b ∈ S₁ \ S, f b :=
    Finset.prod_congr rfl fun b hb => Set.mulIndicator_of_mem (by simpa using hb) f
  have hG : HasProd ((↑(S₁ \ S) : Set ι).mulIndicator f) (∏ v ∈ S₁ \ S, f v) := by
    have h : HasProd ((↑(S₁ \ S) : Set ι).mulIndicator f)
        (∏ b ∈ S₁ \ S, (↑(S₁ \ S) : Set ι).mulIndicator f b) := hasProd_prod_of_ne_finset_one h1
    rwa [h2] at h
  have hdisj : Disjoint (↑(S₁ \ S) : Set ι) {v : ι | v ∉ S ∪ S₁} := by
    rw [Set.disjoint_left]
    intro v hv hv'
    simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hv
    exact hv' (Finset.mem_union_right S hv.1)
  have hunion : (↑(S₁ \ S) : Set ι) ∪ {v : ι | v ∉ S ∪ S₁} = {v : ι | v ∉ S} := by
    ext v
    simp only [Set.mem_union, Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe, Set.mem_setOf_eq, Finset.mem_union,
      not_or]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · exact h
    · intro h
      by_cases h₁ : v ∈ S₁
      · exact Or.inl ⟨h₁, h⟩
      · exact Or.inr ⟨h, h₁⟩
  have hmul := hG.mul hE'
  rw [← Set.mulIndicator_union_of_disjoint hdisj f, hunion] at hmul
  exact (hasProd_subtype_iff_mulIndicator (s := {v : ι | v ∉ S})).2 hmul

end Q15PLK
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal Complex
namespace Q15PLK

variable (K : Type) [Field K] [NumberField K]

private noncomputable def normRealPowChar (σ : ℝ) : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ where
  toFun x := Units.mk0 ((ideleNorm K x ^ σ : ℝ) : ℂ)
    (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (ideleNorm_pos x) σ).ne')
  map_one' := Units.ext (by
    rw [Units.val_mk0, ideleNorm_one, Real.one_rpow, ofReal_one, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, ideleNorm_mul,
      Real.mul_rpow (ideleNorm_pos x).le (ideleNorm_pos y).le, ofReal_mul])

private theorem coe_normRealPowChar_apply (σ : ℝ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((normRealPowChar K σ x : ℂˣ) : ℂ) = ((ideleNorm K x ^ σ : ℝ) : ℂ) := rfl

private theorem coe_normRealPowChar_ne_zero (σ : ℝ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((normRealPowChar K σ x : ℂˣ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (ideleNorm_pos x) σ).ne'

private theorem continuous_normRealPowChar (σ : ℝ) : Continuous (normRealPowChar K σ) := by
  have h1 : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((ideleNorm K x ^ σ : ℝ) : ℂ) :=
    continuous_ofReal.comp ((continuous_ideleNorm K).rpow_const fun x => Or.inl (ideleNorm_pos x).ne')
  rw [Units.continuous_iff]
  refine ⟨h1, ?_⟩
  simp only [Units.val_inv_eq_inv_val, coe_normRealPowChar_apply]
  exact h1.inv₀ fun x => ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (ideleNorm_pos x) σ).ne'

private theorem absNorm_pos_real (v : HeightOneSpectrum (𝓞 K)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h := ideleNorm_pos (uniformizerIdele K v)
  rw [ideleNorm_uniformizerIdele K v] at h
  exact inv_pos.mp h

private theorem exists_unitaryPart (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ)
    (hc : Continuous μ)
    (hpf : ∀ u : Kˣ, ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) = 1) :
    ∃ (σ : ℝ) (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K ν ∧ Continuous ν ∧
      IsUnitaryChar (𝓞 K) K ν ∧ ∀ v : HeightOneSpectrum (𝓞 K),
        ((μ (uniformizerIdele K v) : ℂˣ) : ℂ)
          = ((ν (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)) := by
  obtain ⟨σ, hσ⟩ := exists_norm_apply_eq_ideleNorm_rpow K μ hμ hc
  refine ⟨σ, μ * (normRealPowChar K σ)⁻¹, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ u, one_mul, inv_eq_one]
    exact Units.ext (by rw [coe_normRealPowChar_apply, hpf u, Real.one_rpow, ofReal_one, Units.val_one])
  · have hfun : (⇑(μ * (normRealPowChar K σ)⁻¹) : (AdeleRing (𝓞 K) K)ˣ → ℂˣ)
        = fun x => μ x * (normRealPowChar K σ x)⁻¹ := rfl
    rw [hfun]
    exact hc.mul (continuous_normRealPowChar K σ).inv
  · intro x
    have hpos : (0 : ℝ) < ideleNorm K x ^ σ := Real.rpow_pos_of_pos (ideleNorm_pos x) σ
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, norm_mul, hσ x, Units.val_inv_eq_inv_val,
      norm_inv, coe_normRealPowChar_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
      mul_inv_cancel₀ hpos.ne']
  · intro v
    have hN := absNorm_pos_real K v
    have hne : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)) ≠ 0 := fun h =>
      (by exact_mod_cast hN.ne' : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0) ((cpow_eq_zero_iff _ _).mp h).1
    have key : ((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ σ : ℝ) : ℂ))⁻¹
        * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)) = 1 := by
      rw [Real.inv_rpow hN.le, ← Real.rpow_neg hN.le, ofReal_cpow hN.le, ofReal_neg, ofReal_natCast]
      exact inv_mul_cancel₀ hne
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      coe_normRealPowChar_apply, ideleNorm_uniformizerIdele K v, mul_assoc, key, mul_one]

end Q15PLK
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
namespace Q15PLK

variable (K : Type) [Field K] [NumberField K]

private theorem ideleNorm_principal (u : Kˣ) : ideleNorm K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) = 1 := by
  have h := ideleNorm_det_globalPoints (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
  unfold globalPoints at h
  rw [Matrix.GeneralLinearGroup.map_det, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow,
    pow_two, ideleNorm_mul] at h
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · exact absurd h1 (ne_of_gt (lt_trans (by norm_num) (ideleNorm_pos _)))

end Q15PLK
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

namespace Q15PLK

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

private theorem norm_nC_cpow_neg_le_half {w : ℂ} (hw : 1 ≤ w.re) (v : Pl K) : ‖nC K v ^ (-w)‖ ≤ 1 / 2 := by
  rw [norm_nC_cpow_neg]
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm K v
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := le_trans one_le_two h2
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-w.re) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ (2 : ℝ)⁻¹ := by
        rw [inv_le_inv₀ (lt_of_lt_of_le two_pos h2) two_pos]; exact h2
    _ = 1 / 2 := by norm_num

private theorem norm_logTerm_le {w : ℂ} (hw : 1 ≤ w.re) (c : Pl K → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (v : Pl K) :
    ‖-log (1 - c v * nC K v ^ (-w))‖ ≤ (3 / 2) * ‖nC K v ^ (-w)‖ := by
  have hz : ‖c v * nC K v ^ (-w)‖ ≤ ‖nC K v ^ (-w)‖ := by
    rw [norm_mul]
    calc ‖c v‖ * ‖nC K v ^ (-w)‖ ≤ 1 * ‖nC K v ^ (-w)‖ :=
          mul_le_mul_of_nonneg_right (hc v) (norm_nonneg _)
      _ = ‖nC K v ^ (-w)‖ := one_mul _
  have hhalf : ‖-(c v * nC K v ^ (-w))‖ ≤ 1 / 2 := by
    rw [norm_neg]; exact le_trans hz (norm_nC_cpow_neg_le_half hw v)
  rw [norm_neg, sub_eq_add_neg]
  calc ‖log (1 + -(c v * nC K v ^ (-w)))‖ ≤ (3 / 2) * ‖-(c v * nC K v ^ (-w))‖ :=
        Complex.norm_log_one_add_half_le_self hhalf
    _ ≤ (3 / 2) * ‖nC K v ^ (-w)‖ := by
        rw [norm_neg]; exact mul_le_mul_of_nonneg_left hz (by norm_num)

private theorem differentiableAt_logTerm {w : ℂ} (hw : 1 ≤ w.re) (c : Pl K → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (v : Pl K) :
    DifferentiableAt ℂ (fun s : ℂ => -log (1 - c v * nC K v ^ (-s))) w := by
  have hlt : ‖-(c v * nC K v ^ (-w))‖ < 1 := by
    rw [norm_neg, norm_mul]
    calc ‖c v‖ * ‖nC K v ^ (-w)‖ ≤ 1 * ‖nC K v ^ (-w)‖ :=
          mul_le_mul_of_nonneg_right (hc v) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact norm_nC_cpow_neg_lt_one K (by linarith) v
  have hmem : (1 : ℂ) - c v * nC K v ^ (-w) ∈ Complex.slitPlane := by
    rw [sub_eq_add_neg]; exact Complex.mem_slitPlane_of_norm_lt_one hlt
  have hpow : DifferentiableAt ℂ (fun s : ℂ => nC K v ^ (-s)) w :=
    differentiableAt_id.neg.const_cpow (Or.inl (nC_ne_zero K v))
  exact (((hpow.const_mul (c v)).const_sub (1 : ℂ)).clog hmem).neg

private theorem differentiableOn_logSum (T : Finset (Pl K)) (c : Pl K → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) :
    DifferentiableOn ℂ (logSum T c) {s : ℂ | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀

  set η : ℝ := (s₀.re - 1) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hU : IsOpen {s : ℂ | 1 + η < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmemU : s₀ ∈ {s : ℂ | 1 + η < s.re} := by show 1 + η < s₀.re; rw [hη]; linarith
  have hre : 1 < ((((1 + η : ℝ)) : ℂ)).re := by rw [Complex.ofReal_re]; linarith
  have hsum : Summable fun v : {v : Pl K // v ∉ T} => (3 / 2) * ‖nC K v.1 ^ (-(((1 + η : ℝ)) : ℂ))‖ :=
    ((summable_norm_nC_cpow K hre).subtype {v | v ∉ T}).mul_left (3 / 2)
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => ∑' v : {v : Pl K // v ∉ T}, -log (1 - c v.1 * nC K v.1 ^ (-s)))
      {s : ℂ | 1 + η < s.re} := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun v s hs => ?_) hU (fun v s hs => ?_)
    · exact (differentiableAt_logTerm
        (by show (1 : ℝ) ≤ s.re; exact le_of_lt (by linarith [show 1 + η < s.re from hs]))
        c hc v.1).differentiableWithinAt
    · have hs1 : 1 ≤ s.re := le_of_lt (by linarith [show 1 + η < s.re from hs])
      refine le_trans (norm_logTerm_le hs1 c hc v.1) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      rw [norm_nC_cpow_neg, norm_nC_cpow_neg, Complex.ofReal_re]
      have h1 : (1 : ℝ) ≤ (Ideal.absNorm v.1.asIdeal : ℝ) :=
        le_trans one_le_two (by exact_mod_cast two_le_absNorm K v.1)
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith [show 1 + η < s.re from hs])
  exact ((hdiff s₀ hmemU).differentiableAt (hU.mem_nhds hmemU)).differentiableWithinAt

end Q15PLK
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

open NumberField IsDedekindDomain AutomorphicForm Polynomial
open NumberField.TateGlobal LanglandsTunnell.Converse

namespace Q15PLK

variable (K : Type) [Field K] [NumberField K]

private theorem isIdeleClassChar_inv (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (h : IsIdeleClassChar (𝓞 K) K μ) :
    IsIdeleClassChar (𝓞 K) K μ⁻¹ := by
  intro u
  rw [MonoidHom.inv_apply, h u, inv_one]

private theorem isIdeleClassChar_mul (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsIdeleClassChar (𝓞 K) K μ)
    (hν : IsIdeleClassChar (𝓞 K) K ν) : IsIdeleClassChar (𝓞 K) K (μ * ν) := by
  intro u
  rw [MonoidHom.mul_apply, hμ u, hν u, one_mul]

private theorem continuous_inv_char (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (h : Continuous μ) :
    Continuous (μ⁻¹ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := by
  have hfun : ⇑(μ⁻¹ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) = fun x => (μ x)⁻¹ :=
    funext fun x => MonoidHom.inv_apply μ x
  rw [hfun]
  exact h.inv

private theorem continuous_mul_char (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) (hν : Continuous ν) :
    Continuous (μ * ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := by
  have hfun : ⇑(μ * ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) = fun x => μ x * ν x :=
    funext fun x => MonoidHom.mul_apply μ ν x
  rw [hfun]
  exact hμ.mul hν

private theorem isUnitaryChar_inv (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (h : IsUnitaryChar (𝓞 K) K μ) :
    IsUnitaryChar (𝓞 K) K μ⁻¹ := by
  intro x
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]

private theorem isUnitaryChar_mul (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ)
    (hν : IsUnitaryChar (𝓞 K) K ν) : IsUnitaryChar (𝓞 K) K (μ * ν) := by
  intro x
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ x, hν x, one_mul]

private theorem absNorm_cast_ne_zero (v : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  rw [Ne, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

private theorem hentFactor_eq (Pi : HeckeEigensystem K ℂ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (μ₁ μ₂ ν₁ ν₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (σ₁ σ₂ : ℝ) (v : HeightOneSpectrum (𝓞 K))
    (ha : Pi.a v = (eisensteinTableOf K N hN μ₁ μ₂).a v) (hb : Pi.b v = (eisensteinTableOf K N hN μ₁ μ₂).b v)
    (hp₁ : ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ)
      = ((ν₁ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₁ : ℂ)))
    (hp₂ : ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ)
      = ((ν₂ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₂ : ℂ)))
    (s : ℂ) :
    (C 1 - C (((ν₁⁻¹ (uniformizerIdele K v) : ℂˣ) : ℂ) * Pi.a v) * X
        + C ((((ν₁⁻¹ (uniformizerIdele K v)) ^ 2 : ℂˣ) : ℂ) * Pi.b v) * X ^ 2 : ℂ[X]).eval
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
      = (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + σ₁)))
        * (1 - (((ν₁⁻¹ * ν₂) (uniformizerIdele K v) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + σ₂))) := by
  have hNv := absNorm_cast_ne_zero K v
  have hν₁ : ((ν₁ (uniformizerIdele K v) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [twistFactor_eq_of_eisenstein K Pi N hN μ₁ μ₂ ν₁⁻¹ v ha hb]
  simp only [eval_mul, eval_sub, eval_C, eval_X]
  rw [MonoidHom.mul_apply, Units.val_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hp₁, hp₂]
  simp only [neg_add]
  rw [Complex.cpow_add _ _ hNv, Complex.cpow_add _ _ hNv]
  field_simp

private theorem hentGatedFactor_eq (Pi : HeckeEigensystem K ℂ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (μ₁ μ₂ ν₁ ν₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (σ₁ σ₂ : ℝ) (v : HeightOneSpectrum (𝓞 K))
    (hur : IsUnramifiedCharAt ν₁⁻¹ v)
    (ha : Pi.a v = (eisensteinTableOf K N hN μ₁ μ₂).a v) (hb : Pi.b v = (eisensteinTableOf K N hN μ₁ μ₂).b v)
    (hp₁ : ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ)
      = ((ν₁ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₁ : ℂ)))
    (hp₂ : ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ)
      = ((ν₂ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₂ : ℂ)))
    (s : ℂ) :
    ((if IsUnramifiedCharAt ν₁⁻¹ v
      then C 1 - C (((ν₁⁻¹ (uniformizerIdele K v) : ℂˣ) : ℂ) * Pi.a v) * X
        + C ((((ν₁⁻¹ (uniformizerIdele K v)) ^ 2 : ℂˣ) : ℂ) * Pi.b v) * X ^ 2
      else C 1 : ℂ[X]).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))
      = (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + σ₁)))
        * (1 - (((ν₁⁻¹ * ν₂) (uniformizerIdele K v) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + σ₂))) := by
  rw [if_pos hur]
  exact hentFactor_eq K Pi N hN μ₁ μ₂ ν₁ ν₂ σ₁ σ₂ v ha hb hp₁ hp₂ s

end Q15PLK
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

namespace Q15PLK

open IsDedekindDomain NumberField Filter Topology Polynomial
open AutomorphicForm NumberField.TateGlobal LanglandsTunnell.Converse

variable {K : Type} [Field K] [NumberField K]

private theorem tendsto_nC_cpow_neg_comap_re (v : Pl K) :
    Tendsto (fun s : ℂ => nC K v ^ (-s)) (comap Complex.re atTop) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hre : Tendsto (fun s : ℂ => s.re) (comap Complex.re atTop) atTop := tendsto_comap
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have h2 := two_le_absNorm K v
    exact_mod_cast (lt_of_lt_of_le one_lt_two h2)
  have hlog : 0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) := Real.log_pos hN
  have h1 : Tendsto (fun s : ℂ => -s.re * Real.log (Ideal.absNorm v.asIdeal : ℝ))
      (comap Complex.re atTop) atBot :=
    (tendsto_neg_atTop_atBot.comp hre).atBot_mul_const hlog
  refine (Real.tendsto_exp_atBot.comp h1).congr' (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_def, norm_nC_cpow_neg]
  rw [Real.rpow_def_of_pos (by linarith), mul_comm]

private noncomputable def gatedPoly (Pi : HeckeEigensystem K ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : Pl K) : ℂ[X] :=
  if IsUnramifiedCharAt χ v
    then C 1 - C (((χ (uniformizerIdele K v) : ℂˣ) : ℂ) * Pi.a v) * X
      + C ((((χ (uniformizerIdele K v)) ^ 2 : ℂˣ) : ℂ) * Pi.b v) * X ^ 2
    else C 1

private theorem gatedPoly_eval_zero (Pi : HeckeEigensystem K ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : Pl K) :
    (gatedPoly Pi χ v).eval 0 = 1 := by
  unfold gatedPoly
  split_ifs <;> simp

private theorem eventually_gatedPoly_eval_ne_zero (Pi : HeckeEigensystem K ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : Pl K) :
    ∀ᶠ s : ℂ in comap Complex.re atTop, (gatedPoly Pi χ v).eval (nC K v ^ (-s)) ≠ 0 := by
  have h : Tendsto (fun s : ℂ => (gatedPoly Pi χ v).eval (nC K v ^ (-s))) (comap Complex.re atTop)
      (𝓝 ((gatedPoly Pi χ v).eval 0)) :=
    ((gatedPoly Pi χ v).continuous.tendsto 0).comp (tendsto_nC_cpow_neg_comap_re v)
  rw [gatedPoly_eval_zero] at h
  exact h.eventually_ne one_ne_zero

private theorem differentiable_gatedPoly_eval (Pi : HeckeEigensystem K ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : Pl K) : Differentiable ℂ (fun s : ℂ => (gatedPoly Pi χ v).eval (nC K v ^ (-s))) :=
  (gatedPoly Pi χ v).differentiable.comp (differentiable_id.neg.const_cpow (Or.inl (nC_ne_zero K v)))

private theorem exists_forall_re_gt_of_eventually {p : ℂ → Prop} (h : ∀ᶠ s : ℂ in comap Complex.re atTop, p s) :
    ∃ R : ℝ, ∀ s : ℂ, R < s.re → p s := by
  obtain ⟨t, ht, hsub⟩ := Filter.mem_comap.1 h
  obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.1 ht
  exact ⟨R, fun s hs => hsub (hR s.re (le_of_lt hs))⟩

private theorem not_tendsto_exp_logSum_shift (T : Finset (Pl K)) (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hνK : IsIdeleClassChar (𝓞 K) K ν) (hνc : Continuous ν) (hνu : IsUnitaryChar (𝓞 K) K ν)
    (hT : ∀ v : Pl K, v ∉ T → IsUnramifiedCharAt ν v) (δ : ℝ) (hδ : 0 ≤ δ) :
    ¬ Tendsto (fun σ : ℝ => cexp (logSum T (fun v => ((ν (uniformizerIdele K v) : ℂˣ) : ℂ)) ((σ : ℂ) + δ)))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  set cν : Pl K → ℂ := fun v => ((ν (uniformizerIdele K v) : ℂˣ) : ℂ) with hcν
  have hcν1 : ∀ v, ‖cν v‖ ≤ 1 := fun v => le_of_eq (hνu _)
  rcases hδ.lt_or_eq with hpos | hzero
  ·
    intro htend
    have hcont : ContinuousAt (fun σ : ℝ => cexp (logSum T cν ((σ : ℂ) + δ))) 1 := by
      have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have hmem : ((1 : ℝ) : ℂ) + δ ∈ {s : ℂ | 1 < s.re} := by
        show 1 < (((1 : ℝ) : ℂ) + δ).re
        simp only [Complex.add_re, Complex.ofReal_re]; linarith
      have hd : DifferentiableAt ℂ (logSum T cν) (((1 : ℝ) : ℂ) + δ) :=
        (differentiableOn_logSum T cν hcν1 _ hmem).differentiableAt (hU.mem_nhds hmem)
      have hc1 : ContinuousAt (logSum T cν) (((1 : ℝ) : ℂ) + δ) := hd.continuousAt
      have hpath : Continuous (fun σ : ℝ => (σ : ℂ) + δ) := Complex.continuous_ofReal.add continuous_const
      have hin : ContinuousAt (logSum T cν ∘ fun σ : ℝ => (σ : ℂ) + δ) 1 :=
        ContinuousAt.comp_of_eq (g := logSum T cν) (f := fun σ : ℝ => (σ : ℂ) + δ) hc1 hpath.continuousAt rfl
      have hcomp : ContinuousAt (cexp ∘ (logSum T cν ∘ fun σ : ℝ => (σ : ℂ) + δ)) 1 :=
        ContinuousAt.comp (g := cexp) Complex.continuous_exp.continuousAt hin
      exact hcomp
    have hlim : Tendsto (fun σ : ℝ => cexp (logSum T cν ((σ : ℂ) + δ))) (𝓝[>] (1 : ℝ))
        (𝓝 (cexp (logSum T cν (((1 : ℝ) : ℂ) + δ)))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hne : cexp (logSum T cν (((1 : ℝ) : ℂ) + δ)) ≠ 0 := exp_logSum_ne_zero T cν _
    exact hne (tendsto_nhds_unique hlim htend)
  ·
    subst hzero
    intro htend
    apply NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar K ν hνK hνc hνu T
    refine htend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1 : ℝ) < σ := hσ
    have hre : 1 < ((σ : ℂ)).re := by rw [Complex.ofReal_re]; exact hσ1
    simp only [Complex.ofReal_zero, add_zero]
    rw [← tprod_twisted hre cν hcν1 T]
    refine tprod_congr fun v => ?_
    rw [if_pos (hT v.1 v.2)]
    rfl

set_option maxHeartbeats 6400000 in

private theorem core (Pi : HeckeEigensystem K ℂ)
    (hent : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
      IsUnitaryChar (𝓞 K) K χ →
      ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
        Differentiable ℂ Λ ∧
        ∀ s : ℂ, σ₀ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            ((if IsUnramifiedCharAt χ v.1
              then C 1 - C (((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
                + C ((((χ (uniformizerIdele K v.1)) ^ 2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
              else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s))
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (μ₁ μ₂ ν₁ ν₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (σ₁ σ₂ : ℝ) (h12 : σ₁ ≤ σ₂)
    (hν₁K : IsIdeleClassChar (𝓞 K) K ν₁) (hν₁c : Continuous ν₁) (hν₁u : IsUnitaryChar (𝓞 K) K ν₁)
    (hμ₁ : ∀ v : HeightOneSpectrum (𝓞 K), ((μ₁ (uniformizerIdele K v) : ℂˣ) : ℂ)
      = ((ν₁ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₁ : ℂ)))
    (hν₂K : IsIdeleClassChar (𝓞 K) K ν₂) (hν₂c : Continuous ν₂) (hν₂u : IsUnitaryChar (𝓞 K) K ν₂)
    (hμ₂ : ∀ v : HeightOneSpectrum (𝓞 K), ((μ₂ (uniformizerIdele K v) : ℂˣ) : ℂ)
      = ((ν₂ (uniformizerIdele K v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₂ : ℂ)))
    (hA : Pi.AgreesAwayFromFinite (eisensteinTableOf K N hN μ₁ μ₂)) : False := by
  obtain ⟨SA, hSA⟩ := hA

  have hχK : IsIdeleClassChar (𝓞 K) K ν₁⁻¹ := isIdeleClassChar_inv K ν₁ hν₁K
  have hχc : Continuous (ν₁⁻¹ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := continuous_inv_char K ν₁ hν₁c
  have hχu : IsUnitaryChar (𝓞 K) K ν₁⁻¹ := isUnitaryChar_inv K ν₁ hν₁u
  have hνK : IsIdeleClassChar (𝓞 K) K (ν₁⁻¹ * ν₂) := isIdeleClassChar_mul K ν₁⁻¹ ν₂ hχK hν₂K
  have hνc : Continuous (ν₁⁻¹ * ν₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := continuous_mul_char K ν₁⁻¹ ν₂ hχc hν₂c
  have hνu : IsUnitaryChar (𝓞 K) K (ν₁⁻¹ * ν₂) := isUnitaryChar_mul K ν₁⁻¹ ν₂ hχu hν₂u
  obtain ⟨S₁, σ₀, Λ, hΛ, hprod⟩ := hent ν₁⁻¹ hχK hχc hχu
  obtain ⟨Sχ, hSχ⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous K ν₁⁻¹ hχc
  obtain ⟨Sν, hSν⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous K (ν₁⁻¹ * ν₂) hνc

  set T : Finset (Pl K) := SA ∪ Sχ ∪ Sν with hTdef
  set cν : Pl K → ℂ := fun v => (((ν₁⁻¹ * ν₂) (uniformizerIdele K v) : ℂˣ) : ℂ) with hcνdef
  have hcν : ∀ v, ‖cν v‖ ≤ 1 := fun v => le_of_eq (hνu _)
  set f : ℂ → Pl K → ℂ := fun s v => ((gatedPoly Pi ν₁⁻¹ v).eval (nC K v ^ (-s)))⁻¹ with hfdef
  set g : ℂ → Pl K → ℂ := fun s v =>
    (1 - (fun _ : Pl K => (1 : ℂ)) v * nC K v ^ (-(s + σ₁)))⁻¹ * (1 - cν v * nC K v ^ (-(s + σ₂)))⁻¹ with hgdef
  have hfg : ∀ s : ℂ, ∀ v : Pl K, v ∉ S₁ ∪ T → f s v = g s v := by
    intro s v hv
    have hvT : v ∉ T := fun h => hv (Finset.mem_union_right _ h)
    have hvA : v ∉ SA := fun h => hvT (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hvχ : v ∉ Sχ := fun h => hvT (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    obtain ⟨ha, hb⟩ := hSA v hvA
    have h := hentGatedFactor_eq K Pi N hN μ₁ μ₂ ν₁ ν₂ σ₁ σ₂ v (hSχ v hvχ) ha hb (hμ₁ v) (hμ₂ v) s
    simp only [hfdef, hgdef, hcνdef, gatedPoly, nC, one_mul]
    rw [h, mul_inv]
  set E : ℂ → ℂ := fun s =>
    cexp (logSum (S₁ ∪ T) (fun _ => (1 : ℂ)) (s + σ₁)) * cexp (logSum (S₁ ∪ T) cν (s + σ₂)) with hEdef
  have hEprod : ∀ s : ℂ, 1 - σ₁ < s.re → HasProd (fun v : {v : Pl K // v ∉ S₁ ∪ T} => g s v.1) (E s) := by
    intro s hs
    have h1 : 1 < (s + σ₁).re := by rw [Complex.add_re, Complex.ofReal_re]; linarith
    have h2 : 1 < (s + σ₂).re := by rw [Complex.add_re, Complex.ofReal_re]; linarith
    exact (hasProd_twisted h1 (fun _ => (1 : ℂ)) (fun _ => by simp) (S₁ ∪ T)).mul
      (hasProd_twisted h2 cν hcν (S₁ ∪ T))

  set P : ℂ → ℂ := fun s => ∏ v ∈ T \ S₁, (gatedPoly Pi ν₁⁻¹ v).eval (nC K v ^ (-s)) with hPdef
  have hPdiff : Differentiable ℂ P := by
    simp only [hPdef]
    exact Differentiable.fun_finsetProd fun v _ => differentiable_gatedPoly_eval Pi ν₁⁻¹ v

  have hev : ∀ᶠ s : ℂ in comap Complex.re atTop,
      ∀ v ∈ T \ S₁, (gatedPoly Pi ν₁⁻¹ v).eval (nC K v ^ (-s)) ≠ 0 :=
    (eventually_all_finset (T \ S₁)).2 fun v _ => eventually_gatedPoly_eval_ne_zero Pi ν₁⁻¹ v
  obtain ⟨R₀, hR₀⟩ := exists_forall_re_gt_of_eventually hev
  set R : ℝ := max R₀ (max σ₀ (1 - σ₁)) with hRdef

  have hfar : ∀ s : ℂ, R < s.re → E s = P s * Λ s := by
    intro s hs
    have hsR₀ : R₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₀ : σ₀ < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
    have hs₁ : 1 - σ₁ < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
    have hL : HasProd (fun v : {v : Pl K // v ∉ S₁} => f s v.1) (Λ s) := hprod s hs₀
    have hE' : HasProd (fun v : {v : Pl K // v ∉ S₁ ∪ T} => f s v.1) (E s) := by
      have hfun : (fun v : {v : Pl K // v ∉ S₁ ∪ T} => f s v.1) = fun v => g s v.1 :=
        funext fun v => hfg s v.1 v.2
      rw [hfun]; exact hEprod s hs₁
    have hL' : HasProd (fun v : {v : Pl K // v ∉ S₁} => f s v.1) ((∏ v ∈ T \ S₁, f s v) * E s) :=
      hasProd_compl_of_hasProd_compl_union (f s) S₁ T (E s) hE'
    have hΛeq : Λ s = (∏ v ∈ T \ S₁, f s v) * E s := hL.unique hL'
    have hPf : P s * ∏ v ∈ T \ S₁, f s v = 1 := by
      simp only [hPdef, hfdef]
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun v hv => mul_inv_cancel₀ (hR₀ s hsR₀ v hv)
    calc E s = (P s * ∏ v ∈ T \ S₁, f s v) * E s := by rw [hPf, one_mul]
      _ = P s * ((∏ v ∈ T \ S₁, f s v) * E s) := by ring
      _ = P s * Λ s := by rw [← hΛeq]

  set U : Set ℂ := {s : ℂ | 1 - σ₁ < s.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt (1 - σ₁)).isPreconnected
  have hEdiff : DifferentiableOn ℂ E U := by
    have hshift : ∀ τ : ℝ, σ₁ ≤ τ →
        DifferentiableOn ℂ (fun s : ℂ => s + (τ : ℂ)) U ∧
          Set.MapsTo (fun s : ℂ => s + (τ : ℂ)) U {s : ℂ | 1 < s.re} := by
      intro τ hτ
      refine ⟨(differentiable_id.add_const _).differentiableOn, fun s hs => ?_⟩
      show 1 < (s + (τ : ℂ)).re
      have hs' : 1 - σ₁ < s.re := hs
      rw [Complex.add_re, Complex.ofReal_re]; linarith
    have h1 : DifferentiableOn ℂ (fun s : ℂ => cexp (logSum (S₁ ∪ T) (fun _ => (1 : ℂ)) (s + σ₁))) U := by
      obtain ⟨hd, hm⟩ := hshift σ₁ le_rfl
      exact ((differentiableOn_logSum (S₁ ∪ T) (fun _ => (1 : ℂ)) (fun _ => by simp)).comp hd hm).cexp
    have h2 : DifferentiableOn ℂ (fun s : ℂ => cexp (logSum (S₁ ∪ T) cν (s + σ₂))) U := by
      obtain ⟨hd, hm⟩ := hshift σ₂ h12
      exact ((differentiableOn_logSum (S₁ ∪ T) cν hcν).comp hd hm).cexp
    exact h1.mul h2
  have hPΛdiff : DifferentiableOn ℂ (fun s => P s * Λ s) U := (hPdiff.mul hΛ).differentiableOn
  have hEqU : Set.EqOn E (fun s => P s * Λ s) U := by
    have hz₀ : ((R + 1 : ℝ) : ℂ) ∈ U := by
      show 1 - σ₁ < (((R + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      have : 1 - σ₁ ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
      linarith
    have hnhds : {s : ℂ | R < s.re} ∈ 𝓝 ((R + 1 : ℝ) : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      show R < (((R + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]; linarith
    exact (hEdiff.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq (hPΛdiff.analyticOnNhd hUopen)
      hUconn hz₀ (Filter.eventually_of_mem hnhds fun s hs => hfar s hs)

  set path : ℝ → ℂ := fun σ => ((σ - σ₁ : ℝ) : ℂ) with hpathdef
  have hpathU : ∀ σ : ℝ, 1 < σ → path σ ∈ U := by
    intro σ hσ
    show 1 - σ₁ < (((σ - σ₁ : ℝ) : ℂ)).re
    rw [Complex.ofReal_re]; linarith
  have hpath_cont : Continuous path := Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)
  have hpath1 : path 1 = ((1 - σ₁ : ℝ) : ℂ) := rfl

  have hEpath : Tendsto (fun σ : ℝ => E (path σ)) (𝓝[>] (1 : ℝ)) (𝓝 (P (path 1) * Λ (path 1))) := by
    have hcont : ContinuousAt (fun σ : ℝ => P (path σ) * Λ (path σ)) 1 :=
      ((hPdiff.continuous.comp hpath_cont).mul (hΛ.continuous.comp hpath_cont)).continuousAt
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hEqU (hpathU σ hσ)).symm

  have hζ : Tendsto (fun σ : ℝ => ‖cexp (logSum (S₁ ∪ T) (fun _ => (1 : ℂ)) (path σ + σ₁))‖) (𝓝[>] (1 : ℝ)) atTop := by
    refine (tendsto_norm_exp_logSum_one_atTop (S₁ ∪ T)).congr fun σ => ?_
    have harg : path σ + (σ₁ : ℂ) = (σ : ℂ) := by simp only [hpathdef, Complex.ofReal_sub]; ring
    rw [harg]
  have hζinv : Tendsto (fun σ : ℝ => (cexp (logSum (S₁ ∪ T) (fun _ => (1 : ℂ)) (path σ + σ₁)))⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h__af := hζ.inv_tendsto_atTop
    simp only [norm_inv] at h__af ⊢
    exact h__af

  have hνpath : Tendsto (fun σ : ℝ => cexp (logSum (S₁ ∪ T) cν (path σ + σ₂))) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hmul := hEpath.mul hζinv
    rw [mul_zero] at hmul
    refine hmul.congr fun σ => ?_
    have hz := exp_logSum_ne_zero (S₁ ∪ T) (fun _ => (1 : ℂ)) (path σ + σ₁)
    simp only [hEdef]
    rw [mul_assoc, mul_comm (cexp (logSum (S₁ ∪ T) cν _)), ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

  have hTν : ∀ v : Pl K, v ∉ S₁ ∪ T → IsUnramifiedCharAt (ν₁⁻¹ * ν₂) v := fun v hv =>
    hSν v fun h => hv (Finset.mem_union_right _ (Finset.mem_union_right _ h))
  refine not_tendsto_exp_logSum_shift (S₁ ∪ T) (ν₁⁻¹ * ν₂) hνK hνc hνu hTν (σ₂ - σ₁) (by linarith) ?_
  refine hνpath.congr fun σ => ?_
  have harg : path σ + (σ₂ : ℂ) = (σ : ℂ) + ((σ₂ - σ₁ : ℝ) : ℂ) := by
    simp only [hpathdef, Complex.ofReal_sub]; ring
  rw [harg]

end Q15PLK
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (hent : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
      IsUnitaryChar (𝓞 K) K χ →
      ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
        Differentiable ℂ Λ ∧
        ∀ s : ℂ, σ₀ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            ((if IsUnramifiedCharAt χ v.1
              then C 1 - C (((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
                + C ((((χ (uniformizerIdele K v.1)) ^ 2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
              else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s))
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (_h₁ : IsIdeleClassChar (𝓞 K) K μ₁) (_h₂ : IsIdeleClassChar (𝓞 K) K μ₂)
    (_hc₁ : Continuous μ₁) (_hc₂ : Continuous μ₂) :
    ¬ Pi.AgreesAwayFromFinite (eisensteinTableOf K N hN μ₁ μ₂) := by
  intro hA
  obtain ⟨σ₁, ν₁, hν₁K, hν₁c, hν₁u, hμ₁⟩ := Q15PLK.exists_unitaryPart K μ₁ _h₁ _hc₁ (Q15PLK.ideleNorm_principal K)
  obtain ⟨σ₂, ν₂, hν₂K, hν₂c, hν₂u, hμ₂⟩ := Q15PLK.exists_unitaryPart K μ₂ _h₂ _hc₂ (Q15PLK.ideleNorm_principal K)
  rcases le_total σ₁ σ₂ with h12 | h21
  · exact Q15PLK.core Pi hent N hN μ₁ μ₂ ν₁ ν₂ σ₁ σ₂ h12 hν₁K hν₁c hν₁u hμ₁ hν₂K hν₂c hν₂u hμ₂ hA
  · rw [Q15PLK.eisensteinTableOf_comm K N hN μ₁ μ₂] at hA
    exact Q15PLK.core Pi hent N hN μ₂ μ₁ ν₂ ν₁ σ₂ σ₁ h21 hν₂K hν₂c hν₂u hμ₂ hν₁K hν₁c hν₁u hμ₁ hA

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK.Zeta P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.Q15PLK"

end S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
end P2MW
export P2MW.S_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist (solution)
