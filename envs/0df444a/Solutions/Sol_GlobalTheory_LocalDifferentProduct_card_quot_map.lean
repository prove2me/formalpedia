-- Prove2me | solution 1 for GlobalTheory.LocalDifferentProduct.card_quot_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:08.686605+00:00
-- url     : https://prove2.me/submissions/2fc2a5e2-9339-4802-b0f8-38ec9d5a0c83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinprodLocalDifferentIdealNormEqDiscr
import Theorems.Thm_GlobalTheory_LocalDifferentProduct_valued_coe_algebraMap
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
namespace GlobalTheory.LocalDifferentProduct
section Local
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma valued_le_of_mem_map_of_le_pow {I : Ideal (𝓞 K)} {n : ℕ} (hIn : I ≤ v.asIdeal ^ n)
    {x : v.adicCompletionIntegers K} (hx : x ∈ I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) :
    Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap]
    exact (intValuation_le_pow_iff_mem v i n).mpr (hIn hi)
  | zero => simp
  | add y z _ _ hy hz =>
    push_cast
    exact Valuation.map_add_le _ hy hz
  | smul a y _ hy =>
    rw [smul_eq_mul]
    push_cast
    rw [Valuation.map_mul]
    calc Valued.v (a : v.adicCompletion K) * Valued.v (y : v.adicCompletion K)
        ≤ 1 * WithZero.exp (-(n : ℤ)) := mul_le_mul' (a.2 : Valued.v (a : v.adicCompletion K) ≤ 1) hy
      _ = _ := one_mul _
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma exists_notMem_mul_mem_of_pow_count {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∃ s : 𝓞 K, s ∉ v.asIdeal ∧
      ∀ a ∈ v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors, a * s ∈ I := by
  set n := (Associates.mk v.asIdeal).count (Associates.mk I).factors
  obtain ⟨J, hJ⟩ : v.maxPowDividing I ∣ I := Ideal.dvd_iff_le.mpr (by
    rw [← Ideal.dvd_iff_le]
    exact (Associates.mk_le_mk_iff_dvd).mp (by
      rw [maxPowDividing, Associates.mk_pow]
      exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
        v.associates_irreducible).mpr le_rfl))
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle
    have h1 : v.asIdeal ^ (n + 1) ∣ I := by
      rw [Ideal.dvd_iff_le, hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    have h2 := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
      v.associates_irreducible).mp (by
        rw [← Associates.mk_pow]
        exact Associates.mk_le_mk_iff_dvd.mpr h1)
    omega
  obtain ⟨s, hsJ, hsv⟩ := SetLike.not_le_iff_exists.mp hJv
  refine ⟨s, hsv, fun a ha => ?_⟩
  rw [hJ]
  exact Ideal.mul_mem_mul ha hsJ
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma mem_map_adicCompletionIntegers_of_valued_le {I : Ideal (𝓞 K)} (hI : I ≠ 0) {y : v.adicCompletionIntegers K}
    (hy : Valued.v (y : v.adicCompletion K) ≤
      WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ))) :
    y ∈ I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) := by
  set n := (Associates.mk v.asIdeal).count (Associates.mk I).factors
  obtain ⟨s, hsv, hs⟩ := exists_notMem_mul_mem_of_pow_count v hI
  obtain ⟨π, hπ⟩ := intValuation_exists_uniformizer v
  have hπn : v.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hs1 : v.intValuation s = 1 :=
    le_antisymm (v.intValuation_le_one s) (not_lt.mp fun h => hsv ((intValuation_lt_one_iff_mem v s).mp h))
  have hi₀ : π ^ n * s ∈ I := hs _ ((intValuation_le_pow_iff_mem v _ n).mp hπn.le)
  have hval : Valued.v ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (π ^ n * s) :
      v.adicCompletionIntegers K) : v.adicCompletion K) = WithZero.exp (-(n : ℤ)) := by
    rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap, map_mul, hπn, hs1, mul_one]
  set i₀ : v.adicCompletion K := ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (π ^ n * s) :
      v.adicCompletionIntegers K) : v.adicCompletion K) with hi₀def
  have hne : i₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hval
    exact WithZero.zero_ne_coe hval
  have hz : (y : v.adicCompletion K) / i₀ ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, map_div₀, hval]
    exact div_le_one_of_le₀ hy zero_le'
  have hy' : y = algebraMap (𝓞 K) (v.adicCompletionIntegers K) (π ^ n * s) * ⟨_, hz⟩ := by
    apply Subtype.ext
    show (y : v.adicCompletion K) = i₀ * ((y : v.adicCompletion K) / i₀)
    field_simp
  rw [hy']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hi₀)
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma exists_integer_valuation_sub_le_exp_neg (k : K) (hk : v.valuation K k ≤ 1) (n : ℕ) :
    ∃ a : 𝓞 K, v.valuation K (k - algebraMap (𝓞 K) K a) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hspan : Ideal.span {c} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨s, hsv, hs⟩ := exists_notMem_mul_mem_of_pow_count v hspan
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by
    simpa using hc0
  have hb : b ∈ v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {c})).factors := by
    rw [← intValuation_le_pow_iff_mem, ← intValuation_if_neg v hc0]
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap] at hk
    have hcv : v.intValuation c ≠ 0 := by
      rw [intValuation_if_neg v hc0]
      exact WithZero.exp_ne_zero
    exact (div_le_one₀ (zero_lt_iff.mpr hcv)).mp hk
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp (hs b hb)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv v.isMaximal hsv
  refine ⟨a' * (y * ∑ j ∈ Finset.range n, i ^ j), ?_⟩
  have hgeom := mul_neg_geom_sum i n
  have hk' : algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c -
      algebraMap (𝓞 K) K (a' * (y * ∑ j ∈ Finset.range n, i ^ j)) =
      algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c * algebraMap (𝓞 K) K (i ^ n) := by
    have h1 : algebraMap (𝓞 K) K a' * algebraMap (𝓞 K) K c =
        algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K s := by
      rw [← map_mul, ← map_mul, ha']
    have h2 : algebraMap (𝓞 K) K y * algebraMap (𝓞 K) K s =
        1 - algebraMap (𝓞 K) K i := by
      rw [← map_mul, ← map_one (algebraMap (𝓞 K) K), ← map_sub, ← hyi]
      ring_nf
    have h3 := congrArg (algebraMap (𝓞 K) K) hgeom
    simp only [map_mul, map_sub, map_one, map_pow, map_sum] at h3 ⊢
    have key : algebraMap (𝓞 K) K b - algebraMap (𝓞 K) K c * (algebraMap (𝓞 K) K a' *
        (algebraMap (𝓞 K) K y * ∑ j ∈ Finset.range n, algebraMap (𝓞 K) K i ^ j)) =
        algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K i ^ n := by
      linear_combination (-(algebraMap (𝓞 K) K y *
          ∑ j ∈ Finset.range n, algebraMap (𝓞 K) K i ^ j)) * h1 -
        (algebraMap (𝓞 K) K b * ∑ j ∈ Finset.range n, algebraMap (𝓞 K) K i ^ j) * h2 -
        algebraMap (𝓞 K) K b * h3
    field_simp
    linear_combination key
  rw [hk', map_mul, valuation_of_algebraMap]
  calc v.valuation K (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c) * v.intValuation (i ^ n)
      ≤ 1 * WithZero.exp (-(n : ℤ)) :=
        mul_le_mul' hk ((intValuation_le_pow_iff_mem v _ n).mpr (Ideal.pow_mem_pow hi n))
    _ = _ := one_mul _
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial in
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) in
private lemma exists_integer_valued_sub_le_exp_neg (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ a : 𝓞 K, Valued.v ((x : v.adicCompletion K) -
      ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
        v.adicCompletion K)) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := intValuation_exists_uniformizer v
  set z : v.adicCompletion K := ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) (π ^ n) :
    v.adicCompletionIntegers K) : v.adicCompletion K)
  have hvz : Valued.v z = WithZero.exp (-(n : ℤ)) := by
    rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap, map_pow, hπ,
      ← WithZero.exp_nsmul]
    congr 1
    simp
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hvz
    exact WithZero.zero_ne_coe hvz
  have hnhds : {y : v.adicCompletion K | Valued.v ((x : v.adicCompletion K) - y) ≤
      WithZero.exp (-(n : ℤ))} ∈ nhds (x : v.adicCompletion K) := by
    have ho := Valued.isOpen_closedBall (v.adicCompletion K)
      ((Valuation.ne_zero_iff Valued.v.restrict).mpr hz0)
    have hc : Continuous fun y : v.adicCompletion K => (x : v.adicCompletion K) - y :=
      continuous_const.sub continuous_id
    refine Filter.mem_of_superset ((ho.preimage hc).mem_nhds ?_) ?_
    · show Valued.v.restrict ((x : v.adicCompletion K) - x) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    · intro y hy
      rw [Set.mem_setOf_eq, ← hvz]
      exact (Valuation.restrict_le_iff Valued.v).mp hy
  obtain ⟨_, hz, ⟨k, rfl⟩⟩ := mem_closure_iff_nhds.mp
    ((denseRange_algebraMap (K := K) v) (x : v.adicCompletion K)) _ hnhds
  simp only [Set.mem_setOf_eq] at hz
  have hk1 : v.valuation K k ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have hle : WithZero.exp (-(n : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have h := Valuation.map_sub_le _ hx1 (hz.trans hle)
    rw [sub_sub_cancel] at h
    have e : algebraMap K (v.adicCompletion K) k = (k : v.adicCompletion K) := rfl
    rw [e] at h
    simpa using h
  obtain ⟨a, ha⟩ := exists_integer_valuation_sub_le_exp_neg v k hk1 n
  refine ⟨a, ?_⟩
  have e1 : ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) := rfl
  have hsplit : (x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) =
      ((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) k) +
      algebraMap K (v.adicCompletion K) (k - algebraMap (𝓞 K) K a) := by
    rw [map_sub]
    ring
  rw [e1, hsplit]
  refine Valuation.map_add_le _ hz ?_
  have e2 : algebraMap K (v.adicCompletion K) (k - algebraMap (𝓞 K) K a) =
      ((k - algebraMap (𝓞 K) K a : K) : v.adicCompletion K) := rfl
  rw [e2, valuedAdicCompletion_eq_valuation']
  exact ha
end Local
section Relative
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
end Relative
end GlobalTheory.LocalDifferentProduct
end

set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
open GlobalTheory GlobalTheory.LocalDifferentProduct
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GlobalTheory.LocalDifferentProduct
namespace _root_.GlobalTheory.LocalDifferentProduct
theorem _root_.solution {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) =
      Ideal.absNorm (v.maxPowDividing I) := by
  set n := (Associates.mk v.asIdeal).count (Associates.mk I).factors
  have hIn : I ≤ v.asIdeal ^ n := by
    rw [← Ideal.dvd_iff_le]
    exact (Associates.mk_le_mk_iff_dvd).mp (by
      rw [Associates.mk_pow]
      exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
        v.associates_irreducible).mpr le_rfl)
  let f : 𝓞 K →+* v.adicCompletionIntegers K ⧸
      I.map (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 K) (v.adicCompletionIntegers K))
  have hker : RingHom.ker f = v.asIdeal ^ n := by
    ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h
      have h' := valued_le_of_mem_map_of_le_pow v hIn h
      rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap] at h'
      exact (intValuation_le_pow_iff_mem v a n).mp h'
    · intro h
      apply mem_map_adicCompletionIntegers_of_valued_le v hI
      rw [_root_.GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap]
      exact (intValuation_le_pow_iff_mem v a n).mpr h
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := exists_integer_valued_sub_le_exp_neg v x n
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    apply mem_map_adicCompletionIntegers_of_valued_le v hI
    rw [Valuation.map_sub_swap] at ha
    exact_mod_cast ha
  change _ = Ideal.absNorm (v.asIdeal ^ n)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv.symm
end _root_.GlobalTheory.LocalDifferentProduct
end GlobalTheory.LocalDifferentProduct
