-- Prove2me | solution 1 for NumberField.denseRange_algebraMap_add_adeleSingleAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7df0df1b-7246-595c-b207-66f1eecd0217

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.RingTheory.FractionalIdeal.Norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_denseRange_algebraMap_add_adeleSingleAt

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped RestrictedProduct nonZeroDivisors

noncomputable section

private theorem wz_exists_pow_lt_of_lt_one (x γ : WithZero (Multiplicative ℤ)) (hx : x < 1) (hγ : γ ≠ 0) :
    ∃ n : ℕ, x ^ n < γ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨1, by rw [pow_one]; exact zero_lt_iff.mpr hγ⟩
  · have hl : WithZero.log x < 0 := by
      have h := (WithZero.log_lt_log hx0 one_ne_zero).mpr hx
      simpa using h
    refine ⟨(WithZero.log γ).natAbs + 1, ?_⟩
    rw [← WithZero.exp_log hγ]
    apply WithZero.lt_exp_of_log_lt
    rw [WithZero.log_pow, nsmul_eq_mul]
    have hn : (0 : ℤ) ≤ (((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) := by positivity
    have h1 : (((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) * WithZero.log x ≤
        -(((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) := by nlinarith
    have h2 : -(((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) < WithZero.log γ := by omega
    exact h1.trans_lt h2

section Generic

variable {K : Type} [Field K] [NumberField K]

private theorem exists_radius_of_mem_nhds (i : HeightOneSpectrum (𝓞 K)) (x : i.adicCompletion K)
    (s : Set (i.adicCompletion K)) (hs : s ∈ nhds x) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ y : i.adicCompletion K, Valued.v (y - x) < γ → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1, (map_ne_zero _).mpr γ.ne_zero, fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x) < γ.1
  exact (Valuation.restrict_lt_iff_lt_embedding _).mpr hy

private theorem exists_pow_intValuation_lt (i : HeightOneSpectrum (𝓞 K)) (γ : WithZero (Multiplicative ℤ))
    (hγ : γ ≠ 0) : ∃ a : 𝓞 K, a ≠ 0 ∧ i.intValuation a < γ := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot i.ne_bot
  have hlt : i.intValuation π < 1 := (i.intValuation_lt_one_iff_mem π).mpr hπ
  obtain ⟨n, hn⟩ := wz_exists_pow_lt_of_lt_one _ γ hlt hγ
  exact ⟨π ^ n, pow_ne_zero n hπ0, by rw [map_pow]; exact hn⟩

private theorem exists_ne_zero_forall_intValuation_lt (T : Finset (HeightOneSpectrum (𝓞 K)))
    (γ : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ)) (hγ : ∀ i, γ i ≠ 0) :
    ∃ N : 𝓞 K, N ≠ 0 ∧ ∀ i ∈ T, i.intValuation N < γ i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun i hi => by simp at hi⟩
  | insert j T hj ih =>
    obtain ⟨N, hN0, hN⟩ := ih
    obtain ⟨a, ha0, ha⟩ := exists_pow_intValuation_lt j (γ j) (hγ j)
    refine ⟨N * a, mul_ne_zero hN0 ha0, fun i hi => ?_⟩
    rw [map_mul]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · calc i.intValuation N * i.intValuation a ≤ 1 * i.intValuation a :=
            mul_le_mul_left (i.intValuation_le_one N) _
        _ = i.intValuation a := one_mul _
        _ < γ i := ha
    · calc i.intValuation N * i.intValuation a ≤ i.intValuation N * 1 :=
            mul_le_mul_right (i.intValuation_le_one a) _
        _ = i.intValuation N := mul_one _
        _ < γ i := hN i hi

private def idealUnit (N : 𝓞 K) (hN : N ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 ((Ideal.span {N} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hN)) *
    (Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))⁻¹ ^ k

private theorem val_idealUnit (N : 𝓞 K) (hN : N ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    ((idealUnit N hN v k : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      ((Ideal.span {N} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K))⁻¹ ^ k := by
  rw [idealUnit, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0,
    Units.val_mk0]

private theorem absNorm_idealUnit (N : 𝓞 K) (hN : N ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    FractionalIdeal.absNorm ((idealUnit N hN v k : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (Ideal.absNorm (Ideal.span {N} : Ideal (𝓞 K)) : ℚ) * ((Ideal.absNorm v.asIdeal : ℚ)⁻¹) ^ k := by
  rw [val_idealUnit, map_mul, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.coeIdeal_absNorm]

private theorem minkowskiBound_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedEmbedding.minkowskiBound K I =
      ENNReal.ofReal ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) *
        mixedEmbedding.minkowskiBound K 1 := by
  rw [mixedEmbedding.minkowskiBound, mixedEmbedding.minkowskiBound,
    mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
    mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis, Units.val_one,
    FractionalIdeal.absNorm_one, Rat.cast_one, ENNReal.ofReal_one, one_mul, mul_assoc]

private theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem exists_minkowskiBound_lt (N : 𝓞 K) (hN : N ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (V : ENNReal) (hV : 0 < V) : ∃ k : ℕ, mixedEmbedding.minkowskiBound K (idealUnit N hN v k) < V := by
  have h1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have := two_le_absNorm v
    exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)
  have hgeom : Filter.Tendsto (fun k : ℕ =>
      ((FractionalIdeal.absNorm ((idealUnit N hN v k : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg _))
      (inv_lt_one_of_one_lt₀ h1)).const_mul (Ideal.absNorm (Ideal.span {N} : Ideal (𝓞 K)) : ℝ)
    rw [mul_zero] at h
    refine h.congr fun k => ?_
    rw [absNorm_idealUnit]
    push_cast
    ring
  have hmul := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hgeom)
    (Or.inr (mixedEmbedding.minkowskiBound_lt_top K 1).ne)
  rw [ENNReal.ofReal_zero, zero_mul] at hmul
  obtain ⟨k, hk⟩ := (hmul.eventually (gt_mem_nhds hV)).exists
  exact ⟨k, by rw [minkowskiBound_eq]; exact hk⟩

private theorem valuation_le_of_mem (N : 𝓞 K) (v i : HeightOneSpectrum (𝓞 K)) (hi : i ≠ v) (k : ℕ) {a : K}
    (ha : a ∈ ((Ideal.span {N} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K))⁻¹ ^ k) :
    i.valuation K a ≤ i.intValuation N := by
  have hvi : ¬ v.asIdeal ≤ i.asIdeal := fun h =>
    hi (HeightOneSpectrum.asIdeal_injective (v.isMaximal.eq_of_le i.isPrime.ne_top h)).symm
  obtain ⟨π, hπv, hπi⟩ := SetLike.not_le_iff_exists.mp hvi
  have hπ1 : i.intValuation π = 1 := (i.intValuation_eq_one_iff_mem_primeCompl π).mpr hπi
  have hπk : algebraMap (𝓞 K) K (π ^ k) ∈ ((v.asIdeal ^ k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨π ^ k, Ideal.pow_mem_pow hπv k, rfl⟩
  have hmul : a * algebraMap (𝓞 K) K (π ^ k) ∈ ((Ideal.span {N} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := FractionalIdeal.mul_mem_mul ha hπk
    rwa [FractionalIdeal.coeIdeal_pow, mul_assoc, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero k (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)), mul_one] at h
  obtain ⟨b, hb, hab⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmul
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have hval : i.valuation K (algebraMap (𝓞 K) K (c * N)) = i.valuation K (a * algebraMap (𝓞 K) K (π ^ k)) := by
    rw [hab]
  rw [Valuation.map_mul, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    map_pow, hπ1, one_pow, mul_one] at hval
  rw [← hval, map_mul]
  calc i.intValuation c * i.intValuation N ≤ 1 * i.intValuation N :=
        mul_le_mul_left (i.intValuation_le_one c) _
    _ = i.intValuation N := one_mul _

open scoped Classical in

private theorem exists_multiplier (N : 𝓞 K) (hN : N ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : K, a ≠ 0 ∧ (∀ i : HeightOneSpectrum (𝓞 K), i ≠ v → i.valuation K a ≤ i.intValuation N) ∧
      ∀ w : InfinitePlace K, w a < ε := by
  set f : InfinitePlace K → NNReal := fun _ => ε.toNNReal with hf
  have hf0 : ∀ w, f w ≠ 0 := fun _ => (Real.toNNReal_pos.mpr hε).ne'
  have hvol : 0 < MeasureTheory.volume (mixedEmbedding.convexBodyLT K f) := by
    rw [mixedEmbedding.convexBodyLT_volume]
    exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (mixedEmbedding.convexBodyLTFactor_ne_zero K))
      (ENNReal.coe_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (hf0 w)))
  obtain ⟨k, hk⟩ := exists_minkowskiBound_lt N hN v _ hvol
  obtain ⟨a, ha, ha0, haw⟩ := mixedEmbedding.exists_ne_zero_mem_ideal_lt K (idealUnit N hN v k) hk
  refine ⟨a, ha0, fun i hi => ?_, fun w => ?_⟩
  · rw [val_idealUnit] at ha
    exact valuation_le_of_mem N v i hi k ha
  · have h := haw w
    rwa [hf, Real.coe_toNNReal ε hε.le] at h

private theorem finite_algebraMap_apply (q : K) (i : HeightOneSpectrum (𝓞 K)) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) q i = algebraMap K (i.adicCompletion K) q := rfl

private theorem finite_mul_apply (y z : FiniteAdeleRing (𝓞 K) K) (i : HeightOneSpectrum (𝓞 K)) :
    (y * z) i = y i * z i := rfl

private theorem finite_add_apply (y z : FiniteAdeleRing (𝓞 K) K) (i : HeightOneSpectrum (𝓞 K)) :
    (y + z) i = y i + z i := rfl

omit [NumberField K] in
private theorem infinite_mul_apply (y z : InfiniteAdeleRing K) (w : InfinitePlace K) : (y * z) w = y w * z w := rfl

omit [NumberField K] in

private theorem norm_infinite_algebraMap_apply (q : K) (w : InfinitePlace K) :
    ‖algebraMap K (InfiniteAdeleRing K) q w‖ = w q := by
  have he : algebraMap K (InfiniteAdeleRing K) q w = ((WithAbs.equiv w.1).symm q : w.Completion) := rfl
  rw [he, InfinitePlace.Completion.norm_coe]
  rfl

private theorem valued_algebraMap_adicCompletion (i : HeightOneSpectrum (𝓞 K)) (q : K) :
    Valued.v (algebraMap K (i.adicCompletion K) q) = i.valuation K q :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' i (algebraMap K K q)

private theorem valued_correction_le (i : HeightOneSpectrum (𝓞 K)) (N : 𝓞 K) (s : K)
    (hs : i.valuation K s ≤ i.intValuation N) (y : FiniteAdeleRing (𝓞 K) K)
    (hy : y i ∈ i.adicCompletionIntegers K) :
    Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) s * y) i) ≤ i.intValuation N := by
  rw [finite_mul_apply, finite_algebraMap_apply, Valuation.map_mul, valued_algebraMap_adicCompletion]
  have hy1 : Valued.v (y i) ≤ 1 := by rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at hy
  calc i.valuation K s * Valued.v (y i) ≤ i.intValuation N * 1 := mul_le_mul' hs hy1
    _ = i.intValuation N := mul_one _

omit [NumberField K] in

private theorem tendsto_infinite_correction (r : ℝ) (a : ℕ → K)
    (ha : ∀ k : ℕ, ∀ w : InfinitePlace K, w (a k) < 1 / ((k : ℝ) + 1)) (y : ℕ → InfiniteAdeleRing K)
    (hy : ∀ k, ∀ w : InfinitePlace K, ‖y k w‖ ≤ r) :
    Filter.Tendsto (fun k : ℕ => algebraMap K (InfiniteAdeleRing K) (a k) * y k) Filter.atTop (nhds 0) := by
  refine tendsto_pi_nhds.mpr fun w => ?_
  have hlim : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) * |r|) Filter.atTop (nhds 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const |r|
    rwa [zero_mul] at h
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [infinite_mul_apply, norm_mul, norm_infinite_algebraMap_apply]
  exact mul_le_mul (ha k w).le ((hy k w).trans (le_abs_self r)) (norm_nonneg _) (by positivity)

private theorem exists_decomposition (x : AdeleRing (𝓞 K) K) (s : K) (hs : s ≠ 0) :
    ∃ q : K, ∃ B : AdeleRing (𝓞 K) K, B ∈ AdelicBox.adelicBox K ∧
      x - algebraMap K (AdeleRing (𝓞 K) K) q = algebraMap K (AdeleRing (𝓞 K) K) s * B := by
  obtain ⟨κ, hκ, -⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox K
    (algebraMap K (AdeleRing (𝓞 K) K) s⁻¹ * x)
  refine ⟨-(s * κ), _, hκ, ?_⟩
  rw [map_neg, sub_neg_eq_add, mul_add, ← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hs, map_one, one_mul,
    add_comm]

private theorem isOpen_adicCompletionIntegers (i : HeightOneSpectrum (𝓞 K)) :
    IsOpen (i.adicCompletionIntegers K : Set (i.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

end Generic

theorem solution (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    DenseRange fun qy : K × v.adicCompletion K =>
      algebraMap K (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt K v qy.2 := by
  classical
  obtain ⟨r, hr⟩ := AdelicBox.exists_forall_norm_apply_le_of_mem_infiniteBox K
  intro x
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨U₁, hU₁, U₂, hU₂, hUW⟩ := mem_nhds_prod_iff.mp hW

  obtain ⟨S, hS_nhds, hS_cof, hS_sub⟩ := (RestrictedProduct.mem_nhds_iff_of_cofinite
    (fun i => isOpen_adicCompletionIntegers i) (x := x.2) (U := U₂)).mp hU₂
  have hT : {i : HeightOneSpectrum (𝓞 K) |
      ¬ S i = (i.adicCompletionIntegers K : Set (i.adicCompletion K))}.Finite := Filter.eventually_cofinite.mp hS_cof

  choose γ hγ0 hγ using fun i => exists_radius_of_mem_nhds i (x.2 i) (S i) (hS_nhds i)

  obtain ⟨N, hN0, hN⟩ := exists_ne_zero_forall_intValuation_lt hT.toFinset γ hγ0

  choose a ha0 ha_fin ha_arch using fun k : ℕ => exists_multiplier N hN0 v (1 / ((k : ℝ) + 1)) (by positivity)

  choose q B hB hxqB using fun k => exists_decomposition x (a k) (ha0 k)
  have hBbox : ∀ k, (B k).1 ∈ AdelicBox.infiniteBox K ∧
      (B k).2 ∈ AdelicBox.integralFiniteAdeles (𝓞 K) K := fun k => hB k

  have htend : Filter.Tendsto (fun k => (x - algebraMap K (AdeleRing (𝓞 K) K) (q k)).1)
      Filter.atTop (nhds 0) := by
    have h := tendsto_infinite_correction r a ha_arch (fun k => (B k).1) (fun k w => hr _ (hBbox k).1 w)
    refine h.congr fun k => ?_
    rw [hxqB k]
    rfl

  have hfst : Filter.Tendsto (fun k => (algebraMap K (AdeleRing (𝓞 K) K) (q k)).1)
      Filter.atTop (nhds x.1) := by
    have h := tendsto_const_nhds (x := x.1) |>.sub htend
    rw [sub_zero] at h
    refine h.congr fun k => ?_
    exact sub_sub_cancel x.1 (algebraMap K (AdeleRing (𝓞 K) K) (q k)).1
  obtain ⟨k, hk⟩ := (hfst.eventually_mem hU₁).exists

  refine ⟨_, ?_, (q k, (x - algebraMap K (AdeleRing (𝓞 K) K) (q k)).2 v), rfl⟩
  apply hUW
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  ·
    show (algebraMap K (AdeleRing (𝓞 K) K) (q k)).1 + (0 : InfiniteAdeleRing K) ∈ U₁
    rw [add_zero]
    exact hk
  ·
    show algebraMap K (FiniteAdeleRing (𝓞 K) K) (q k) +
      StandardAddChar.finAdeleSingleAt K v ((x - algebraMap K (AdeleRing (𝓞 K) K) (q k)).2 v) ∈ U₂
    set z : FiniteAdeleRing (𝓞 K) K := algebraMap K (FiniteAdeleRing (𝓞 K) K) (q k) +
      StandardAddChar.finAdeleSingleAt K v ((x - algebraMap K (AdeleRing (𝓞 K) K) (q k)).2 v) with hz

    have hD : ∀ i, (x - algebraMap K (AdeleRing (𝓞 K) K) (q k)).2 i = x.2 i -
        algebraMap K (i.adicCompletion K) (q k) := fun i => rfl
    have hD' : (x - algebraMap K (AdeleRing (𝓞 K) K) (q k)).2 =
        algebraMap K (FiniteAdeleRing (𝓞 K) K) (a k) * (B k).2 := by
      rw [hxqB k]; rfl
    have hcorr : ∀ i, i ≠ v → Valued.v (x.2 i - algebraMap K (i.adicCompletion K) (q k)) ≤ i.intValuation N := by
      intro i hi
      rw [← hD i, hD']
      exact valued_correction_le i N (a k) (ha_fin k i hi) (B k).2 ((hBbox k).2 i)
    have hz_mem : ∀ i, z i ∈ S i := by
      intro i
      by_cases hiv : i = v
      · subst hiv
        rw [hz, finite_add_apply, finite_algebraMap_apply, StandardAddChar.finAdeleSingleAt_apply_self, hD,
          add_sub_cancel]
        exact mem_of_mem_nhds (hS_nhds i)
      · have hzi : z i = algebraMap K (i.adicCompletion K) (q k) := by
          rw [hz, finite_add_apply, finite_algebraMap_apply, StandardAddChar.finAdeleSingleAt_apply_of_ne _ _ _ hiv,
            add_zero]
        by_cases hiT : S i = (i.adicCompletionIntegers K : Set (i.adicCompletion K))
        ·
          rw [hiT, SetLike.mem_coe, hzi]
          have hx_int : x.2 i ∈ i.adicCompletionIntegers K := by
            have := mem_of_mem_nhds (hS_nhds i)
            rwa [hiT, SetLike.mem_coe] at this
          have hc_int : x.2 i - algebraMap K (i.adicCompletion K) (q k) ∈ i.adicCompletionIntegers K := by
            rw [HeightOneSpectrum.mem_adicCompletionIntegers]
            exact (hcorr i hiv).trans (i.intValuation_le_one N)
          have := sub_mem hx_int hc_int
          rwa [sub_sub_cancel] at this
        ·
          have hiT' : i ∈ hT.toFinset := hT.mem_toFinset.mpr hiT
          rw [hzi]
          apply hγ i
          rw [← Valuation.map_neg, neg_sub]
          exact (hcorr i hiv).trans_lt (hN i hiT')
    have hz_pi : (⇑z : ∀ i : HeightOneSpectrum (𝓞 K), i.adicCompletion K) ∈ Set.univ.pi S :=
      Set.mem_univ_pi.mpr hz_mem
    obtain ⟨u, hu, huz⟩ := hS_sub hz_pi
    rwa [show u = z from DFunLike.coe_injective huz] at hu

end

end S_NumberField_denseRange_algebraMap_add_adeleSingleAt
end P2MW
export P2MW.S_NumberField_denseRange_algebraMap_add_adeleSingleAt (solution)
