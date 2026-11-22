-- Prove2me | solution 1 for MasulloGRH.zetaIntegral_eq_sZetaIntegral_mul_partialEulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:48:54.544666+00:00
-- url     : https://prove2.me/submissions/2de3bb87-9c36-4d9b-9657-8ffc356fedcf

import Mathlib
import Definitions.Def_MasulloGRH_ZetaIntegrals
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals
import Theorems.Thm_MasulloGRH_tamagawa_measures_wellDefined
import Theorems.Thm_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa
import Theorems.Thm_MasulloGRH_sZetaIntegral_integrable_and_differentiableOn

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

/-!
# Weil's identity in the unramified case (Theorem 3.4.1.1, eq. (3.4.1.6), corrected)

The support of `f = f_S ⊗ 1` in the ideles is cut into the pieces
`E n = π^n · GL₁(𝔸_{F,S} × ∏_{v ∉ S} 𝒪_vˣ)`, `n` a finitely supported exponent vector on the places
outside `S`.  On `E n` the integrand is `χ(π^n)|π^n|^s` times the pull-back of the `S`-local
integrand, so by left invariance of the Tamagawa measure and Lemma A.3.2.4 its integral is
`∏_v (χ(𝔭_v) N(𝔭_v)^{-s})^{n_v} · C · Z_S`.  Summing over `n` gives the Euler product
(`SolEuler.hasProd_mw`, a sieve argument; absolute convergence from `∑_v N(𝔭_v)^{-σ} < ∞`).
-/

namespace Sol_MasulloGRH_zetaIntegral_eq_sZetaIntegral_mul_partialEulerProduct

open Filter Topology RestrictedProduct
open scoped ENNReal NNReal

namespace SolEuler

variable {ι : Type*}

noncomputable def mw {R : Type*} [CommMonoid R] (b : ι → R) (n : ι →₀ ℕ) : R :=
  n.prod fun i k => b i ^ k

section
variable {R : Type*} [CommMonoid R] (b : ι → R)

theorem mw_add (m n : ι →₀ ℕ) : mw b (m + n) = mw b m * mw b n := by
  classical
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

@[simp] theorem mw_zero : mw b 0 = 1 := Finsupp.prod_zero_index

theorem mw_single (i : ι) (k : ℕ) : mw b (Finsupp.single i k) = b i ^ k :=
  Finsupp.prod_single_index (pow_zero _)

theorem mw_map {S : Type*} [CommMonoid S] (φ : R →* S) (n : ι →₀ ℕ) :
    φ (mw b n) = mw (fun i => φ (b i)) n := by
  unfold mw Finsupp.prod
  rw [map_prod]
  simp [map_pow]
end

theorem norm_mw (b : ι → ℂ) (n : ι →₀ ℕ) : ‖mw b n‖ = mw (fun i => ‖b i‖) n := by
  unfold mw Finsupp.prod
  rw [norm_prod]
  simp [norm_pow]

theorem tsum_good (x : ι → ℝ≥0∞) (S : Finset ι) :
    ∑' n : ι →₀ ℕ, {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0}.indicator (mw x) n =
      ∏ i ∈ S, (1 - x i)⁻¹ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : {n : ι →₀ ℕ | ∀ i, i ∉ (∅ : Finset ι) → n i = 0} = {0} := by
      ext n
      simp only [Finset.notMem_empty, not_false_eq_true, forall_const, Set.mem_setOf_eq,
        Set.mem_singleton_iff]
      exact ⟨fun h => Finsupp.ext h, fun h i => by simp [h]⟩
    rw [this, tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp, ← ih, ← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_right]
    have h2 : ∀ k : ℕ, x p ^ k * ∑' n : ι →₀ ℕ,
        {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0}.indicator (mw x) n =
        ∑' n : ι →₀ ℕ, x p ^ k * {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0}.indicator (mw x) n :=
      fun k => (ENNReal.tsum_mul_left).symm
    rw [tsum_congr h2, ← ENNReal.tsum_prod]
    refine tsum_eq_tsum_of_ne_zero_bij (fun q => Finsupp.single p q.1.1 + q.1.2) ?_ ?_ ?_
    · rintro ⟨⟨k, m⟩, hq⟩ ⟨⟨k', m'⟩, hq'⟩ he
      simp only [Function.mem_support, ne_eq] at hq hq' he
      have hm : m ∈ {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0} := by
        by_contra h; exact hq (by rw [Set.indicator_of_notMem h, mul_zero])
      have hm' : m' ∈ {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0} := by
        by_contra h; exact hq' (by rw [Set.indicator_of_notMem h, mul_zero])
      have hk : k = k' := by
        have := congrArg (fun n => n p) he
        simpa [hm p hp, hm' p hp] using this
      subst hk
      have : m = m' := add_left_cancel he
      subst this
      rfl
    · intro n hn
      simp only [Function.mem_support, ne_eq] at hn
      have hgood : n ∈ {n : ι →₀ ℕ | ∀ i, i ∉ insert p S → n i = 0} := by
        by_contra h; exact hn (Set.indicator_of_notMem h _)
      have hgood' : Finsupp.erase p n ∈ {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0} := by
        intro i hi
        by_cases hip : i = p
        · subst hip; simp
        · rw [Finsupp.erase_ne hip]
          exact hgood i (by simp [hip, hi])
      have hsplit : Finsupp.single p (n p) + Finsupp.erase p n = n := Finsupp.single_add_erase p n
      refine ⟨⟨(n p, Finsupp.erase p n), ?_⟩, hsplit⟩
      simp only [Function.mem_support, ne_eq]
      rw [Set.indicator_of_mem hgood', ← mw_single x p (n p), ← mw_add, hsplit]
      rwa [Set.indicator_of_mem hgood] at hn
    · rintro ⟨⟨k, m⟩, hq⟩
      simp only [Function.mem_support, ne_eq] at hq
      have hm : m ∈ {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0} := by
        by_contra h; exact hq (by rw [Set.indicator_of_notMem h, mul_zero])
      have hgood : Finsupp.single p k + m ∈ {n : ι →₀ ℕ | ∀ i, i ∉ insert p S → n i = 0} := by
        intro i hi
        have hip : i ≠ p := fun h => hi (by simp [h])
        have hiS : i ∉ S := fun h => hi (by simp [h])
        simp [Finsupp.single_apply, Ne.symm hip, hm i hiS]
      simp only
      rw [Set.indicator_of_mem hgood, Set.indicator_of_mem hm, mw_add, mw_single]

theorem summable_norm_mw (b : ι → ℂ) (hb : Summable fun i => ‖b i‖) (h2 : ∀ i, ‖b i‖ ≤ 1 / 2) :
    Summable fun n : ι →₀ ℕ => ‖mw b n‖ := by
  classical
  have hnorm : ∀ n, ‖mw b n‖ = ((mw (fun i => ‖b i‖₊) n : ℝ≥0) : ℝ) := by
    intro n
    rw [norm_mw]
    unfold mw Finsupp.prod
    simp
  simp_rw [hnorm]
  rw [NNReal.summable_coe, ← ENNReal.tsum_coe_ne_top_iff_summable]
  apply ne_top_of_le_ne_top (b := ENNReal.ofReal (Real.exp (2 * ∑' i, ‖b i‖))) ENNReal.ofReal_ne_top
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun u => ?_
  set S := u.biUnion fun n => n.support
  have hx : ∀ i, (‖b i‖₊ : ℝ≥0∞) < 1 := by
    intro i
    have : ‖b i‖ < 1 := (h2 i).trans_lt (by norm_num)
    exact_mod_cast this
  calc ∑ n ∈ u, ((mw (fun i => ‖b i‖₊) n : ℝ≥0) : ℝ≥0∞)
        = ∑ n ∈ u, {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0}.indicator
            (mw (fun i => (‖b i‖₊ : ℝ≥0∞))) n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Set.indicator_of_mem]
        · exact mw_map (fun i => ‖b i‖₊) ENNReal.ofNNRealHom.toMonoidHom n
        · intro i hi
          by_contra h
          exact hi (Finset.mem_biUnion.mpr ⟨n, hn, Finsupp.mem_support_iff.mpr h⟩)
    _ ≤ ∑' n, {n : ι →₀ ℕ | ∀ i, i ∉ S → n i = 0}.indicator
            (mw (fun i => (‖b i‖₊ : ℝ≥0∞))) n := ENNReal.sum_le_tsum _
    _ = ∏ i ∈ S, (1 - (‖b i‖₊ : ℝ≥0∞))⁻¹ := tsum_good _ S
    _ ≤ ∏ i ∈ S, ENNReal.ofReal (Real.exp (2 * ‖b i‖)) := by
        refine Finset.prod_le_prod' fun i _ => ?_
        have hb1 : ‖b i‖ < 1 := (h2 i).trans_lt (by norm_num)
        have e1 : (1 - (‖b i‖₊ : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((1 - ‖b i‖)⁻¹) := by
          rw [ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_sub _ (norm_nonneg _),
            ENNReal.ofReal_one, ofReal_norm]
          rfl
        rw [e1]
        apply ENNReal.ofReal_le_ofReal
        have hpos : 0 < 1 - ‖b i‖ := by linarith
        rw [inv_le_iff_one_le_mul₀ hpos]
        have := Real.add_one_le_exp (2 * ‖b i‖)
        nlinarith [norm_nonneg (b i), h2 i]
    _ = ENNReal.ofReal (Real.exp (2 * ∑ i ∈ S, ‖b i‖)) := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum,
          Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Real.exp (2 * ∑' i, ‖b i‖)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have := hb.sum_le_tsum S (fun i _ => norm_nonneg (b i))
        linarith

theorem hasProd_mw (b : ι → ℂ) (hs : Summable fun n : ι →₀ ℕ => ‖mw b n‖) (h1 : ∀ i, b i ≠ 1) :
    HasProd (fun i => (1 - b i)⁻¹) (∑' n, mw b n) := by
  classical
  let good (S : Finset ι) : Set (ι →₀ ℕ) := {n | ∀ i ∈ S, n i = 0}
  let w (S : Finset ι) := (good S).indicator (mw b)
  let R (S : Finset ι) := ∑' n, w S n
  have hsum (S) : Summable (w S) := (hs.of_norm).indicator _
  have hrec (S : Finset ι) (p : ι) (hpS : p ∉ S) : R (insert p S) = (1 - b p) * R S := by
    let d := {n : ι →₀ ℕ | n p ≠ 0}.indicator (w S)
    have hdiff (n) : w (insert p S) n = w S n - d n := by
      by_cases h : n p = 0
      · have hiff : n ∈ good (insert p S) ↔ n ∈ good S := by
          simp only [good, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp, h, true_and]
        have hd : d n = 0 := Set.indicator_of_notMem (by simpa using h) _
        rw [hd, sub_zero]
        simp only [w, Set.indicator_apply, hiff]
      · have hbad : n ∉ good (insert p S) := fun hx => h (hx p (Finset.mem_insert_self _ _))
        have hd : d n = w S n := Set.indicator_of_mem (by simpa using h) _
        rw [hd, sub_self]
        exact Set.indicator_of_notMem hbad _
    have hcomp (n) : d (Finsupp.single p 1 + n) = b p * w S n := by
      have h1' : (Finsupp.single p 1 + n) ∈ {n : ι →₀ ℕ | n p ≠ 0} := by simp
      have hiff : Finsupp.single p 1 + n ∈ good S ↔ n ∈ good S := by
        simp only [good, Set.mem_setOf_eq]
        refine forall₂_congr fun i hi => ?_
        have : p ≠ i := fun h => hpS (h ▸ hi)
        simp [Finsupp.single_apply, this]
      rw [show d (Finsupp.single p 1 + n) = w S (Finsupp.single p 1 + n) from
        Set.indicator_of_mem h1' _]
      simp only [w, Set.indicator_apply, hiff]
      split_ifs <;> simp [mw_add, mw_single]
    have hdv : Function.support d ⊆ Set.range (fun n => Finsupp.single p 1 + n) := by
      intro n hn
      have hp : n p ≠ 0 := by
        by_contra h
        exact hn (Set.indicator_of_notMem (by simpa using h) _)
      refine ⟨n - Finsupp.single p 1, ?_⟩
      simp only
      rw [add_tsub_cancel_of_le]
      rw [Finsupp.single_le_iff]
      omega
    have hinj : Function.Injective (fun n : ι →₀ ℕ => Finsupp.single p 1 + n) :=
      add_right_injective _
    have hsumd : ∑' n, d n = b p * R S := by
      rw [← hinj.tsum_eq hdv, tsum_congr hcomp, tsum_mul_left]
    change ∑' n, w (insert p S) n = _
    rw [tsum_congr hdiff, (hsum S).tsum_sub ((hsum S).indicator _), hsumd]
    change R S - b p * R S = _
    ring
  have hfinite (S : Finset ι) : (∏ i ∈ S, (1 - b i)⁻¹) * R S = ∑' n, mw b n := by
    induction S using Finset.induction_on with
    | empty => simp [R, w, good]
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, hrec S i hi, ← ih]
      have hn : 1 - b i ≠ 0 := sub_ne_zero.mpr (h1 i).symm
      field_simp
  have hlim : Tendsto R atTop (𝓝 1) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter (Finset ι)))
      (f := fun S n => w S n) (g := fun n : ι →₀ ℕ => if n = 0 then (1 : ℂ) else 0) hs ?_ ?_
    · simpa [R, tsum_ite_eq] using h
    · intro n
      by_cases h : n = 0
      · subst h
        apply tendsto_const_nhds.congr
        intro S
        have : (0 : ι →₀ ℕ) ∈ good S := fun i _ => rfl
        simp [w, this]
      · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
          by_contra hc
          push_neg at hc
          exact h (Finsupp.ext hc)
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_ge_atTop {i}] with S hS
        have : n ∉ good S := fun hn => hi (hn i (hS (Finset.mem_singleton_self i)))
        simp [w, this, h]
    · exact Filter.Eventually.of_forall fun S n => by
        by_cases hn : n ∈ good S <;> simp [w, hn]
  have hn := hlim.eventually_ne (one_ne_zero : (1 : ℂ) ≠ 0)
  have h := (tendsto_const_nhds (x := ∑' n, mw b n)).div hlim one_ne_zero
  rw [div_one] at h
  unfold HasProd
  apply h.congr'
  filter_upwards [hn] with S hS
  exact (div_eq_iff hS).mpr (hfinite S).symm

/-- The Dirichlet series defining Dedekind zeta converges absolutely to the right of one. -/
theorem dedekindZeta_LSeriesSummable (F : Type*) [Field F] [NumberField F] {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // I.absNorm = n} : ℂ)) s := by
  have hres := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).eventually_ne
    (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero F))
  obtain ⟨t, ht, ht'⟩ := (hres.and (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs))).exists
  apply LSeriesSummable.of_re_le_re (s := (t : ℂ)) ht'.le
  by_contra hdiv
  exact ht (by rw [dedekindZeta, LSeries.eq_zero_of_not_LSeriesSummable _ _ hdiv, mul_zero])

theorem summable_absNorm_rpow (F : Type*) [Field F] [NumberField F] {r : ℝ} (hr : 1 < r) :
    Summable fun I : Ideal (𝓞 F) ↦ (I.absNorm : ℝ) ^ (-r) := by
  classical
  let A (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 F) // I.absNorm = n}
  have hsum : Summable (fun n : ℕ ↦ A n * (n : ℝ) ^ (-r)) := by
    apply (dedekindZeta_LSeriesSummable F (s := (r : ℂ)) hr).norm.congr
    intro n
    obtain rfl | hn := eq_or_ne n 0
    · simp [Real.zero_rpow (by linarith : -r ≠ 0)]
    · simp [hn, A, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  rw [← (Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 F))).summable_iff]
  have (n : ℕ) : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  refine (summable_sigma_of_nonneg (fun _ ↦ by dsimp; positivity)).2
    ⟨fun _ ↦ Summable.of_finite, hsum.congr fun n ↦ ?_⟩
  change _ = ∑' I : {I : Ideal (𝓞 F) // I.absNorm = n}, (I.val.absNorm : ℝ) ^ (-r)
  rw [tsum_congr (fun I : {I : Ideal (𝓞 F) // I.absNorm = n} ↦
    congrArg (fun m : ℕ ↦ (m : ℝ) ^ (-r)) I.property)]
  simp [A, tsum_const, nsmul_eq_mul]

theorem summable_prime_rpow (F : Type*) [Field F] [NumberField F] {r : ℝ} (hr : 1 < r) :
    Summable fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-r) :=
  (summable_absNorm_rpow F hr).comp_injective
    (fun v w h => IsDedekindDomain.HeightOneSpectrum.ext h)

end SolEuler

namespace SolInfra
open MasulloGRH

variable {F : Type*} [Field F] [NumberField F]

/-- finite coordinate of an idele -/
noncomputable def fc (v : HeightOneSpectrum (𝓞 F)) : IdeleGroup F →* v.adicCompletion F where
  toFun g := (g : AdeleRing (𝓞 F) F).2 v
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def ic (w : InfinitePlace F) : IdeleGroup F →* w.Completion where
  toFun g := (g : AdeleRing (𝓞 F) F).1 w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fc_apply (v : HeightOneSpectrum (𝓞 F)) (g : IdeleGroup F) :
    fc v g = (g : AdeleRing (𝓞 F) F).2 v := rfl

theorem ic_apply (w : InfinitePlace F) (g : IdeleGroup F) :
    ic w g = (g : AdeleRing (𝓞 F) F).1 w := rfl

open Classical in
theorem fc_ideleSingle (v w : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    fc w (ideleSingle v x) = ((RestrictedProduct.mulSingle
      (fun w : HeightOneSpectrum (𝓞 F) => (Submonoid.ofClass (w.adicCompletionIntegers F)).units)
        v x w : (w.adicCompletion F)ˣ) : w.adicCompletion F) := rfl

theorem fc_ideleSingle_same (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    fc v (ideleSingle v x) = x := by
  classical
  rw [fc_ideleSingle, RestrictedProduct.mulSingle_eq_same]

theorem fc_ideleSingle_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v)
    (x : (v.adicCompletion F)ˣ) : fc w (ideleSingle v x) = 1 := by
  classical
  rw [fc_ideleSingle, RestrictedProduct.mulSingle_eq_of_ne (A := (fun w : HeightOneSpectrum (𝓞 F) =>
    (Submonoid.ofClass (w.adicCompletionIntegers F)).units)) x h]
  rfl

theorem ic_ideleSingle (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ)
    (w : InfinitePlace F) : ic w (ideleSingle v x) = 1 := rfl

theorem exists_unif (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h1 : Valued.v ((π : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have h0 : ((π : F) : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  exact ⟨Units.mk0 _ h0, h1⟩

noncomputable def unif (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ :=
  (exists_unif v).choose

theorem unif_spec (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((unif v : (v.adicCompletion F)ˣ) : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
  (exists_unif v).choose_spec

theorem norm_eq_zpow_log (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : x ≠ 0) :
    ‖x‖ = (v.asIdeal.absNorm : ℝ) ^ WithZero.log (Valued.v x) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0, WithZero.toAdd_unzero_eq_log]
  simp

theorem norm_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [le_antisymm_iff, Valued.toNormedField.norm_le_one_iff,
    Valued.toNormedField.one_le_norm_iff, ← le_antisymm_iff]

theorem norm_unif (v : HeightOneSpectrum (𝓞 F)) :
    ‖((unif v : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
  rw [norm_eq_zpow_log _ _ (unif v).ne_zero, unif_spec, WithZero.log_exp, zpow_neg_one]

/-- The primeValue at an unramified place is the local component at our uniformizer. -/
theorem primeValue_eq (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hv : χ.IsUnramifiedAt v) : χ.primeValue v = χ.localComponent v (unif v) := by
  unfold HeckeCharacter.primeValue
  rw [dif_pos ⟨hv, exists_unif v⟩]
  rfl


section Ext
variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

open Classical in
noncomputable def jfFun (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F :=
  fun v => if h : v ∈ Sf then x ⟨v, h⟩ else 1

theorem jfFun_pos (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    (v : HeightOneSpectrum (𝓞 F)) (h : v ∈ Sf) : jfFun Sf x v = x ⟨v, h⟩ := by
  classical
  unfold jfFun
  rw [dif_pos h]

theorem jfFun_neg (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    (v : HeightOneSpectrum (𝓞 F)) (h : v ∉ Sf) : jfFun Sf x v = 1 := by
  classical
  unfold jfFun
  rw [dif_neg h]

theorem jfFun_mem (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    ∀ᶠ v in 𝓟 {v | v ∉ Sf},
      jfFun Sf x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [Filter.eventually_principal]
  intro v hv
  rw [jfFun_neg Sf x v hv]
  exact one_mem (v.adicCompletionIntegers F)

noncomputable def jfP (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 {v | v ∉ Sf}] :=
  RestrictedProduct.mk (jfFun Sf x) (jfFun_mem Sf x)

theorem cofinite_le : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 {v | v ∉ Sf} := by
  rw [Filter.le_principal_iff, Filter.mem_cofinite]
  have : {v : HeightOneSpectrum (𝓞 F) | v ∉ Sf}ᶜ = (Sf : Set (HeightOneSpectrum (𝓞 F))) := by
    ext v; simp
  rw [this]
  exact Sf.finite_toSet

noncomputable def jf (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (cofinite_le Sf) (jfP Sf x)

theorem jf_apply (x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    (v : HeightOneSpectrum (𝓞 F)) : jf Sf x v = jfFun Sf x v := rfl

theorem continuous_jf : Continuous (jf (F := F) Sf) := by
  apply (RestrictedProduct.continuous_inclusion (cofinite_le Sf)).comp
  rw [RestrictedProduct.continuous_rng_of_principal]
  apply continuous_pi
  intro v
  by_cases h : v ∈ Sf
  · have : (fun x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F =>
        (((jfP Sf x : Πʳ v : HeightOneSpectrum (𝓞 F),
          [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 {v | v ∉ Sf}]) :
            (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) v)) = fun x => x ⟨v, h⟩ := by
      funext x; exact jfFun_pos Sf x v h
    simpa [Function.comp_def, this] using continuous_apply (⟨v, h⟩ : Sf)
  · have : (fun x : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F =>
        (((jfP Sf x : Πʳ v : HeightOneSpectrum (𝓞 F),
          [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 {v | v ∉ Sf}]) :
            (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) v)) = fun _ => 1 := by
      funext x; exact jfFun_neg Sf x v h
    simpa [Function.comp_def, this] using continuous_const

noncomputable def J : SAdeleRing F Sf →* AdeleRing (𝓞 F) F where
  toFun x := ((x.1, jf Sf x.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  map_one' := by
    apply Prod.ext
    · rfl
    · apply IsDedekindDomain.FiniteAdeleRing.ext
      intro v
      show jf Sf (1 : SAdeleRing F Sf).2 v = (1 : FiniteAdeleRing (𝓞 F) F) v
      rw [jf_apply]
      by_cases h : v ∈ Sf
      · rw [jfFun_pos Sf _ v h]; rfl
      · rw [jfFun_neg Sf _ v h]; rfl
  map_mul' x y := by
    apply Prod.ext
    · rfl
    · apply IsDedekindDomain.FiniteAdeleRing.ext
      intro v
      show jf Sf (x * y).2 v = (jf Sf x.2 * jf Sf y.2) v
      rw [jf_apply]
      show _ = jf Sf x.2 v * jf Sf y.2 v
      rw [jf_apply, jf_apply]
      by_cases h : v ∈ Sf
      · rw [jfFun_pos Sf _ v h, jfFun_pos Sf _ v h, jfFun_pos Sf _ v h]; rfl
      · rw [jfFun_neg Sf _ v h, jfFun_neg Sf _ v h, jfFun_neg Sf _ v h, mul_one]

theorem continuous_J : Continuous (J (F := F) Sf) :=
  continuous_fst.prodMk ((continuous_jf Sf).comp continuous_snd)

/-- extension of an S-idele by 1 -/
noncomputable def jS : SIdeleGroup F Sf →* IdeleGroup F := Units.map (J Sf)

theorem continuous_jS : Continuous (jS (F := F) Sf) := (continuous_J Sf).units_map _

theorem fc_jS_of_notMem (y : SIdeleGroup F Sf) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Sf) :
    fc v (jS Sf y) = 1 := by
  show jf Sf (y : SAdeleRing F Sf).2 v = 1
  rw [jf_apply, jfFun_neg Sf _ v hv]

theorem jS_mem (y : SIdeleGroup F Sf) : jS Sf y ∈ sIntegralIdeles Sf := by
  intro v hv
  have := fc_jS_of_notMem Sf y v hv
  rw [fc_apply] at this
  rw [this, map_one]

theorem restrict_jS (y : SIdeleGroup F Sf) : sIdeleRestrict Sf (jS Sf y) = y := by
  ext1
  apply Prod.ext
  · rfl
  · funext v
    show jf Sf (y : SAdeleRing F Sf).2 v = (y : SAdeleRing F Sf).2 v
    rw [jf_apply, jfFun_pos Sf _ v v.2]

end Ext

section Pieces
variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- the idele `∏ π_v ^ n_v` -/
noncomputable def P (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) : IdeleGroup F :=
  SolEuler.mw (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} => ideleSingle v.1 (unif v.1)) n

theorem fc_P_out (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ Sf) :
    fc w (P Sf n) = ((unif w : (w.adicCompletion F)ˣ) : w.adicCompletion F) ^ (n ⟨w, hw⟩) := by
  unfold P SolEuler.mw Finsupp.prod
  rw [map_prod]
  simp_rw [map_pow]
  rw [Finset.prod_eq_single ⟨w, hw⟩]
  · rw [fc_ideleSingle_same]
  · intro b _ hb
    rw [fc_ideleSingle_ne _ _ (fun h => hb (Subtype.ext h.symm)), one_pow]
  · intro hnot
    simp [Finsupp.notMem_support_iff.mp hnot]

theorem fc_P_in (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∈ Sf) : fc w (P Sf n) = 1 := by
  unfold P SolEuler.mw Finsupp.prod
  rw [map_prod]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [map_pow]
  dsimp only
  rw [fc_ideleSingle_ne _ _ (fun h => b.2 (by rw [← h]; exact hw)), one_pow]

theorem ic_P (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) (w : InfinitePlace F) :
    ic w (P Sf n) = 1 := by
  unfold P SolEuler.mw Finsupp.prod
  rw [map_prod]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [map_pow, ic_ideleSingle, one_pow]

theorem val_fc_P_out (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ Sf) : Valued.v (fc w (P Sf n)) = WithZero.exp (-(n ⟨w, hw⟩ : ℤ)) := by
  rw [fc_P_out Sf n w hw, map_pow, unif_spec, ← WithZero.exp_nsmul]
  congr 1
  simp

/-- the pieces of the support -/
def E (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) : Set (IdeleGroup F) :=
  {g | (P Sf n)⁻¹ * g ∈ sIntegralIdeles Sf}

theorem mem_E (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) (g : IdeleGroup F) :
    g ∈ E Sf n ↔ ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf},
      Valued.v (fc v.1 g) = WithZero.exp (-(n v : ℤ)) := by
  unfold E sIntegralIdeles
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h v
    have h1 := h v.1 v.2
    rw [← fc_apply, map_mul, map_inv, map_mul, map_inv₀, val_fc_P_out Sf n v.1 v.2] at h1
    rw [eq_inv_of_mul_eq_one_right h1, inv_inv]
  · intro h v hv
    rw [← fc_apply, map_mul, map_inv, map_mul, map_inv₀, val_fc_P_out Sf n v hv, h ⟨v, hv⟩,
      inv_mul_cancel₀ WithZero.exp_ne_zero]

theorem E_disjoint : Pairwise (Function.onFun Disjoint (E (F := F) Sf)) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  intro g hn hm
  apply hnm
  ext v
  have h1 := (mem_E Sf n g).mp hn v
  have h2 := (mem_E Sf m g).mp hm v
  rw [h1, WithZero.exp_inj, neg_inj] at h2
  exact_mod_cast h2


theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
    ext I; simp
  have : (Set.univ : Set (Ideal (𝓞 F))).Countable := by
    rw [h]
    exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
  exact Set.countable_univ_iff.mp this

instance countable_hos : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI := countable_ideal (F := F)
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h)

theorem continuous_fc (v : HeightOneSpectrum (𝓞 F)) : Continuous (fc (F := F) v) :=
  (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)

theorem isClosed_U : IsClosed (sIntegralIdeles (F := F) Sf) := by
  have : sIntegralIdeles (F := F) Sf =
      ⋂ v ∈ {v : HeightOneSpectrum (𝓞 F) | v ∉ Sf}, {g : IdeleGroup F | ‖fc v g‖ = 1} := by
    ext g
    simp only [sIntegralIdeles, Set.mem_setOf_eq, Set.mem_iInter, norm_eq_one_iff, fc_apply]
  rw [this]
  exact isClosed_biInter fun v _ =>
    isClosed_eq (continuous_fc v).norm continuous_const

theorem measurableSet_U : MeasurableSet (sIntegralIdeles (F := F) Sf) :=
  (isClosed_U Sf).measurableSet

theorem measurableSet_E (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) :
    MeasurableSet (E (F := F) Sf n) :=
  ((isClosed_U Sf).preimage (continuous_const.mul continuous_id)).measurableSet

/-- Every idele integral outside `S` lies in some piece. -/
theorem exists_E (g : IdeleGroup F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) :
    ∃ n, g ∈ E Sf n := by
  classical
  have h0 : ∀ v : HeightOneSpectrum (𝓞 F), fc v g ≠ 0 := fun v h => by
    have := congrArg (fc v) (mul_inv_cancel g)
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hfin : {v : HeightOneSpectrum (𝓞 F) | Valued.v (fc v g) ≠ 1}.Finite := by
    have h1 := ((g : AdeleRing (𝓞 F) F).2).2
    have h2 := (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2).2
    have h3 := Filter.eventually_cofinite.mp (h1.and h2)
    refine h3.subset fun v hv => ?_
    simp only [Set.mem_setOf_eq] at hv ⊢
    intro ⟨ha, hb⟩
    apply hv
    have ha' : Valued.v (fc v g) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ha
    have hb' : Valued.v (fc v g⁻¹) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hb
    rw [map_inv, map_inv₀] at hb'
    have hne : Valued.v (fc v g) ≠ 0 := (Valuation.ne_zero_iff _).mpr (h0 v)
    exact le_antisymm ha' ((inv_le_one₀ (pos_iff_ne_zero.mpr hne)).mp hb')
  let k : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} → ℕ :=
    fun v => (-(WithZero.log (Valued.v (fc v.1 g)))).toNat
  have hk : (Function.support k).Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun v hv => ?_
    simp only [Function.mem_support, Set.mem_preimage, Set.mem_setOf_eq] at hv ⊢
    intro h1
    apply hv
    simp [k, h1]
  refine ⟨Finsupp.ofSupportFinite k hk, ?_⟩
  rw [mem_E]
  intro v
  have hne : Valued.v (fc v.1 g) ≠ 0 := (Valuation.ne_zero_iff _).mpr (h0 v.1)
  have hle : Valued.v (fc v.1 g) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hg v.1 v.2)
  have hlog : WithZero.log (Valued.v (fc v.1 g)) ≤ 0 := by
    rw [← WithZero.log_one, WithZero.log_le_log hne one_ne_zero]
    exact hle
  rw [Finsupp.ofSupportFinite_coe]
  have : ((k v : ℕ) : ℤ) = -(WithZero.log (Valued.v (fc v.1 g))) := by
    simp only [k]
    rw [Int.toNat_of_nonneg (by omega)]
  rw [this, neg_neg, WithZero.exp_log hne]

end Pieces

section Compute
variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

theorem sAdeleRestrict_P_mul (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) (u : IdeleGroup F) :
    sAdeleRestrict Sf ((P Sf n * u : IdeleGroup F) : AdeleRing (𝓞 F) F) =
      sAdeleRestrict Sf (u : AdeleRing (𝓞 F) F) := by
  have h1 : sAdeleRestrict Sf ((P Sf n : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := by
    rw [sAdeleRestrict_apply]
    apply Prod.ext
    · funext w
      exact ic_P Sf n w
    · funext v
      exact fc_P_in Sf n v v.2
  rw [Units.val_mul, map_mul, h1, one_mul]

theorem mem_A_P_mul (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) (u : IdeleGroup F)
    (hu : u ∈ sIntegralIdeles Sf) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Sf) :
    ((P Sf n * u : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← fc_apply, map_mul, map_mul,
    val_fc_P_out Sf n v hv, fc_apply, hu v hv, mul_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem norm_fc_of_mem (u : IdeleGroup F) (hu : u ∈ sIntegralIdeles Sf) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ Sf) : ‖fc v u‖ = 1 :=
  (norm_eq_one_iff v _).mpr (hu v hv)

theorem ideleNorm_P_mul (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) (u : IdeleGroup F)
    (hu : u ∈ sIntegralIdeles Sf) :
    ideleNorm (P Sf n * u) = sIdeleNorm Sf (sIdeleRestrict Sf u) *
      SolEuler.mw (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} =>
        ((Ideal.absNorm v.1.asIdeal : ℝ))⁻¹) n := by
  classical
  unfold ideleNorm sIdeleNorm
  have hinf : ∀ w : InfinitePlace F, ‖((P Sf n * u : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w‖ =
      ‖((sIdeleRestrict Sf u : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖ := by
    intro w
    rw [← ic_apply, map_mul, ic_P, one_mul]
    rfl
  simp_rw [hinf]
  rw [mul_assoc]
  congr 1
  have hsplit : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((P Sf n * u : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = ‖fc v u‖ * ‖fc v (P Sf n)‖ := by
    intro v
    rw [← fc_apply, map_mul, norm_mul, mul_comm]
  simp_rw [hsplit]
  have hα : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ‖fc v u‖) ⊆ (Sf : Set _) := by
    intro v hv
    by_contra h
    exact hv (norm_fc_of_mem Sf u hu v h)
  have hβ : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ‖fc v (P Sf n)‖) ⊆
      ((n.support.map (Function.Embedding.subtype _) : Finset (HeightOneSpectrum (𝓞 F))) :
        Set _) := by
    intro v hv
    by_cases h : v ∈ Sf
    · exfalso; apply hv; simp only; rw [fc_P_in Sf n v h, norm_one]
    · by_contra h2
      apply hv
      simp only
      have : n ⟨v, h⟩ = 0 := by
        by_contra h3
        apply h2
        simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe,
          Finsupp.mem_support_iff]
        exact ⟨⟨v, h⟩, h3, rfl⟩
      rw [fc_P_out Sf n v h, this, pow_zero, norm_one]
  rw [finprod_mul_distrib ((Sf.finite_toSet).subset hα) ((Finset.finite_toSet _).subset hβ),
    finprod_eq_prod_of_mulSupport_subset _ hα, finprod_eq_prod_of_mulSupport_subset _ hβ,
    Finset.prod_map]
  congr 1
  · rw [← Finset.prod_coe_sort Sf]
    rfl
  · unfold SolEuler.mw Finsupp.prod
    refine Finset.prod_congr rfl fun v _ => ?_
    change ‖fc v.1 (P Sf n)‖ = _
    rw [fc_P_out Sf n v.1 v.2, norm_pow, norm_unif]

theorem cpow_pow_ofReal {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (s : ℂ) :
    (((x ^ k : ℝ)) : ℂ) ^ s = ((x : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg hx _) hx, ih,
      pow_succ]

theorem cpow_mw {ι : Type*} (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (n : ι →₀ ℕ) (s : ℂ) :
    ((SolEuler.mw x n : ℝ) : ℂ) ^ s = SolEuler.mw (fun i => ((x i : ℝ) : ℂ) ^ s) n := by
  classical
  unfold SolEuler.mw Finsupp.prod
  induction n.support using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (pow_nonneg (hx i) _)
        (Finset.prod_nonneg fun j _ => pow_nonneg (hx j) _), ih, cpow_pow_ofReal (hx i)]

theorem ofReal_inv_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hx.le]
  exact Real.pi_pos.ne

theorem mw_mul {ι R : Type*} [CommMonoid R] (a c : ι → R) (n : ι →₀ ℕ) :
    SolEuler.mw (fun i => a i * c i) n = SolEuler.mw a n * SolEuler.mw c n := by
  unfold SolEuler.mw Finsupp.prod
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _

/-- The character as a monoid homomorphism on ideles. -/
noncomputable def chi (χ : HeckeCharacter F) : IdeleGroup F →* ℂ where
  toFun g := ((χ (QuotientGroup.mk g) : Circle) : ℂ)
  map_one' := by simp
  map_mul' g h := by simp

theorem chi_apply (χ : HeckeCharacter F) (g : IdeleGroup F) :
    chi χ g = ((χ (QuotientGroup.mk g) : Circle) : ℂ) := rfl

theorem chi_P (χ : HeckeCharacter F)
    (hχ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → χ.IsUnramifiedAt v)
    (n : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} →₀ ℕ) :
    chi χ (P Sf n) = SolEuler.mw (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} =>
      χ.primeValue v.1) n := by
  unfold P
  rw [SolEuler.mw_map]
  congr 1
  funext v
  rw [primeValue_eq χ v.1 (hχ v.1 v.2)]
  rfl

end Compute

end SolInfra

namespace SolMain
open MasulloGRH SolInfra

variable {F : Type*} [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))

noncomputable def Cst : ℝ≥0∞ := (ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|))⁻¹ *
  ∏ v ∈ Sf, ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
    multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))

theorem Cst_ne_top : Cst Sf ≠ ⊤ := by
  unfold Cst
  apply ENNReal.mul_ne_top
  · rw [ENNReal.inv_ne_top]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    apply Real.sqrt_pos.mpr
    apply abs_pos.mpr
    exact_mod_cast NumberField.discr_ne_zero F
  · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

theorem Cst_toReal : (Cst Sf).toReal = (Real.sqrt |(discr F : ℝ)|)⁻¹ *
    ∏ v ∈ Sf, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))) := by
  unfold Cst
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_prod]
  congr 1
  exact Finset.prod_congr rfl fun v _ => ENNReal.toReal_ofReal (Real.sqrt_nonneg _)

theorem continuous_r : Continuous (sIdeleRestrict (F := F) Sf) := by
  have : Continuous (sAdeleRestrict (F := F) Sf) := by
    have h : (fun x : AdeleRing (𝓞 F) F => sAdeleRestrict Sf x) =
        fun x => (x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) := rfl
    rw [show ((sAdeleRestrict (F := F) Sf : AdeleRing (𝓞 F) F → SAdeleRing F Sf)) =
      fun x => (x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) from h]
    exact continuous_fst.prodMk
      (continuous_pi fun v => (RestrictedProduct.continuous_eval v.1).comp continuous_snd)
  exact this.units_map _

theorem map_restrict :
    ((tamagawaIdele F).restrict (sIntegralIdeles Sf)).map (sIdeleRestrict Sf) =
      Cst Sf • sMultiplicativeTamagawa F Sf := by
  ext B hB
  rw [Measure.map_apply (continuous_r Sf).measurable hB,
    Measure.restrict_apply ((continuous_r Sf).measurable hB), Measure.smul_apply, smul_eq_mul,
    mul_comm, Cst, ← tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa F Sf B hB]
  congr 1
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hB', hU⟩
    exact ⟨hU, _, hB', rfl⟩
  · rintro ⟨hU, b, hb, he⟩
    refine ⟨?_, hU⟩
    have : sIdeleRestrict Sf g = b := Units.ext he.symm
    rw [this]
    exact hb

theorem continuous_chi (χ : HeckeCharacter F) : Continuous (chi χ) := by
  have h1 : Continuous fun g : IdeleGroup F => χ (QuotientGroup.mk g) :=
    χ.continuous.comp continuous_quot_mk
  exact continuous_subtype_val.comp h1

theorem norm_chi (χ : HeckeCharacter F) (g : IdeleGroup F) : ‖chi χ g‖ = 1 :=
  Circle.norm_coe _


theorem sIdeleNorm_nonneg (y : SIdeleGroup F Sf) : 0 ≤ sIdeleNorm Sf y := by
  unfold sIdeleNorm
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem mw_nonneg {ι : Type*} (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (n : ι →₀ ℕ) :
    0 ≤ SolEuler.mw x n :=
  Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm v.asIdeal :=
  lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)

theorem main (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (fS : SAdelicSchwartz F Sf) (χ : HeckeCharacter F)
    (hχ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → χ.IsUnramifiedAt v)
    (χS : SIdeleGroup F Sf → ℂ)
    (hχS : ∀ g : IdeleGroup F, g ∈ sIntegralIdeles Sf →
      χS (sIdeleRestrict Sf g) = ((χ (QuotientGroup.mk g) : Circle) : ℂ))
    (s : ℂ) (hs : 1 < s.re) :
    Integrable
      (fun g : IdeleGroup F =>
        Set.indicator
          {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
            x.2 v ∈ v.adicCompletionIntegers F}
          (fun x : AdeleRing (𝓞 F) F => fS.eval (sAdeleRestrict Sf x)) (g : AdeleRing (𝓞 F) F) *
          quasiTwist (fun g : IdeleGroup F => ((χ (QuotientGroup.mk g) : Circle) : ℂ)) s g)
      (tamagawaIdele F) ∧
    zetaIntegralFun
        (Set.indicator
          {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
            x.2 v ∈ v.adicCompletionIntegers F}
          (fun x : AdeleRing (𝓞 F) F => fS.eval (sAdeleRestrict Sf x)))
        (quasiTwist (fun g : IdeleGroup F => ((χ (QuotientGroup.mk g) : Circle) : ℂ)) s) =
      sZetaIntegral fS (sQuasiTwist Sf χS s) *
        (((Real.sqrt |(discr F : ℝ)|)⁻¹ *
          ∏ v ∈ Sf, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))) : ℝ) : ℂ) *
        ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf},
          (1 - χ.primeValue (v : HeightOneSpectrum (𝓞 F)) *
            ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  classical
  haveI : (tamagawaIdele F).IsHaarMeasure := (tamagawa_measures_wellDefined F).2.1.1
  set μ := tamagawaIdele F with hμ
  set U := sIntegralIdeles Sf with hU
  set A : Set (AdeleRing (𝓞 F) F) := {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
    v ∉ Sf → x.2 v ∈ v.adicCompletionIntegers F} with hA
  set H : IdeleGroup F → ℂ := fun g : IdeleGroup F =>
    A.indicator (fun x : AdeleRing (𝓞 F) F => fS.eval (sAdeleRestrict Sf x))
      (g : AdeleRing (𝓞 F) F) *
      quasiTwist (fun g : IdeleGroup F => ((χ (QuotientGroup.mk g) : Circle) : ℂ)) s g with hH
  set G : SIdeleGroup F Sf → ℂ := fun y => fS.eval (y : SAdeleRing F Sf) * sQuasiTwist Sf χS s y
    with hG
  set b : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} → ℂ := fun v =>
    χ.primeValue v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) with hb
  set K : IdeleGroup F → ℂ := U.indicator (fun u => G (sIdeleRestrict Sf u)) with hK
  -- the S-local character
  have hχS' : ∀ y, χS y = chi χ (jS Sf y) := fun y => by
    have := hχS (jS Sf y) (jS_mem Sf y)
    rwa [restrict_jS] at this
  have hqc : IsSIdeleQuasiCharacter Sf χS := by
    refine ⟨?_, ?_, ?_⟩
    · have : χS = fun y => chi χ (jS Sf y) := funext hχS'
      rw [this]
      exact (continuous_chi χ).comp (continuous_jS Sf)
    · intro g h
      rw [hχS', hχS', hχS', map_mul, map_mul]
    · intro g h
      have := norm_chi χ (jS Sf g)
      rw [← hχS', h, norm_zero] at this
      exact zero_ne_one this
  have hGint : Integrable G (sMultiplicativeTamagawa F Sf) :=
    (sZetaIntegral_integrable_and_differentiableOn F Sf fS χS hqc 0
      (fun g => by rw [hχS', norm_chi, Real.rpow_zero])).1 s (by linarith)
  -- the function K on the S-integral ideles
  have hmap := map_restrict Sf
  have hrm : AEMeasurable (sIdeleRestrict Sf) (μ.restrict U) :=
    (continuous_r Sf).measurable.aemeasurable
  have hGint' : Integrable G (Measure.map (sIdeleRestrict Sf) (μ.restrict U)) := by
    rw [hmap]
    exact hGint.smul_measure (Cst_ne_top Sf)
  have hGm : AEStronglyMeasurable G (Measure.map (sIdeleRestrict Sf) (μ.restrict U)) :=
    hGint'.aestronglyMeasurable
  have hKU : IntegrableOn (fun u => G (sIdeleRestrict Sf u)) U μ :=
    (integrable_map_measure hGm hrm).mp hGint'
  have hKi : Integrable K μ := (integrable_indicator_iff (measurableSet_U Sf)).mpr hKU
  have hKint : ∫ u, K u ∂μ = (Cst Sf).toReal • sZetaIntegral fS (sQuasiTwist Sf χS s) := by
    rw [hK, integral_indicator (measurableSet_U Sf), ← integral_map hrm hGm, hmap,
      integral_smul_measure]
    rfl
  -- the pointwise identity
  have hHP : ∀ n u, u ∈ U → H (P Sf n * u) = SolEuler.mw b n * G (sIdeleRestrict Sf u) := by
    intro n u hu
    have hmem : ((P Sf n * u : IdeleGroup F) : AdeleRing (𝓞 F) F) ∈ A :=
      fun v hv => mem_A_P_mul Sf n u hu v hv
    show A.indicator (fun x : AdeleRing (𝓞 F) F => fS.eval (sAdeleRestrict Sf x))
        ((P Sf n * u : IdeleGroup F) : AdeleRing (𝓞 F) F) *
        (chi χ (P Sf n * u) * ((ideleNorm (P Sf n * u) : ℝ) : ℂ) ^ s) =
      SolEuler.mw b n * (fS.eval (sAdeleRestrict Sf (u : AdeleRing (𝓞 F) F)) *
        (χS (sIdeleRestrict Sf u) * ((sIdeleNorm Sf (sIdeleRestrict Sf u) : ℝ) : ℂ) ^ s))
    rw [Set.indicator_of_mem hmem, sAdeleRestrict_P_mul, ideleNorm_P_mul Sf n u hu, map_mul,
      chi_P Sf χ hχ, chi_apply, ← hχS u hu, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (sIdeleNorm_nonneg Sf _)
        (mw_nonneg _ (fun v => inv_nonneg.mpr (Nat.cast_nonneg _)) n),
      cpow_mw _ (fun v => inv_nonneg.mpr (Nat.cast_nonneg _))]
    have hq : (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf} =>
        ((((Ideal.absNorm v.1.asIdeal : ℝ))⁻¹ : ℝ) : ℂ) ^ s) =
        fun v => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) := by
      funext v
      rw [ofReal_inv_cpow (by exact_mod_cast absNorm_pos v.1), Complex.ofReal_natCast]
    rw [hq, hb, mw_mul]
    ring
  have hind : ∀ n g, (E Sf n).indicator H g = SolEuler.mw b n * K ((P Sf n)⁻¹ * g) := by
    intro n g
    by_cases hg : g ∈ E Sf n
    · have hu : (P Sf n)⁻¹ * g ∈ U := hg
      rw [Set.indicator_of_mem hg, hK, Set.indicator_of_mem hu]
      have := hHP n _ hu
      rwa [mul_inv_cancel_left] at this
    · have hu : (P Sf n)⁻¹ * g ∉ U := hg
      rw [Set.indicator_of_notMem hg, hK, Set.indicator_of_notMem hu, mul_zero]
  -- pieces
  have hEint : ∀ n, IntegrableOn H (E Sf n) μ := fun n => by
    rw [← integrable_indicator_iff (measurableSet_E Sf n)]
    have : (E Sf n).indicator H = fun g => SolEuler.mw b n * K ((P Sf n)⁻¹ * g) :=
      funext (hind n)
    rw [this]
    exact (hKi.comp_mul_left (P Sf n)⁻¹).const_mul _
  have hEset : ∀ n, ∫ g in E Sf n, H g ∂μ =
      SolEuler.mw b n * ((Cst Sf).toReal • sZetaIntegral fS (sQuasiTwist Sf χS s)) := fun n => by
    rw [← integral_indicator (measurableSet_E Sf n)]
    have : (E Sf n).indicator H = fun g => SolEuler.mw b n * K ((P Sf n)⁻¹ * g) :=
      funext (hind n)
    rw [this, integral_const_mul, integral_mul_left_eq_self K (P Sf n)⁻¹, hKint]
  have hEnorm : ∀ n, ∫ g in E Sf n, ‖H g‖ ∂μ = ‖SolEuler.mw b n‖ * ∫ g, ‖K g‖ ∂μ := fun n => by
    rw [← integral_indicator (measurableSet_E Sf n)]
    have : (E Sf n).indicator (fun g => ‖H g‖) =
        fun g => ‖SolEuler.mw b n‖ * ‖K ((P Sf n)⁻¹ * g)‖ := by
      funext g
      rw [← norm_indicator_eq_indicator_norm, hind, norm_mul]
    rw [this, integral_const_mul, integral_mul_left_eq_self (fun g => ‖K g‖) (P Sf n)⁻¹]
  -- Euler product
  have hbn : ∀ v, ‖b v‖ = ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s.re) := fun v => by
    simp only [hb]
    rw [norm_mul, primeValue_eq χ v.1 (hχ v.1 v.2), HeckeCharacter.localComponent,
      Circle.norm_coe, one_mul, Complex.norm_natCast_cpow_of_pos (absNorm_pos v.1),
      Complex.neg_re]
  have hbsum : Summable fun v => ‖b v‖ := by
    simp_rw [hbn]
    exact (SolEuler.summable_prime_rpow F hs).comp_injective Subtype.val_injective
  have hb2 : ∀ v, ‖b v‖ ≤ 1 / 2 := fun v => by
    rw [hbn, Real.rpow_neg (Nat.cast_nonneg _)]
    have hq2 : (2 : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.1
    have h1 : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ s.re := by
      calc ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) = ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (1 : ℝ) :=
            (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
    rw [one_div]
    exact inv_anti₀ (by norm_num) (hq2.trans h1)
  have hs_mw : Summable fun n => ‖SolEuler.mw b n‖ := SolEuler.summable_norm_mw b hbsum hb2
  have hprod := SolEuler.hasProd_mw b hs_mw (fun v h => by
    have := hb2 v
    rw [h, norm_one] at this
    norm_num at this)
  -- union of the pieces
  have hUnion : IntegrableOn H (⋃ n, E Sf n) μ :=
    integrableOn_iUnion_of_summable_integral_norm hEint
      (by simp_rw [hEnorm]; exact hs_mw.mul_right _)
  have hsupp : Function.support H ⊆ ⋃ n, E Sf n := by
    intro g hg
    have hA' : (g : AdeleRing (𝓞 F) F) ∈ A := by
      by_contra h
      apply hg
      simp only [hH]
      rw [Set.indicator_of_notMem h, zero_mul]
    obtain ⟨n, hn⟩ := exists_E Sf g hA'
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hHint : Integrable H μ := (integrableOn_iff_integrable_of_support_subset hsupp).mp hUnion
  refine ⟨hHint, ?_⟩
  show ∫ g, H g ∂μ = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ⋃ n, E Sf n)
      (fun g hg => by
        by_contra h
        exact hg (hsupp h)),
    integral_iUnion (measurableSet_E Sf) (E_disjoint Sf) hUnion]
  simp_rw [hEset]
  rw [tsum_mul_right, ← hprod.tprod_eq, Complex.real_smul, Cst_toReal]
  ring

end SolMain

end Sol_MasulloGRH_zetaIntegral_eq_sZetaIntegral_mul_partialEulerProduct

open MasulloGRH in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (fS : SAdelicSchwartz F Sf) (χ : HeckeCharacter F)
    (hχ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → χ.IsUnramifiedAt v)
    (χS : SIdeleGroup F Sf → ℂ)
    (hχS : ∀ g : IdeleGroup F, g ∈ sIntegralIdeles Sf →
      χS (sIdeleRestrict Sf g) = ((χ (QuotientGroup.mk g) : Circle) : ℂ))
    (s : ℂ) (hs : 1 < s.re) :
    Integrable
      (fun g : IdeleGroup F =>
        Set.indicator
          {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
            x.2 v ∈ v.adicCompletionIntegers F}
          (fun x : AdeleRing (𝓞 F) F => fS.eval (sAdeleRestrict Sf x)) (g : AdeleRing (𝓞 F) F) *
          quasiTwist (fun g : IdeleGroup F => ((χ (QuotientGroup.mk g) : Circle) : ℂ)) s g)
      (tamagawaIdele F) ∧
    zetaIntegralFun
        (Set.indicator
          {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
            x.2 v ∈ v.adicCompletionIntegers F}
          (fun x : AdeleRing (𝓞 F) F => fS.eval (sAdeleRestrict Sf x)))
        (quasiTwist (fun g : IdeleGroup F => ((χ (QuotientGroup.mk g) : Circle) : ℂ)) s) =
      sZetaIntegral fS (sQuasiTwist Sf χS s) *
        (((Real.sqrt |(discr F : ℝ)|)⁻¹ *
          ∏ v ∈ Sf, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))) : ℝ) : ℂ) *
        ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf},
          (1 - χ.primeValue (v : HeightOneSpectrum (𝓞 F)) *
            ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ :=
  Sol_MasulloGRH_zetaIntegral_eq_sZetaIntegral_mul_partialEulerProduct.SolMain.main F Sf fS χ hχ χS hχS s hs
