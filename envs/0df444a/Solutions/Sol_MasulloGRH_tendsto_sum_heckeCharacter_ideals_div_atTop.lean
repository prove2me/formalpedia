-- Prove2me | solution 1 for MasulloGRH.tendsto_sum_heckeCharacter_ideals_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:36:46.438446+00:00
-- url     : https://prove2.me/submissions/72408f0f-d45b-4450-864d-b6e9625c3f33

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm
import Theorems.Thm_TauCeti_LSeries_wienerIkehara
import Theorems.Thm_TauCeti_exists_differentiableOn_eq_LSeries_ofBadPrimes_sub
import Theorems.Thm_TauCeti_LSeriesSummable_normCoeff_one_iff
import Theorems.Thm_MasulloGRH_heckeLFunction_logDeriv_bound_in_zero_free_region
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation

open Filter Topology NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_tendsto_sum_heckeCharacter_ideals_div_atTop

open MasulloGRH
open scoped nonZeroDivisors

theorem hasProd_eulerFactors_of_summable {M ι : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]
    (P : ι → M) (hp : ∀ i, Prime (P i)) (hd : ∀ i j, P i ∣ P j → i = j)
    (hc : ∀ x : M, x ≠ 0 → x ≠ 1 → ∃ i, P i ∣ x) (f : M →*₀ ℂ)
    (hs : Summable fun x ↦ ‖f x‖) (h₁ : ∀ i, f (P i) ≠ 1) :
    HasProd (fun i ↦ (1 - f (P i))⁻¹) (∑' x, f x) := by
  classical
  let good (S : Finset ι) := {x : M | ∀ i ∈ S, ¬ P i ∣ x}
  let w (S : Finset ι) := (good S).indicator (f : M → ℂ)
  let R (S : Finset ι) := ∑' x, w S x
  have hsum (S) : Summable (w S) := (Summable.of_norm (f := fun x : M ↦ f x) hs).indicator _
  have hrec (S : Finset ι) (p : ι) (hpS : p ∉ S) :
      R (insert p S) = (1 - f (P p)) * R S := by
    let d := {x : M | P p ∣ x}.indicator (w S)
    have hdiff (x) : w (insert p S) x = w S x - d x := by
      by_cases h : P p ∣ x
      · have hbad : x ∉ good (insert p S) := fun hx ↦ hx p (Finset.mem_insert_self _ _) h
        simp [w, d, h, hbad]
      · have hiff : x ∈ good (insert p S) ↔ x ∈ good S := by simp [good, h]
        simp only [w, d, Set.indicator_apply, Set.mem_ofPred_eq, h, ite_false, sub_zero, hiff]
    have hcomp (x) : d (P p * x) = f (P p) * w S x := by
      have hiff : P p * x ∈ good S ↔ x ∈ good S := by
        constructor
        · exact fun hx i hi hix ↦ hx i hi (dvd_mul_of_dvd_right hix _)
        · intro hx i hi hdvd
          rcases (hp i).dvd_or_dvd hdvd with hip | hix
          · exact hpS (hd i p hip ▸ hi)
          · exact hx i hi hix
      simp only [d, w, Set.indicator_apply, Set.mem_ofPred_eq, dvd_mul_right, ite_true,
        hiff, map_mul, mul_ite, mul_zero]
    have hdv : Function.support d ⊆ Set.range (fun x ↦ P p * x) := by
      intro x hx
      by_contra hn
      have h : ¬ P p ∣ x := fun ⟨a, ha⟩ ↦ hn ⟨a, ha.symm⟩
      exact hx (by simp [d, h])
    have hinj : Function.Injective (fun x ↦ P p * x) := fun _ _ ↦ mul_left_cancel₀ (hp p).ne_zero
    have hsumd : (∑' x, d x) = f (P p) * R S := by
      rw [← hinj.tsum_eq hdv, tsum_congr hcomp, tsum_mul_left]
    change (∑' x, w (insert p S) x) = _
    rw [tsum_congr hdiff, (hsum S).tsum_sub ((hsum S).indicator _), hsumd]
    change R S - f (P p) * R S = _
    ring
  have hfinite (S : Finset ι) :
      (∏ i ∈ S, (1 - f (P i))⁻¹) * R S = ∑' x, f x := by
    induction S using Finset.induction_on with
    | empty => simp [R, w, good]
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, hrec S i hi, ← ih]
      have hn : 1 - f (P i) ≠ 0 := sub_ne_zero.mpr (h₁ i).symm
      field_simp [hn]
  have hlim : Tendsto R atTop (𝓝 1) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := w)
      (g := fun x : M ↦ if x = 1 then (1 : ℂ) else 0) hs
    have hx (x : M) : Tendsto (fun S ↦ w S x) atTop (𝓝 (if x = 1 then (1 : ℂ) else 0)) := by
      apply tendsto_const_nhds.congr'
      by_cases h : x = 1
      · subst x
        exact .of_forall fun S ↦ by simp [w, good, fun i ↦ (hp i).not_dvd_one]
      by_cases h0 : x = 0
      · subst x
        exact .of_forall fun S ↦ by simp [w, Set.indicator_apply, h]
      obtain ⟨i, hi⟩ := hc x h0 h
      filter_upwards [Filter.eventually_ge_atTop {i}] with S hiS
      have hiS' : i ∈ S := hiS (Finset.mem_singleton_self i)
      have hbad : x ∉ good S := fun hs ↦ hs i hiS' hi
      simp [w, hbad, h]
    have hb (S : Finset ι) (x : M) : ‖w S x‖ ≤ ‖f x‖ := by
      by_cases hx : x ∈ good S <;> simp [w, hx]
    simpa [R] using h hx (.of_forall hb)
  have hn := hlim.eventually_ne (one_ne_zero : (1 : ℂ) ≠ 0)
  have h := (tendsto_const_nhds (x := ∑' x, f x)).div hlim (by norm_num)
  rw [div_one] at h
  apply h.congr'
  filter_upwards [hn] with S hS
  exact (div_eq_iff hS).mpr (hfinite S).symm


variable {F : Type*} [Field F] [NumberField F]

/-- `χ(I)` as in the target. -/
noncomputable def idealVal (χ : HeckeCharacter F) (I : Ideal (𝓞 F)) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    χ.primeValue v ^ Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)

theorem count_eq_multiplicity (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) =
      multiplicity v.asIdeal I := by
  have h := UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors v.irreducible hI
  rw [normalize_eq] at h
  exact h.symm

theorem idealVal_eq (χ : HeckeCharacter F) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    idealVal χ I = ∏ᶠ v : HeightOneSpectrum (𝓞 F), χ.primeValue v ^ multiplicity v.asIdeal I := by
  unfold idealVal
  exact finprod_congr fun v ↦ by rw [count_eq_multiplicity v hI]

theorem norm_primeValue_le (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    ‖χ.primeValue v‖ ≤ 1 := by
  unfold HeckeCharacter.primeValue
  split_ifs with h
  · unfold HeckeCharacter.localComponent
    rw [Circle.norm_coe]
  · simp

open Classical in
/-- `χ(I)` for `I ≠ 0`, and `0` at `I = 0`, as a monoid-with-zero homomorphism. -/
noncomputable def idealHom (χ : HeckeCharacter F) : Ideal (𝓞 F) →*₀ ℂ :=
  let a : HeightOneSpectrum (𝓞 F) → ℂ := χ.primeValue
  let factor (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) := a v ^ multiplicity v.asIdeal I
  have hsupport (I : Ideal (𝓞 F)) (hI : I ≠ 0) : (factor I).HasFiniteMulSupport :=
    UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity a
      HeightOneSpectrum.asIdeal_injective HeightOneSpectrum.irreducible hI
  { toFun := fun I ↦ if I = 0 then 0 else ∏ᶠ v, factor I v
    map_zero' := by simp
    map_one' := by
      rw [if_neg one_ne_zero]
      exact finprod_eq_one_of_forall_eq_one fun v ↦ by
        simp only [factor, multiplicity_of_one_right v.prime.not_isUnit, pow_zero]
    map_mul' := by
      intro I J
      by_cases hI : I = 0
      · simp [hI]
      by_cases hJ : J = 0
      · simp [hJ]
      rw [if_neg (mul_ne_zero hI hJ), if_neg hI, if_neg hJ,
        ← finprod_mul_distrib (hsupport I hI) (hsupport J hJ)]
      apply finprod_congr
      intro v
      simp only [factor, multiplicity_mul v.prime
        (FiniteMultiplicity.of_prime_left v.prime (mul_ne_zero hI hJ)), pow_add] }

theorem idealHom_apply (χ : HeckeCharacter F) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    idealHom χ I = idealVal χ I := by
  rw [idealVal_eq χ hI]
  show (if I = 0 then 0 else _) = _
  rw [if_neg (by simpa using hI)]

theorem idealHom_prime (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    idealHom χ v.asIdeal = χ.primeValue v := by
  have hd (v w : HeightOneSpectrum (𝓞 F)) (h : v.asIdeal ∣ w.asIdeal) : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
  show (if v.asIdeal = 0 then 0 else _) = _
  rw [if_neg v.prime.ne_zero, finprod_eq_single _ v]
  · simp only [multiplicity_self, pow_one]
  · intro w hw
    simp only [multiplicity_eq_zero.mpr (fun h ↦ hw (hd w v h)), pow_zero]

theorem norm_idealHom_le (χ : HeckeCharacter F) (I : Ideal (𝓞 F)) : ‖idealHom χ I‖ ≤ 1 := by
  by_cases hI : I = 0
  · rw [hI, map_zero, norm_zero]
    exact zero_le_one
  show ‖(if I = 0 then 0 else _)‖ ≤ 1
  rw [if_neg hI, finprod_eq_prod _
    (UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity χ.primeValue
      HeightOneSpectrum.asIdeal_injective HeightOneSpectrum.irreducible hI), norm_prod]
  exact Finset.prod_le_one (fun v _ ↦ norm_nonneg _) fun v _ ↦ by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_primeValue_le χ v)


theorem fiber_finite (n : ℕ) : {I : Ideal (𝓞 F) | Ideal.absNorm I = n}.Finite :=
  Ideal.finite_setOfPred_absNorm_eq n

/-- The nonzero... ideals of norm `n` (for `n = 0`, only `⊥`). -/
noncomputable def fiber (F : Type*) [Field F] [NumberField F] (n : ℕ) : Finset (Ideal (𝓞 F)) :=
  (fiber_finite (F := F) n).toFinset

theorem mem_fiber {n : ℕ} {I : Ideal (𝓞 F)} : I ∈ fiber F n ↔ Ideal.absNorm I = n := by
  simp [fiber]

theorem hasSum_fiber {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (n : ℕ)
    (g : Ideal (𝓞 F) → E) :
    HasSum (fun I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n} ↦ g I.val) (∑ I ∈ fiber F n, g I) := by
  have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := (fiber_finite (F := F) n).to_subtype
  let : Fintype {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := Fintype.ofFinite _
  rw [Finset.sum_subtype (fiber F n) (fun I ↦ mem_fiber) g]
  exact hasSum_fintype _

/-- Number of ideals of norm `n`. -/
noncomputable def bcoef (F : Type*) [Field F] [NumberField F] (n : ℕ) : ℝ := ((fiber F n).card : ℝ)

/-- `∑_{N(I) = n} χ(I)`. -/
noncomputable def acoef (χ : HeckeCharacter F) (n : ℕ) : ℂ := ∑ I ∈ fiber F n, idealHom χ I

theorem bcoef_nonneg (n : ℕ) : 0 ≤ bcoef F n := Nat.cast_nonneg _

theorem norm_acoef_le (χ : HeckeCharacter F) (n : ℕ) : ‖acoef χ n‖ ≤ bcoef F n := by
  unfold acoef bcoef
  refine (norm_sum_le _ _).trans ?_
  calc ∑ I ∈ fiber F n, ‖idealHom χ I‖ ≤ ∑ I ∈ fiber F n, (1 : ℝ) :=
        Finset.sum_le_sum fun I _ ↦ norm_idealHom_le χ I
    _ = ((fiber F n).card : ℝ) := by simp

theorem normCoeff_eq_bcoef (f : TauCeti.IdealArithmeticFunction F) (hf : ∀ I, f I = 1)
    {n : ℕ} (hn : n ≠ 0) : (TauCeti.normCoeff F f) n = (bcoef F n : ℂ) := by
  have h1 : (TauCeti.normCoeff F f) n =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n}, f I := rfl
  have h2 : (∑ᶠ I ∈ {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n}, f I) =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n}, (1 : ℂ) :=
    finsum_mem_congr rfl fun I _ ↦ hf I
  have h3 := finsum_mem_image (f := fun _ : Ideal (𝓞 F) ↦ (1 : ℂ))
    (s := {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n})
    (g := Subtype.val) Subtype.val_injective.injOn
  have h4 : Subtype.val '' {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n} =
      {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
    ext J
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact hI
    · intro hJ
      have hJ0 : J ≠ 0 := by
        intro h
        apply hn
        rw [← (show Ideal.absNorm J = n from hJ), h]
        simp
      exact ⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩, hJ, rfl⟩
  rw [h1, h2, ← h3, h4, finsum_mem_eq_finite_toFinset_sum _ (fiber_finite (F := F) n)]
  simp [bcoef, fiber]


theorem LSeriesSummable_bcoef {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (bcoef F n : ℂ)) s := by
  have h := (TauCeti.LSeriesSummable_normCoeff_one_iff F (s := s)).mpr hs
  exact (LSeriesSummable_congr s fun {n} hn ↦ normCoeff_eq_bcoef 1 (fun _ ↦ rfl) hn).mp h

theorem summable_absNorm_rpow {r : ℝ} (hr : 1 < r) :
    Summable fun I : Ideal (𝓞 F) ↦ (Ideal.absNorm I : ℝ) ^ (-r) := by
  have hsum : Summable (fun n : ℕ ↦ bcoef F n * (n : ℝ) ^ (-r)) := by
    have h := (LSeriesSummable_bcoef (F := F) (s := (r : ℂ)) (by simpa using hr)).norm
    refine h.congr fun n ↦ ?_
    rw [LSeries.norm_term_eq]
    obtain rfl | hn := eq_or_ne n 0
    · simp [Real.zero_rpow (by linarith : -r ≠ 0)]
    · rw [if_neg hn, Complex.norm_real, Real.norm_of_nonneg (bcoef_nonneg n), Complex.ofReal_re,
        Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  rw [← (Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 F) → ℕ)).summable_iff]
  refine (summable_sigma_of_nonneg (fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)).2 ⟨fun n ↦ ?_, hsum.congr fun n ↦ ?_⟩
  · have : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} := (fiber_finite (F := F) n).to_subtype
    exact Summable.of_finite
  · show _ = ∑' y : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}, (Ideal.absNorm y.val : ℝ) ^ (-r)
    rw [(hasSum_fiber n (fun I : Ideal (𝓞 F) ↦ (Ideal.absNorm I : ℝ) ^ (-r))).tsum_eq,
      Finset.sum_congr rfl (fun I hI ↦ by rw [mem_fiber.mp hI]), Finset.sum_const, nsmul_eq_mul]
    rfl

theorem LSeriesHasSum_acoef (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (acoef χ) s (heckeEulerProduct χ s) := by
  let c := idealHom χ
  let term : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := fun I ↦ c I * ((Ideal.absNorm I : ℝ) : ℂ) ^ (-s)
      map_zero' := by rw [map_zero c, zero_mul]
      map_one' := by
        rw [map_one c, map_one, Nat.cast_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
      map_mul' := by
        intro I J
        rw [map_mul c, map_mul, Nat.cast_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        ring }
  have hbound (I : Ideal (𝓞 F)) : ‖term I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-s.re) := by
    by_cases hI : I = 0
    · rw [hI, map_zero, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hN : (0 : ℝ) < Ideal.absNorm I := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa using hI))
    change ‖c I * ((Ideal.absNorm I : ℝ) : ℂ) ^ (-s)‖ ≤ _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hN.le _) (norm_idealHom_le χ I)
  have hsum : Summable (fun I ↦ ‖term I‖) :=
    (summable_absNorm_rpow hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  have hd (v w : HeightOneSpectrum (𝓞 F)) (h : v.asIdeal ∣ w.asIdeal) : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
  have hprod := hasProd_eulerFactors_of_summable
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal) (fun v ↦ v.prime) hd
    (fun I hI h1 ↦ by
      obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal (by simpa only [Ideal.one_eq_top] using h1)
      exact ⟨⟨J, hJ.isPrime, fun h ↦ hI (le_bot_iff.mp (h ▸ hIJ))⟩, Ideal.dvd_iff_le.mpr hIJ⟩)
    term hsum (fun v ↦ by
      have hv : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hlt := (hbound v.asIdeal).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg hv (by linarith : -s.re < 0))
      exact fun h ↦ (ne_of_lt hlt) (by rw [h, norm_one]))
  have hlocal : (fun v : HeightOneSpectrum (𝓞 F) ↦ (1 - term v.asIdeal)⁻¹) =
      fun v ↦ (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
    funext v
    change (1 - c v.asIdeal * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s))⁻¹ = _
    rw [idealHom_prime, Complex.ofReal_natCast]
  rw [hlocal] at hprod
  have hEq : heckeEulerProduct χ s = ∑' I, term I := hprod.tprod_eq
  rw [hEq]
  let e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 F) → ℕ)
  have hS : HasSum (fun x ↦ term (e x)) (∑' I, term I) :=
    (e.hasSum_iff (f := fun I ↦ term I)).mpr hsum.of_norm.hasSum
  refine hS.sigma fun n ↦ ?_
  have hf := hasSum_fiber (F := F) n (fun I ↦ term I)
  have key : LSeries.term (acoef χ) s n = ∑ I ∈ fiber F n, term I := by
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      symm
      apply Finset.sum_eq_zero
      intro I hI
      have : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp (mem_fiber.mp hI)
      rw [this, ← Ideal.zero_eq_bot, map_zero]
    · rw [LSeries.term_of_ne_zero hn]
      unfold acoef
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro I hI
      change _ = c I * ((Ideal.absNorm I : ℝ) : ℂ) ^ (-s)
      rw [mem_fiber.mp hI, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
  rw [key]
  exact hf

theorem heckeLFunction_eq (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    heckeLFunction χ s = heckeEulerProduct χ s := by
  have h := heckeLFunction_exists_meromorphic_continuation F χ
  unfold heckeLFunction
  rw [dif_pos h]
  exact h.choose_spec.2 s hs

theorem continuousOn_heckeLFunction (χ : HeckeCharacter F) (hχ : ¬ χ.IsTrivialOnNormOne) :
    ContinuousOn (heckeLFunction χ) {s : ℂ | 1 ≤ s.re} := by
  obtain ⟨c, C, hc, h⟩ := (heckeLFunction_logDeriv_bound_in_zero_free_region F χ).1 hχ
  intro s hs
  have hlog : 0 < Real.log (|s.im| + 3) := Real.log_pos (by linarith [abs_nonneg s.im])
  have h1 : 1 - c / Real.log (|s.im| + 3) ≤ s.re := by
    have : 0 < c / Real.log (|s.im| + 3) := div_pos hc hlog
    have hs' : (1 : ℝ) ≤ s.re := hs
    linarith
  exact (h s h1).1.continuousAt.continuousWithinAt


open ComplexConjugate in
theorem conj_term (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    conj (LSeries.term f (conj s) n) = LSeries.term (fun m ↦ conj (f m)) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne),
      Complex.conj_conj, Complex.conj_natCast]

open ComplexConjugate in
theorem LSeriesHasSum_conj {f : ℕ → ℂ} {s a : ℂ} (h : LSeriesHasSum f (conj s) a) :
    LSeriesHasSum (fun m ↦ conj (f m)) s (conj a) := by
  have h' := Complex.hasSum_conj'.mpr h
  unfold LSeriesHasSum
  convert h' using 1
  funext n
  exact (conj_term f s n).symm

theorem exists_G0 : ∃ G0 : ℂ → ℂ, ContinuousOn G0 {s : ℂ | 1 ≤ s.re} ∧
    ∀ s : ℂ, 1 < s.re →
      G0 s = LSeries (fun n ↦ (bcoef F n : ℂ)) s - (dedekindZeta_residue F : ℂ) / (s - 1) := by
  obtain ⟨G, hG, hGs⟩ := TauCeti.exists_differentiableOn_eq_LSeries_ofBadPrimes_sub F ∅
  refine ⟨G, ?_, fun s hs ↦ ?_⟩
  · refine hG.continuousOn.mono fun s hs ↦ ?_
    have hd : (0 : ℝ) < 1 / (Module.finrank ℚ F : ℝ) := by
      have : 0 < Module.finrank ℚ F := Module.finrank_pos
      positivity
    show 1 - 1 / (Module.finrank ℚ F : ℝ) < s.re
    have : (1 : ℝ) ≤ s.re := hs
    linarith
  · rw [hGs s hs, Finset.prod_empty, mul_one]
    congr 1
    apply LSeries_congr
    intro n hn
    apply normCoeff_eq_bcoef _ _ hn
    intro I
    have hI : (I : Ideal (𝓞 F)) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero I
    rw [TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_apply,
      TauCeti.MultiplicativeIdealWeight.ofBadPrimes_apply, if_pos]
    exact ⟨hI, fun p hp ↦ absurd hp (by simp)⟩

open ComplexConjugate in
/-- The core asymptotic: `x⁻¹ ∑_{n ≤ x} a_n → 0`. -/
theorem tendsto_acoef (χ : HeckeCharacter F) (hχ : ¬ χ.IsTrivialOnNormOne) :
    Tendsto (fun x : ℝ ↦ (x : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, acoef χ n) atTop (𝓝 0) := by
  obtain ⟨G0, hG0, hG0s⟩ := exists_G0 (F := F)
  set ρ : ℝ := dedekindZeta_residue F
  have hB (s : ℂ) (hs : 1 < s.re) : LSeriesHasSum (fun n ↦ (bcoef F n : ℂ)) s
      (LSeries (fun n ↦ (bcoef F n : ℂ)) s) := (LSeriesSummable_bcoef hs).LSeriesHasSum
  have hA (s : ℂ) (hs : 1 < s.re) : LSeriesHasSum (acoef χ) s (heckeEulerProduct χ s) :=
    LSeriesHasSum_acoef χ hs
  have hAc (s : ℂ) (hs : 1 < s.re) : LSeriesHasSum (fun n ↦ conj (acoef χ n)) s
      (conj (heckeEulerProduct χ (conj s))) :=
    LSeriesHasSum_conj (hA (conj s) (by simpa using hs))
  have hH := continuousOn_heckeLFunction χ hχ
  have hHc : ContinuousOn (fun s ↦ conj (heckeLFunction χ (conj s))) {s : ℂ | 1 ≤ s.re} := by
    refine Complex.continuous_conj.comp_continuousOn
      (hH.comp Complex.continuous_conj.continuousOn fun s hs ↦ ?_)
    show 1 ≤ (conj s).re
    simpa using hs
  have hHe (s : ℂ) (hs : 1 < s.re) : heckeLFunction χ s = heckeEulerProduct χ s :=
    heckeLFunction_eq χ hs
  have hHce (s : ℂ) (hs : 1 < s.re) :
      heckeLFunction χ (conj s) = heckeEulerProduct χ (conj s) :=
    heckeLFunction_eq χ (by simpa using hs)
  -- the three Tauberian limits
  have hb : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, bcoef F n) atTop (𝓝 ρ) :=
    TauCeti.LSeries.wienerIkehara (fun n ↦ bcoef_nonneg n) hB hG0 hG0s
  have hre : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (bcoef F n + (acoef χ n).re))
      atTop (𝓝 ρ) := by
    refine TauCeti.LSeries.wienerIkehara
      (F := fun s ↦ LSeries (fun n ↦ (bcoef F n : ℂ)) s +
        (1 / 2 : ℂ) * (heckeEulerProduct χ s + conj (heckeEulerProduct χ (conj s))))
      (G := fun s ↦ G0 s + (1 / 2 : ℂ) * (heckeLFunction χ s + conj (heckeLFunction χ (conj s))))
      (fun n ↦ ?_) (fun s hs ↦ ?_) ?_ (fun s hs ↦ ?_)
    · have h1 := norm_acoef_le χ n
      have h2 := Complex.abs_re_le_norm (acoef χ n)
      show 0 ≤ bcoef F n + (acoef χ n).re
      linarith [neg_abs_le (acoef χ n).re]
    · have h := (hB s hs).add (((hA s hs).add (hAc s hs)).smul (1 / 2 : ℂ))
      refine (LSeriesHasSum_congr s _ fun {n} _ ↦ ?_).mp h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      rw [Complex.re_eq_add_conj]
      ring
    · exact hG0.add (continuousOn_const.mul (hH.add hHc))
    · rw [hG0s s hs, hHe s hs, hHce s hs]
      push_cast
      ring
  have him : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (bcoef F n + (acoef χ n).im))
      atTop (𝓝 ρ) := by
    refine TauCeti.LSeries.wienerIkehara
      (F := fun s ↦ LSeries (fun n ↦ (bcoef F n : ℂ)) s +
        (1 / (2 * Complex.I)) * (heckeEulerProduct χ s - conj (heckeEulerProduct χ (conj s))))
      (G := fun s ↦ G0 s +
        (1 / (2 * Complex.I)) * (heckeLFunction χ s - conj (heckeLFunction χ (conj s))))
      (fun n ↦ ?_) (fun s hs ↦ ?_) ?_ (fun s hs ↦ ?_)
    · have h1 := norm_acoef_le χ n
      have h2 := Complex.abs_im_le_norm (acoef χ n)
      show 0 ≤ bcoef F n + (acoef χ n).im
      linarith [neg_abs_le (acoef χ n).im]
    · have h := (hB s hs).add (((hA s hs).sub (hAc s hs)).smul (1 / (2 * Complex.I)))
      refine (LSeriesHasSum_congr s _ fun {n} _ ↦ ?_).mp h
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      push_cast
      rw [Complex.im_eq_sub_conj]
      ring
    · exact hG0.add (continuousOn_const.mul (hH.sub hHc))
    · rw [hG0s s hs, hHe s hs, hHce s hs]
      push_cast
      ring
  have hre0 : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (acoef χ n).re) atTop (𝓝 0) := by
    have := hre.sub hb
    rw [sub_self] at this
    refine this.congr fun x ↦ ?_
    rw [Finset.sum_add_distrib]
    ring
  have him0 : Tendsto (fun x : ℝ ↦ x⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (acoef χ n).im) atTop (𝓝 0) := by
    have := him.sub hb
    rw [sub_self] at this
    refine this.congr fun x ↦ ?_
    rw [Finset.sum_add_distrib]
    ring
  have hC := ((Complex.continuous_ofReal.tendsto 0).comp hre0).add
    (((Complex.continuous_ofReal.tendsto 0).comp him0).mul_const Complex.I)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hC
  refine hC.congr fun x ↦ ?_
  simp only [Function.comp_apply]
  push_cast
  rw [mul_assoc, ← mul_add, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun n _ ↦ Complex.re_add_im _


theorem finsum_eq_sum_acoef (χ : HeckeCharacter F) {x : ℝ} (hx : 0 ≤ x) :
    (∑ᶠ (I : Ideal (𝓞 F)) (_ : I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x),
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        χ.primeValue v ^
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, acoef χ n := by
  have hset : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} =
      ⋃ n ∈ ((Finset.Icc 1 ⌊x⌋₊ : Finset ℕ) : Set ℕ), ((fiber F n : Finset (Ideal (𝓞 F))) : Set (Ideal (𝓞 F))) := by
    ext I
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, Finset.mem_Icc, mem_fiber,
      exists_prop]
    constructor
    · rintro ⟨h0, hle⟩
      refine ⟨Ideal.absNorm I, ⟨?_, Nat.le_floor hle⟩, rfl⟩
      exact Nat.one_le_iff_ne_zero.mpr fun h ↦ h0 (Ideal.absNorm_eq_zero_iff.mp h)
    · rintro ⟨n, ⟨h1, hn⟩, hI⟩
      refine ⟨fun h ↦ ?_, ?_⟩
      · rw [h, Ideal.absNorm_bot] at hI
        omega
      · rw [hI]
        exact (Nat.le_floor_iff hx).mp hn
  have h1 : (∑ᶠ (I : Ideal (𝓞 F)) (_ : I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x),
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        χ.primeValue v ^
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)) =
      ∑ᶠ I ∈ {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}, idealVal χ I := rfl
  rw [h1, hset, finsum_mem_biUnion]
  · rw [finsum_mem_coe_finset]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finsum_mem_coe_finset]
    unfold acoef
    apply Finset.sum_congr rfl
    intro I hI
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hI0 : I ≠ ⊥ := by
      intro h
      rw [mem_fiber, h, Ideal.absNorm_bot] at hI
      omega
    exact (idealHom_apply χ hI0).symm
  · intro m _ n _ hmn
    refine Set.disjoint_left.mpr fun I hm hn ↦ hmn ?_
    rw [Finset.mem_coe, mem_fiber] at hm hn
    rw [← hm, ← hn]
  · exact Finset.finite_toSet _
  · intro n _
    exact Finset.finite_toSet _

end Sol_MasulloGRH_tendsto_sum_heckeCharacter_ideals_div_atTop

open Sol_MasulloGRH_tendsto_sum_heckeCharacter_ideals_div_atTop in
theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F)
    (hχ : ¬ χ.IsTrivialOnNormOne) :
    Tendsto
      (fun x : ℝ =>
        (∑ᶠ (I : Ideal (𝓞 F)) (_ : I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x),
          ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            χ.primeValue v ^
              Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)) / (x : ℂ))
      atTop (𝓝 0) := by
  refine (tendsto_acoef χ hχ).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [div_eq_inv_mul, finsum_eq_sum_acoef χ hx]
