-- Prove2me | solution 1 for MasulloRH.spectral_trace_of_polynomial_translation
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:44:27.056508+00:00
-- url     : https://prove2.me/submissions/135ef724-4130-484e-81af-e31ea1411913

import Mathlib
import Theorems.Thm_MasulloGRH_trace_of_diagonal_frequency_bands
import Theorems.Thm_MasulloRH_localized_fourier_multiplier

open MeasureTheory Filter MasulloRH MasulloGRH
open scoped FourierTransform SchwartzMap BigOperators ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LocalizedFourier


private noncomputable def rawWindow (x : ℝ) : ℂ :=
  ((Real.smoothTransition (x+1) - Real.smoothTransition x : ℝ) : ℂ)

private lemma rawWindow_zero (x : ℝ) (hx : 1 ≤ |x|) : rawWindow x = 0 := by
  rcases le_abs.mp hx with h | h
  · simp [rawWindow, Real.smoothTransition.one_of_one_le h,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x+1)]
  · simp [rawWindow, Real.smoothTransition.zero_of_nonpos (by linarith : x ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : x+1 ≤ 0)]

private lemma rawWindow_smooth : ContDiff ℝ ∞ rawWindow := by
  have H : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (x+1) - Real.smoothTransition x) :=
    (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub Real.smoothTransition.contDiff
  exact Complex.ofRealCLM.contDiff.comp H

private lemma rawWindow_compact : HasCompactSupport rawWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(-1:ℝ)) (b:=1))
  intro x hx
  by_contra h
  apply hx
  apply rawWindow_zero
  by_contra! h'
  exact h ⟨(abs_lt.mp h').1.le, (abs_lt.mp h').2.le⟩

/-- A smooth integer-translate partition window, supported in the unit interval on each side of zero. -/
noncomputable def integerWindow : 𝓢(ℝ,ℂ) := rawWindow_compact.toSchwartzMap rawWindow_smooth

theorem integerWindow_zero (x : ℝ) (hx : 1 ≤ |x|) : integerWindow x = 0 := rawWindow_zero x hx

theorem integerWindow_range (x : ℝ) :
    (integerWindow x).im = 0 ∧ 0 ≤ (integerWindow x).re ∧ (integerWindow x).re ≤ 1 := by
  change (Complex.ofReal _).im = 0 ∧ 0 ≤ Real.smoothTransition (x+1) - Real.smoothTransition x ∧
    Real.smoothTransition (x+1) - Real.smoothTransition x ≤ 1
  exact ⟨rfl, sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith)),
    sub_le_self _ (Real.smoothTransition.nonneg x) |>.trans (Real.smoothTransition.le_one _)⟩

theorem integerWindow_local (x : ℝ) (j : ℤ) (h0 : j ≠ ⌊x⌋) (h1 : j ≠ ⌊x⌋+1) :
    integerWindow (x-(j:ℝ)) = 0 := by
  have hp := Int.floor_le x
  have hq := Int.lt_floor_add_one x
  apply integerWindow_zero
  by_cases hj : j < ⌊x⌋
  · have h : (j:ℝ) + 1 ≤ (⌊x⌋:ℝ) := by exact_mod_cast (show j+1 ≤ ⌊x⌋ by omega)
    exact le_abs.mpr (Or.inl (by linarith))
  · have h : (⌊x⌋:ℝ) + 2 ≤ (j:ℝ) := by exact_mod_cast (show ⌊x⌋+2 ≤ j by omega)
    exact le_abs.mpr (Or.inr (by linarith))

theorem integerWindow_hasSum (x : ℝ) : HasSum (fun j : ℤ => integerWindow (x-(j:ℝ))) 1 := by
  let p : ℤ := ⌊x⌋
  let f := fun j : ℤ => integerWindow (x-(j:ℝ))
  have hs : ∀ j ∉ ({p, p+1} : Finset ℤ), f j = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact integerWindow_local x j hj.1 hj.2
  have hp : (p:ℝ) ≤ x := Int.floor_le x
  have hq : x < (p:ℝ)+1 := Int.lt_floor_add_one x
  have hsum : ∑ j ∈ ({p,p+1} : Finset ℤ), f j = 1 := by
    rw [Finset.sum_pair (by omega : p ≠ p+1)]
    change ((Real.smoothTransition ((x-(p:ℝ))+1) - Real.smoothTransition (x-(p:ℝ)) : ℝ) : ℂ) +
      ((Real.smoothTransition ((x-((p+1:ℤ):ℝ))+1) - Real.smoothTransition (x-((p+1:ℤ):ℝ)) : ℝ) : ℂ) = 1
    simp only [Int.cast_add, Int.cast_one]
    rw [show x-((p:ℝ)+1)+1 = x-(p:ℝ) by ring,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x-(p:ℝ)+1),
      Real.smoothTransition.zero_of_nonpos (by linarith : x-((p:ℝ)+1) ≤ 0)]
    push_cast
    ring
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hs


end LocalizedFourier

namespace MasulloRH

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integratedOperator_exists
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (W : ℝ → ℝ) (A : ℝ)
    (hcont : ∀ u, Continuous (fun y => U y u))
    (hK : AEStronglyMeasurable K) (hKW : Integrable (fun y => ‖K y‖ * W y))
    (hW : ∀ y, 0 ≤ W y) (hA : 0 ≤ A) (hU : ∀ y, ‖U y‖ ≤ A * W y) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, K y • U y u) ∧
      ‖T‖ ≤ A * ∫ y : ℝ, ‖K y‖ * W y := by
  have hdom (u : H) (y : ℝ) :
      ‖K y • U y u‖ ≤ (‖K y‖ * W y) * (A * ‖u‖) := by
    rw [norm_smul]
    calc
      _ ≤ ‖K y‖ * ((A * W y) * ‖u‖) := by
        gcongr
        exact ((U y).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hU y) (norm_nonneg _))
      _ = _ := by ring
  have hi (u : H) : Integrable (fun y => K y • U y u) := by
    apply (hKW.mul_const (A * ‖u‖)).mono' (hK.smul (hcont u).aestronglyMeasurable)
    exact Eventually.of_forall (hdom u)
  let L : H →ₗ[ℂ] H := {
    toFun := fun u => ∫ y : ℝ, K y • U y u
    map_add' := by
      intro u v
      simp only [map_add, smul_add, integral_add (hi u) (hi v)]
    map_smul' := by
      intro c u
      simp only [map_smul, RingHom.id_apply]
      simp_rw [smul_comm (K _) c, integral_smul] }
  have hb (u : H) : ‖L u‖ ≤ (A * ∫ y : ℝ, ‖K y‖ * W y) * ‖u‖ := by
    calc
      _ ≤ ∫ y : ℝ, (‖K y‖ * W y) * (A * ‖u‖) := by
        exact norm_integral_le_of_norm_le (hKW.mul_const _) (Eventually.of_forall (hdom u))
      _ = _ := by rw [integral_mul_const]; ring
  have hC : 0 ≤ A * ∫ y : ℝ, ‖K y‖ * W y := mul_nonneg hA
    (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (hW y)))
  exact ⟨L.mkContinuous _ hb, fun _ => rfl, L.mkContinuous_norm_le hC hb⟩

theorem integratedOperator_eigen
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, K y • U y u)
    (character : ℝ → ℂ) (v : H) (hv : ∀ y, U y v = character y • v) :
    T v = (∫ y : ℝ, K y * character y) • v := by
  rw [hT]
  simp_rw [hv, smul_smul]
  exact integral_smul_const _ _

theorem integratedOperator_fourier
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, K y • U y u)
    (ξ : ℝ) (v : H)
    (hv : ∀ y : ℝ, U y v = Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • v) :
    T v = (𝓕 K ξ) • v := by
  rw [integratedOperator_eigen U K T hT _ v hv, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => mul_comm _ _

theorem integratedOperator_inverseFourier
    (U : ℝ → H →L[ℂ] H) (m : ℝ → ℂ) (T : H →L[ℂ] H)
    (hm : Integrable m) (hmF : Integrable (𝓕 m))
    (hT : ∀ u, T u = ∫ y : ℝ, (𝓕⁻ m) y • U y u)
    (ξ : ℝ) (hmξ : ContinuousAt m ξ) (v : H)
    (hv : ∀ y : ℝ, U y v = Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • v) :
    T v = m ξ • v := by
  rw [integratedOperator_fourier U (𝓕⁻ m) T hT ξ v hv, hm.fourier_fourierInv_eq hmF hmξ]


end MasulloRH

private lemma polynomial_band_count {ι : Type*} (ν : ι → ℝ)
    (hw : Summable fun i => 1/(1+(ν i)^2)) :
    ∃ F : ℤ → Finset ι, ∃ C : ℝ, 0 ≤ C ∧
      (∀ j i, i ∈ F j ↔ |ν i - j| ≤ 1) ∧
      ∀ j, ((F j).card : ℝ) ≤ C * (1 + |(j:ℝ)|)^2 := by
  classical
  let w (i : ι) : ℝ := 1 / (1 + (ν i)^2)
  let D (j : ℤ) := 2 * (1 + |(j:ℝ)|)^2
  have hD (j : ℤ) : 0 < D j := by dsimp [D]; positivity
  have hle {j : ℤ} {i : ι} (hi : |ν i - j| ≤ 1) : 1 / D j ≤ w i := by
    apply one_div_le_one_div_of_le (by positivity)
    have h : |ν i| ≤ 1 + |(j:ℝ)| := calc
      |ν i| = |ν i - j + j| := by ring_nf
      _ ≤ |ν i - j| + |(j:ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
    have hs := sq_le_sq₀ (abs_nonneg (ν i)) (by positivity : 0 ≤ 1+|(j:ℝ)|)
    dsimp [D]
    nlinarith [(sq_abs (ν i)), hs.mpr h, abs_nonneg (j:ℝ)]
  have hfinite (j : ℤ) : {i | |ν i - j| ≤ 1}.Finite := by
    have hev : ∀ᶠ i in cofinite, w i < 1 / D j :=
      hw.tendsto_cofinite_zero.eventually_lt_const (by positivity)
    apply (Filter.mem_cofinite.mp hev).subset
    intro i hi
    exact not_lt.mpr (hle hi)
  let F (j : ℤ) := (hfinite j).toFinset
  have hF (j : ℤ) (i : ι) : i ∈ F j ↔ |ν i - j| ≤ 1 := Set.Finite.mem_toFinset _
  refine ⟨F, 2 * ∑' i, w i, mul_nonneg (by norm_num) (tsum_nonneg (fun i => by dsimp [w]; positivity)), hF, ?_⟩
  intro j
  have hsum : ∑ i ∈ F j, 1 / D j ≤ ∑ i ∈ F j, w i :=
    Finset.sum_le_sum (fun i hi => hle ((hF j i).mp hi))
  have hupper := hsum.trans (hw.sum_le_tsum (F j) (fun _ _ => by positivity))
  have hdiv : ((F j).card : ℝ) / D j ≤ ∑' i, w i := by simpa [div_eq_mul_inv] using hupper
  have hcard := (div_le_iff₀ (hD j)).mp hdiv
  dsimp [D] at hcard
  linarith only [hcard]

private lemma summable_band_cost {ι E : Type*} [NormedAddCommGroup E]
    (A : ℤ → E) (F : ℤ → Finset ι) (C B : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ j, ((F j).card : ℝ) ≤ C * (1 + |(j:ℝ)|)^2)
    (hA : ∀ j : ℤ, (1 + |(j:ℝ)|)^4 * ‖A j‖ ≤ B) :
    Summable fun j => ((F j).card : ℝ) * ‖A j‖ := by
  have hnat : Summable (fun n : ℕ => 1/(1+|(n:ℝ)|)^2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    simpa [abs_of_nonneg, add_comm (1:ℝ) _, Real.rpow_two] using h
  have hint : Summable (fun j : ℤ => 1/(1+|(j:ℝ)|)^2) := by
    apply Summable.of_nat_of_neg <;> simpa using hnat
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hint.mul_left (C*B))
  intro j
  set x := 1 + |(j:ℝ)|
  have hx : 0 < x := by dsimp [x]; positivity
  calc
    _ ≤ (C * x^2) * ‖A j‖ := mul_le_mul_of_nonneg_right (hcount j) (norm_nonneg _)
    _ = (C * (x^4 * ‖A j‖)) / x^2 := by field_simp
    _ ≤ C * B / x^2 := by gcongr; exact hA j
    _ = _ := by ring

private lemma schwartz_weighted_integral (g : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun x : ℝ => (1+|x|)^k * ‖g x‖) := by
  have h := (g.integrable.norm.add (g.integrable_pow_mul volume k)).const_mul ((2:ℝ)^(k-1))
  apply h.mono' (by fun_prop)
  refine Eventually.of_forall fun x => ?_
  change ‖(1+|x|)^k * ‖g x‖‖ ≤ 2^(k-1) * (‖g x‖ + ‖x‖ ^ k * ‖g x‖)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, ← one_add_mul, ← mul_assoc]
  gcongr
  simpa using add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg x) k

private noncomputable def freqBand (m θ : 𝓢(ℝ,ℂ)) (j : ℤ) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) ((θ.compSubConstCLM ℂ (j:ℝ)).hasTemperateGrowth) m

private lemma freqBand_apply (m θ : 𝓢(ℝ,ℂ)) (j : ℤ) (x : ℝ) :
    freqBand m θ j x = m x * θ (x-j) := rfl

private lemma makeFrequencyOperator {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (horbit : ∀ u, Continuous (fun y => U y u))
    (hU : ∀ y, ‖U y‖ ≤ B * (1+|y|)^k) (m : 𝓢(ℝ,ℂ)) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, (𝓕⁻ (⇑m)) y • U y u) ∧
      ‖T‖ ≤ B * (∫ y : ℝ, (1+|y|)^k * ‖(𝓕⁻ (⇑m)) y‖) ∧
      ∀ (ξ : ℝ) (v : H), (∀ y : ℝ, U y v = Complex.exp (↑(-2*Real.pi*y*ξ) * Complex.I) • v) →
        T v = m ξ • v := by
  let g : 𝓢(ℝ,ℂ) := 𝓕⁻ m
  have hcoe : (⇑g : ℝ → ℂ) = 𝓕⁻ (⇑m) := SchwartzMap.fourierInv_coe m
  have hK : AEStronglyMeasurable (𝓕⁻ (⇑m)) := hcoe ▸ g.continuous.aestronglyMeasurable
  have hw : Integrable (fun x : ℝ => ‖(𝓕⁻ (⇑m)) x‖ * (1+|x|)^k) := by
    simpa only [mul_comm (‖_‖), ← hcoe] using schwartz_weighted_integral g k
  obtain ⟨T,hT,hb⟩ := integratedOperator_exists U (𝓕⁻ (⇑m)) (fun y : ℝ => (1+|y|)^k) B
    horbit hK hw (fun y => by positivity) hB hU
  refine ⟨T, hT, ?_, ?_⟩
  · simpa only [mul_comm (‖_‖)] using hb
  · intro ξ v hv
    apply integratedOperator_inverseFourier U m T m.integrable _ hT ξ m.continuous.continuousAt v hv
    simpa only [← SchwartzMap.fourier_coe] using (𝓕 m : 𝓢(ℝ,ℂ)).integrable

theorem solution {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (horbit : ∀ u, Continuous (fun y => U y u))
    (hU : ∀ y, ‖U y‖ ≤ B * (1+|y|)^k)
    (v : ι → H) (ν : ι → ℝ) (hl : LinearIndependent ℂ v)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (heig : ∀ i (y : ℝ), U y (v i) = Complex.exp (↑(-2*Real.pi*y*ν i) * Complex.I) • v i)
    (hw : Summable fun i => 1/(1+(ν i)^2)) (m : 𝓢(ℝ,ℂ)) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, (𝓕⁻ (⇑m)) y • U y u) ∧
      IsNuclearOperator T ∧ HasSum (fun i => m (ν i)) (operatorTrace T) := by
  classical
  obtain ⟨T,hT,_,ht⟩ := makeFrequencyOperator U k B hB horbit hU m
  refine ⟨T,hT,?_⟩
  let θ := LocalizedFourier.integerWindow
  obtain ⟨F,C,hC,hF,hcount⟩ := polynomial_band_count ν hw
  choose A hA hnorm ha using fun j : ℤ =>
    makeFrequencyOperator U k B hB horbit hU (freqBand m θ j)
  obtain ⟨L,_,hkernel⟩ := localized_fourier_multiplier m θ k 4
  have hdecay (j : ℤ) : (1+|(j:ℝ)|)^4 * ‖A j‖ ≤ B * L := by
    calc
      _ ≤ (1+|(j:ℝ)|)^4 * (B * (∫ y : ℝ, (1+|y|)^k *
          ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-(j:ℝ)))) y‖)) :=
        mul_le_mul_of_nonneg_left (hnorm j) (by positivity)
      _ = B * ((1+|(j:ℝ)|)^4 * (∫ y : ℝ, (1+|y|)^k *
          ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-(j:ℝ)))) y‖)) := by ring
      _ ≤ B*L := mul_le_mul_of_nonneg_left (hkernel j).2 hB
  have hc := summable_band_cost A F C (B*L) hC hcount hdecay
  let e := Equiv.intEquivNat.symm
  refine trace_of_diagonal_frequency_bands v hl hd (fun n => F (e n)) (fun n => A (e n))
    (fun n i => m (ν i) * θ (ν i - (e n:ℝ))) ?_ ?_ (e.summable_iff.mpr hc) T (fun i => m (ν i)) ?_ ?_
  · intro n i
    exact ha (e n) (ν i) (v i) (heig i)
  · intro n i hi
    have hx : 1 ≤ |ν i - (e n:ℝ)| := (lt_of_not_ge (fun h => hi ((hF _ _).mpr h))).le
    rw [LocalizedFourier.integerWindow_zero _ hx, mul_zero]
  · intro i
    have hi : HasSum (fun j : ℤ => m (ν i) * θ (ν i - (j:ℝ))) (m (ν i)) := by
      simpa only [mul_one] using (LocalizedFourier.integerWindow_hasSum (ν i)).mul_left (m (ν i))
    exact e.hasSum_iff.mpr hi
  · exact fun i => ht _ _ (heig i)
