-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_site_all_cases_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:48:40.866584+00:00
-- url     : https://prove2.me/submissions/f02f7cea-19ad-4674-9d82-591990273c08

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactivePointApproximation_error_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactive_sliced_fixed_scaled_support_s2
import Theorems.Thm_OAI_Erdos3_exists_affineCube_plateau_site_approximation_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanCoefficient_sub_bound {α : Type*} [DecidableEq α]
    (f g : Finset α → ℝ) (s : Finset α) {H : ℝ}
    (h : ∀ t ∈ s.powerset, |f t-g t| ≤ H) :
    |booleanCoefficient f s-booleanCoefficient g s| ≤ (2 : ℝ)^s.card*H := by
  unfold booleanCoefficient
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ)^(s\t).card*f t-(-1 : ℝ)^(s\t).card*g t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ s.powerset, |f t-g t| := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_sub, abs_mul, abs_pow]
      norm_num
    _ ≤ ∑ _t ∈ s.powerset, H := Finset.sum_le_sum h
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_rational_approximations {I : Type*} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) {Q E : ℝ}
    (h : ∀ i, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ m : ℤ, |θ i-(m : ℝ)/q| ≤ E) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Q^Fintype.card I ∧
      ∃ a : I → ℤ, ∀ i, |θ i-(a i : ℝ)/D| ≤ E := by
  choose q hq hqQ m hm using h
  let D := ∏ i, q i
  let rest := fun i => ∏ j ∈ Finset.univ.erase i, q j
  have hrest (i : I) : 0 < rest i := Finset.prod_pos (fun j _ => hq j)
  have hD (i : I) : q i * rest i = D :=
    Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
  have hDp : 0 < D := Finset.prod_pos (fun i _ => hq i)
  refine ⟨D,hDp,?_,(fun i => (rest i : ℤ)*m i),?_⟩
  · calc
      (D : ℝ) = ∏ i, (q i : ℝ) := by simp [D]
      _ ≤ ∏ _i : I, Q := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hqQ i)
      _ = Q^Fintype.card I := by simp
  · intro i
    have hqr : (0 : ℝ) < q i := by exact_mod_cast hq i
    have hrr : (0 : ℝ) < rest i := by exact_mod_cast hrest i
    have hd : (D : ℝ) = (q i : ℝ)*rest i := by exact_mod_cast (hD i).symm
    have he : (((rest i : ℤ)*m i : ℤ) : ℝ)/(D : ℝ) = (m i : ℝ)/q i := by
      push_cast
      rw [hd]
      field_simp
    rw [he]
    exact hm i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

theorem regularizationRadius_spec {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < regularizationRadius L ε ∧ regularizationRadius L ε ≤ 1 ∧
      L*regularizationRadius L ε ≤ ε/2 := by
  have hp : 0 < regularizationRadius L ε := by unfold regularizationRadius; positivity
  refine ⟨hp, min_le_left _ _, ?_⟩
  have hs := (le_div_iff₀ (show 0 < 2*(1+L) by positivity)).mp
    (show regularizationRadius L ε ≤ ε/(2*(1+L)) from min_le_right _ _)
  nlinarith

theorem regularizationRadius_inverse_le_exp {L ε P : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : 0 ≤ P)
    (hLP : L ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (regularizationRadius L ε)⁻¹ ≤ Real.exp (2*P+2) := by
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+2)
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (ε/(2*(1+L)))⁻¹ = 2*(1+L)*ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp P := by
        gcongr
        exact one_add_le_exp_succ hP hLP
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LengthDyadicCutoff
namespace OAI

section

namespace Erdos3

theorem length_small_grid_bound {N V L C ζ : ℝ} {c t : ℕ}
    (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hsize : N ≤ V * L ^ t) (hsmall : L ≤ C / ζ ^ c) :
    N ≤ V * C ^ t / ζ ^ (c * t) := by
  calc
    _ ≤ V * L ^ t := hsize
    _ ≤ V * (C / ζ ^ c) ^ t :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hsmall t) hV
    _ = _ := by rw [div_pow, pow_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

theorem unscale_grid_interval {M H d : ℕ} (hM : 0 < M) (k : Fin M) (a : ℤ)
    (h : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    |(k.val : ℝ) / M - (a : ℝ) / d| ≤ (H : ℝ) / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (k.val : ℝ) / M - (a : ℝ) / d =
      ((k.val : ℝ) - M * ((a : ℝ) / d)) / M := by field_simp
  rw [he, abs_div, abs_of_pos hM']
  exact div_le_div_of_nonneg_right h hM'.le

theorem rationalGridMajorSet_rational {M Q H : ℕ} (hM : 0 < M) (k : Fin M)
    (hk : k ∈ rationalGridMajorSet M Q H) :
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ (Q + 1 : ℝ) ∧
      ∃ a : ℤ, |(k.val : ℝ) / M - (a : ℝ) / d| ≤ (H : ℝ) / M := by
  classical
  obtain ⟨d, hd, ha⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨a, _, hk⟩ := Finset.mem_biUnion.mp ha
  have he := (Finset.mem_filter.mp hk).2
  by_cases hd0 : d = 0
  · refine ⟨1, by omega, by exact_mod_cast (show 1 ≤ Q + 1 by omega), 0, ?_⟩
    apply unscale_grid_interval hM k 0
    simpa only [hd0, Nat.cast_zero, div_zero, Int.cast_zero, zero_div, mul_zero, sub_zero] using he
  · refine ⟨d, Nat.pos_of_ne_zero hd0, ?_, a, unscale_grid_interval hM k a he⟩
    exact_mod_cast (Finset.mem_range.mp hd).le

theorem rationalGridMajorBox_character {J : Type*} [Fintype J] [DecidableEq J]
    {M Q H : ℕ} (hM : 0 < M) (k : J → Fin M) (hk : k ∈ rationalGridMajorBox J M Q H) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (Q + 1 : ℝ) ^ Fintype.card J ∧
      ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ H) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ξ j / M := by
  have hj := Fintype.mem_piFinset.mp hk
  obtain ⟨D, hD, hDQ, a, ha⟩ := exists_common_rational_approximations
    (fun j => ((k j).val : ℝ) / M) (fun j => rationalGridMajorSet_rational hM (k j) (hj j))
  let ξ j := (M : ℝ) * (((k j).val : ℝ) / M - (a j : ℝ) / D)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨D, hD, hDQ, a, ξ, ?_, ?_⟩
  · intro j
    dsimp only [ξ]
    rw [abs_mul, abs_of_pos hM']
    calc
      _ ≤ (M : ℝ) * ((H : ℝ) / M) := mul_le_mul_of_nonneg_left (ha j) hM'.le
      _ = H := by field_simp
  · intro j
    dsimp only [ξ]
    field_simp
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rationalGridMajorBox_scaled_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M Q H : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    (k : J → Fin M) (hk : k ∈ rationalGridMajorBox J M Q H) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (Q + 1 : ℝ) ^ Fintype.card J ∧
      ∃ (a : J → ℤ) (ω : J → ℝ), (∀ j, |ω j| ≤ H) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
  have hM : 0 < M := lt_of_lt_of_le hK hKM
  have hK0 : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hM0 : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  obtain ⟨D, hD, hDQ, a, ξ, hξ, he⟩ := rationalGridMajorBox_character hM k hk
  refine ⟨D, hD, hDQ, a, (fun j => (K : ℝ) * ξ j / M), ?_, ?_⟩
  · intro j
    simp only [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K),
      abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    apply (div_le_iff₀ (Nat.cast_pos.mpr hM)).mpr
    calc
      (K : ℝ) * |ξ j| ≤ (K : ℝ) * H := mul_le_mul_of_nonneg_left (hξ j) (Nat.cast_nonneg K)
      _ ≤ (M : ℝ) * H := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKM) (Nat.cast_nonneg H)
      _ = (H : ℝ) * M := mul_comm _ _
  · intro j
    rw [he j]
    congr 1
    field_simp

theorem lengthAwarePolynomialGrid_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    {C L V A ζ : ℝ} {c t r : ℕ} (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ V * L ^ t)
    (k : J → Fin M)
    (hk : k ∈ lengthAwareSpectrumCover C L c (polynomialGridCover J M A r) ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ max ((⌈A / ζ ^ r⌉₊ + 1 : ℝ) ^ Fintype.card J)
        (V * C ^ t / ζ ^ (c * t)) ∧
      ∃ (a : J → ℤ) (ω : J → ℝ), (∀ j, |ω j| ≤ (⌈A / ζ ^ r⌉₊ : ℝ)) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
  classical
  by_cases hstart : C / ζ ^ c ≤ L
  · have hk' : k ∈ rationalGridMajorBox J M ⌈A / ζ ^ r⌉₊ ⌈A / ζ ^ r⌉₊ := by
      simpa only [lengthAwareSpectrumCover, if_pos hstart, polynomialGridCover] using hk
    obtain ⟨D, hD, hb, a, ω, hω, he⟩ := rationalGridMajorBox_scaled_character hK hKM k hk'
    exact ⟨D, hD, hb.trans (le_max_left _ _), a, ω, hω, he⟩
  · cases isEmpty_or_nonempty J with
    | inl hJ =>
      let := hJ
      refine ⟨1, Nat.zero_lt_one, ?_, (fun j => isEmptyElim j),
        (fun j => isEmptyElim j), (fun j => isEmptyElim j), (fun j => isEmptyElim j)⟩
      simpa only [Fintype.card_eq_zero, pow_zero, Nat.cast_one] using
        (le_max_left (1 : ℝ) (V * C ^ t / ζ ^ (c * t)))
    | inr hJ =>
      let := hJ
      have hM : 0 < M := lt_of_lt_of_le hK hKM
      have hpow : (M : ℝ) ≤ (M : ℝ) ^ Fintype.card J :=
        le_self_pow₀ (by exact_mod_cast hM) (Fintype.card_pos.ne')
      have hb := length_small_grid_bound hV hL hsize (le_of_lt (lt_of_not_ge hstart))
      refine ⟨M, hM, (hpow.trans hb).trans (le_max_right _ _),
        (fun j => ((k j).val : ℤ)), (fun _ => 0), ?_, ?_⟩
      · intro j
        simpa only [abs_zero] using (Nat.cast_nonneg ⌈A / ζ ^ r⌉₊ : (0 : ℝ) ≤ _)
      · intro j
        simp only [Int.cast_natCast, zero_div, add_zero]

end Erdos3

end

section

namespace Erdos3

theorem uniformBlockSpectrumCover_scaled_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (k : J → Fin M) (hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
      ∃ (a : J → ℤ) (ω : J → ℝ),
        (∀ j, |ω j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K :=
  lengthAwarePolynomialGrid_character hK hKM hL hW hsize k hk

theorem uniformBlockSpectrumCover_modes {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ∃ (D : (J → Fin M) → ℕ) (a : (J → Fin M) → J → ℤ) (ω : (J → Fin M) → J → ℝ),
      (∀ k, 0 < D k) ∧ ∀ k ∈ uniformBlockSpectrumCover J M n U V L ζ,
        (D k : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω k j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a k j : ℝ) / D k + ω k j / K := by
  classical
  have hex (k : J → Fin M) : ∃ D : ℕ, 0 < D ∧ ∃ (a : J → ℤ) (ω : J → ℝ),
      k ∈ uniformBlockSpectrumCover J M n U V L ζ →
        (D : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
    by_cases hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ
    · obtain ⟨D, hD, hb, a, ω, hω, he⟩ :=
        uniformBlockSpectrumCover_scaled_character hK hKM n t hL hW hsize k hk
      exact ⟨D, hD, a, ω, fun _ => ⟨hb, hω, he⟩⟩
    · exact ⟨1, Nat.zero_lt_one, 0, 0, fun h => (hk h).elim⟩
  choose D hD a ω h using hex
  exact ⟨D, a, ω, hD, h⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {O : Type*} [Fintype O]

theorem integerRowMassTent_range {K : ℝ} (hK : 0 ≤ K) (z : O → ℤ) (x : O → ℝ) :
    0 ≤ integerRowMassTent K z x ∧ integerRowMassTent K z x ≤ K ^ Fintype.card O := by
  refine ⟨Finset.prod_nonneg (fun i _ => (integerMassTent_range K hK (z i) (x i)).1), ?_⟩
  simpa only [integerRowMassTent, Finset.prod_const, Finset.card_univ] using
    Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).1)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).2)

theorem integerRowMassTent_grid {K : ℝ} (hK : 0 < K) (z k : O → ℤ) :
    integerRowMassTent K z (fun i => (k i : ℝ) / K) =
      if z = k then K ^ Fintype.card O else 0 := by
  classical
  by_cases he : z = k
  · subst z
    simp [integerRowMassTent, integerMassTent_grid K hK]
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ k i := Function.ne_iff.mp he
    have hz : integerMassTent K (z i) ((k i : ℝ) / K) = 0 := by
      rw [integerMassTent_grid K hK]
      simp [Ne.symm hi]
    simp only [he, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem integerRowMassTent_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (z : O → ℤ) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassTent (K : ℝ) z) := by
  have hf (i : O) : LipschitzWith (2 * K ^ 2) (fun x : O → ℝ => integerMassTent K (z i) (x i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ (2 * (K : ℝ) ^ 2) * |x i - y i| := integerMassTent_difference K K.coe_nonneg (z i) (x i) (y i)
      _ ≤ _ := by
        simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, Real.dist_eq] using
          mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (by positivity : 0 ≤ 2 * (K : ℝ) ^ 2)
  exact (bounded_lipschitz_real_prod _ hK hf (fun i x => by
    rw [abs_of_nonneg (integerMassTent_range K K.coe_nonneg (z i) (x i)).1]
    exact (integerMassTent_range K K.coe_nonneg (z i) (x i)).2)).2

theorem integerRowMassTent_integrable {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    Integrable (fun z => integerRowMassTent K z x) p.toMeasure := by
  apply (integrable_const (K ^ Fintype.card O)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integerRowMassTent_range hK z x).1]
    exact (integerRowMassTent_range hK z x).2)

theorem integerRowMassInterpolation_range {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    0 ≤ integerRowMassInterpolation K p x ∧ integerRowMassInterpolation K p x ≤ K ^ Fintype.card O := by
  refine ⟨integral_nonneg (fun z => (integerRowMassTent_range hK z x).1), ?_⟩
  have h := integral_mono (integerRowMassTent_integrable hK p x) (integrable_const (K ^ Fintype.card O))
    (fun z => (integerRowMassTent_range hK z x).2)
  simpa only [integerRowMassInterpolation, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using h

theorem integerRowMassInterpolation_grid {K : ℝ} (hK : 0 < K) (p : PMF (O → ℤ)) (k : O → ℤ) :
    integerRowMassInterpolation K p (fun i => (k i : ℝ) / K) =
      K ^ Fintype.card O * (p k).toReal := by
  classical
  have he : (fun z => integerRowMassTent K z (fun i => (k i : ℝ) / K)) =
      Set.indicator {k} (fun _ => K ^ Fintype.card O) := by
    funext z
    simp only [integerRowMassTent_grid hK, Set.indicator_apply, Set.mem_singleton_iff]
  rw [integerRowMassInterpolation, he, integral_indicator (measurableSet_singleton k), integral_singleton,
    measureReal_def, PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k), smul_eq_mul, mul_comm]

theorem integerRowMassInterpolation_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (p : PMF (O → ℤ)) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassInterpolation (K : ℝ) p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖integerRowMassInterpolation (K : ℝ) p x - integerRowMassInterpolation (K : ℝ) p y‖ ≤ _
  rw [integerRowMassInterpolation, integerRowMassInterpolation,
    ← integral_sub (integerRowMassTent_integrable K.coe_nonneg p x) (integerRowMassTent_integrable K.coe_nonneg p y)]
  have h := norm_integral_le_of_norm_le_const (μ := p.toMeasure)
    (f := fun z => integerRowMassTent (K : ℝ) z x - integerRowMassTent (K : ℝ) z y)
    (C := (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O : ℝ≥0) * dist x y)
    (Filter.Eventually.of_forall (fun z => by
      simpa only [dist_eq_norm] using (integerRowMassTent_lipschitz K hK z).dist_le_mul x y))
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

theorem inactiveSideLength_lower_power {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) : K < q * 2 ^ h * inactiveSideLength h K q ^ h := by
  have hpos := inactiveSideLength_pos (K := K) hh hq
  have hnext : K / q < (inactiveSideLength h K q + 1) ^ h := by
    simpa [inactiveSideLength, hlarge] using Nat.lt_pow_nthRoot_add_one hh.ne' (K / q)
  have hdiv : K < q * (K / q + 1) := by
    have hm := Nat.mod_lt K hq
    have he := Nat.mod_add_div K q
    nlinarith
  calc
    K < q * (K / q + 1) := hdiv
    _ ≤ q * (inactiveSideLength h K q + 1) ^ h :=
      Nat.mul_le_mul_left q (Nat.succ_le_of_lt hnext)
    _ ≤ q * (2 * inactiveSideLength h K q) ^ h := by gcongr; omega
    _ = _ := by rw [mul_pow]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {J : Type*} [Fintype J]

theorem normalizedSupportPlateau_range (H : ℝ) (x : J → ℝ) :
    0 ≤ normalizedSupportPlateau H x ∧ normalizedSupportPlateau H x ≤ 1 :=
  linearCutoff_range _ _ _

theorem normalizedSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) (x : J → ℝ)
    (hx : ∀ j, |x j| ≤ H) : normalizedSupportPlateau H x = 1 := by
  apply linearCutoff_eq_one _ _ (by norm_num)
  exact (pi_norm_le_iff_of_nonneg hH).mpr (by simpa only [Real.norm_eq_abs] using hx)

theorem normalizedSupportPlateau_support {H : ℝ} (x : J → ℝ)
    (hx : normalizedSupportPlateau H x ≠ 0) : ∀ j, |x j| < H + 1 / 4 := by
  have hn : ‖x‖ < H + 1 / 4 := by
    apply lt_of_not_ge
    intro h
    apply hx
    exact linearCutoff_eq_zero H (1 / 4) (by simpa using h)
  intro j
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  exact hj.trans_lt hn

theorem normalizedSupportPlateau_lipschitz (H : ℝ) :
    LipschitzWith 4 (normalizedSupportPlateau (J := J) H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (linearCutoff_lipschitz H (1 / 4) (by norm_num)).dist_le_mul ‖x‖ ‖y‖
  norm_num only [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    one_div, inv_inv] at h
  exact h.trans (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) (by norm_num))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerSupportTorus
namespace OAI

section

namespace Erdos3

theorem integerSupportTorusFactor_pos (H : ℝ) : 0 < integerSupportTorusFactor H := by
  unfold integerSupportTorusFactor
  omega

theorem grid_scale_factor_le_one (R K j : ℕ) (hR : 0 < R) (hK : 0 < K) :
    ((K : ℝ) / (R * K)) ^ j ≤ 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  apply pow_le_one₀ (by positivity)
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedBlockTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockTorusFactor_pos (q h b : ℕ) (A : ℝ) : 0 < blockTorusFactor q h b A :=
  integerSupportTorusFactor_pos _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedCubePlateau
namespace OAI

section

namespace Erdos3

open scoped BigOperators

instance blockTorusFactor_neZero (q h b : ℕ) (A : ℝ) : NeZero (blockTorusFactor q h b A) :=
  ⟨(blockTorusFactor_pos q h b A).ne'⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem intervalTensorWeight_nonneg {S : Type*} [Fintype S] (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : 0 ≤ intervalTensorWeight B r k x :=
  Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range B hr (k i) (x i)).1)

theorem intervalTensorWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x = 1 := by
  unfold intervalTensorWeight
  rw [← Fintype.prod_sum (fun i k => intervalSiteWeight B r k (x i))]
  simp only [intervalSiteWeight_sum hB hr _ (hx _), Finset.prod_const_one]

theorem intervalTensorWeight_near {S : Type*} [Fintype S] {B r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) (hx : 0 < intervalTensorWeight B r k x) :
    dist x (fun i => intervalSiteCenter B r (k i)) ≤ 2 * r := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hp := productPartitionWeight_pos_coordinate (fun _ : S => intervalSiteWeight B r)
    (fun _ j x => (intervalSiteWeight_range B hr j x).1) k x hx i
  exact (intervalSiteWeight_near B r (k i) (x i) hp).le

theorem intervalTensorApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖F x - intervalTensorApprox B r F x‖ ≤ 2 * K * r := by
  apply norm_sub_positive_sum_le (fun k => intervalTensorWeight B r k x)
    (fun k => F (fun i => intervalSiteCenter B r (k i))) (F x) _
    (fun k => intervalTensorWeight_nonneg B hr k x) (intervalTensorWeight_sum hB hr x hx)
  intro k hk
  have h := hF.dist_le_mul x (fun i => intervalSiteCenter B r (k i))
  rw [dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (intervalTensorWeight_near hr k x hk) K.coe_nonneg).trans_eq (by ring))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {S D : Type*} [Fintype S] [Fintype D]

theorem siteCurry_lipschitz :
    LipschitzWith 1 (fun x : S × D → ℝ => fun s d => x (s, d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro s
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro d
  exact dist_le_pi_dist x y (s, d)

theorem groupedSiteApprox_eq_interval [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ) (x : S → D → ℝ) :
    groupedSiteApprox B r F x =
      intervalTensorApprox B r (fun y : S × D → ℝ => F (fun s d => y (s, d)))
        (fun p => x p.1 p.2) := by
  unfold groupedSiteApprox intervalTensorApprox groupedSiteCoefficient
  apply Finset.sum_congr rfl
  intro k _
  simp only [groupedSiteFactor, vectorIntervalSiteWeight, intervalTensorWeight,
    Complex.ofReal_prod, Fintype.prod_prod_type]
  ring

theorem groupedSiteApprox_error [DecidableEq S] [DecidableEq D]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → D → ℝ) → ℂ)
    {K : ℝ≥0} (hF : LipschitzWith K F) (x : S → D → ℝ)
    (hx : ∀ s d, |x s d| ≤ B) :
    ‖F x-groupedSiteApprox B r F x‖ ≤ 2*K*r := by
  rw [groupedSiteApprox_eq_interval]
  exact intervalTensorApprox_error hB hr _
    (by simpa only [mul_one] using hF.comp (siteCurry_lipschitz (S := S) (D := D)))
    (fun p : S × D => x p.1 p.2) (fun p : S × D => hx p.1 p.2)

theorem groupedSiteCoefficient_sum [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    {A : ℝ} (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ k : S × D → Fin (intervalSiteCount B r), ‖groupedSiteCoefficient B r F k‖) ≤
      (intervalSiteCount B r : ℝ)^(Fintype.card S*Fintype.card D)*A := by
  calc
    _ ≤ ∑ _k : S × D → Fin (intervalSiteCount B r), A := Finset.sum_le_sum (fun k _ => hF _)
    _ = _ := by simp [Fintype.card_prod]

omit [Fintype S] in
theorem groupedSiteFactor_bound (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) :
    ‖groupedSiteFactor B r k s x‖ ≤ 1 :=
  vectorIntervalSiteWeight_bound B hr _ _

omit [Fintype S] in
theorem groupedSiteFactor_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) :
    LipschitzWith (Fintype.card D*((2*intervalSiteCount B r+1)/r))
      (groupedSiteFactor B r k s) :=
  vectorIntervalSiteWeight_lipschitz B hr _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VectorSiteBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_grouped_site_approximation {S D : Type*} [Fintype S] [Fintype D]
    [DecidableEq S] [DecidableEq D]
    (F : (S → D → ℝ) → ℂ) (A K : ℝ≥0) (hA : ∀ x, ‖F x‖ ≤ A)
    (hK : LipschitzWith K F) {B ε P : ℝ} (hB : 0 < B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hBP : B ≤ Real.exp P) (hAP : (A : ℝ) ≤ Real.exp P) (hKP : (K : ℝ) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*P+8) ∧
      ∃ (c : (S × D → Fin n) → ℂ) (f : (S × D → Fin n) → S → (D → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card S*Fintype.card D : ℕ)*(4*P+8)+P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*P+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : S → D → ℝ, (∀ s d, |x s d| ≤ B) →
          ‖F x-∑ k, c k*∏ s, f k s (x s)‖ ≤ ε := by
  let r := regularizationRadius K ε
  have hs := regularizationRadius_spec K.coe_nonneg hε
  have hr : 0 < r := hs.1
  have hi : r⁻¹ ≤ Real.exp (2*P+2) :=
    regularizationRadius_inverse_le_exp K.coe_nonneg hε hP hKP hεP
  have hP' : 0 ≤ 2*P+2 := by positivity
  have hPP' : P ≤ 2*P+2 := by linarith
  have hB' : B ≤ Real.exp (2*P+2) := hBP.trans (Real.exp_le_exp.mpr hPP')
  have hn : (intervalSiteCount B r : ℝ) ≤ Real.exp (4*P+8) := by
    have hb := intervalSiteCount_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have he : 2*(2*P+2)+4 = 4*P+8 := by ring
    simpa only [he] using hb
  have hf : (Fintype.card D : ℝ)*((2*(intervalSiteCount B r : ℝ)+1)/r) ≤
      Real.exp (Fintype.card D+6*P+12) := by
    have hb := intervalSiteLipschitz_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have hd : (Fintype.card D : ℝ) ≤ Real.exp (Fintype.card D : ℝ) := by
      linarith [Real.add_one_le_exp (Fintype.card D : ℝ)]
    calc
      _ ≤ Real.exp (Fintype.card D : ℝ)*Real.exp (3*(2*P+2)+6) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨intervalSiteCount B r, hn, groupedSiteCoefficient B r F, groupedSiteFactor B r, ?_,
    (fun k s x => groupedSiteFactor_bound B hr k s x), ?_, ?_⟩
  · apply (groupedSiteCoefficient_sum B r F hA).trans
    calc
      _ ≤ (Real.exp (4*P+8))^(Fintype.card S*Fintype.card D)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  · intro k s
    have hl := groupedSiteFactor_lipschitz B (r := ⟨r, hr.le⟩) hr k s
    apply hl.weaken
    exact_mod_cast hf
  · intro x hx
    apply (groupedSiteApprox_error hB hr F hK x hx).trans
    have hs' : (K : ℝ)*r ≤ ε/2 := hs.2.2
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SitePlateauCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem scalarSupportPlateau_norm (H x : ℝ) : ‖scalarSupportPlateau H x‖ ≤ 1 := by
  rw [scalarSupportPlateau, Complex.norm_real,
    Real.norm_of_nonneg (normalizedSupportPlateau_range H _).1]
  exact (normalizedSupportPlateau_range H _).2

theorem scalarSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) {x : ℝ} (hx : |x| ≤ H) :
    scalarSupportPlateau H x = 1 := by
  simp only [scalarSupportPlateau, normalizedSupportPlateau_one hH _ (fun _ => hx), Complex.ofReal_one]

theorem scalarSupportPlateau_support (H x : ℝ) (hx : scalarSupportPlateau H x ≠ 0) :
    |x| < H + 1 / 4 := by
  apply normalizedSupportPlateau_support (fun _ : Unit => x) _ ()
  intro hz
  exact hx (by simp only [scalarSupportPlateau, hz, Complex.ofReal_zero])

theorem scalarSupportPlateau_zero {H x : ℝ} (hx : H + 1 / 4 ≤ |x|) :
    scalarSupportPlateau H x = 0 := by
  by_contra hn
  exact (not_lt_of_ge hx) (scalarSupportPlateau_support H x hn)

theorem scalarSupportPlateau_lipschitz (H : ℝ) : LipschitzWith 4 (scalarSupportPlateau H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (normalizedSupportPlateau_lipschitz (J := Unit) H).dist_le_mul
    (fun _ => x) (fun _ => y)
  rw [dist_pi_const] at h
  simpa only [scalarSupportPlateau, dist_eq_norm,
    ← Complex.ofReal_sub, Complex.norm_real] using h

theorem scalarSupportPlateau_mul_lipschitz (H : ℝ) (f : ℝ → ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L f) (hf : ∀ x, ‖f x‖ ≤ 1) :
    LipschitzWith (L + 4) (fun x => scalarSupportPlateau H x * f x) := by
  simpa only [one_mul] using lipschitz_mul_of_bounds (scalarSupportPlateau H) f
    (scalarSupportPlateau_lipschitz H) hL (Bf := 1) (Bg := 1)
    (scalarSupportPlateau_norm H) hf

theorem finite_site_cutoff_error {T S : Type*} [Fintype T] [Fintype S]
    (target : ℂ) (c : T → ℂ) (f : T → S → ℂ) (χ : S → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (hkeep : target ≠ 0 → ∀ s, χ s = 1)
    (he : (∀ s, χ s ≠ 0) → ‖target - ∑ k, c k * ∏ s, f k s‖ ≤ ε) :
    ‖target - ∑ k, c k * ∏ s, χ s * f k s‖ ≤ ε := by
  have hid : (∑ k, c k * ∏ s, χ s * f k s) =
      (∏ s, χ s) * ∑ k, c k * ∏ s, f k s := by
    simp only [Finset.prod_mul_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have ht : (∏ s, χ s) * target = target := by
    by_cases hz : target = 0
    · simp only [hz, mul_zero]
    · simp only [hkeep hz, Finset.prod_const_one, one_mul]
  rw [hid, ← ht, ← mul_sub, norm_mul]
  by_cases hz : ∃ s, χ s = 0
  · obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hs, norm_zero, zero_mul]
    exact hε
  · have hp : ‖∏ s, χ s‖ ≤ 1 := by
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun s _ => hχ s)).trans_eq
        (Finset.prod_const_one)
    exact (mul_le_mul hp (he (fun s hs => hz ⟨s, hs⟩)) (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integer_boolean_reconstruction (y : Finset α → ℤ) (s : Finset α) :
    y s = ∑ t : Finset α, if t ⊆ s then booleanCoefficient y t else 0 := by
  have h := congrArg (fun M : Matrix (Finset α) (Finset α) ℤ => M *ᵥ y)
    (booleanReconstruction_mul_extraction (α := α))
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
  have hv : booleanJetExtractionMatrix (id : Finset α → Finset α) *ᵥ y =
      fun t => booleanCoefficient y t := by
    funext t
    exact booleanJetExtractionMatrix_mulVec id y t
  rw [hv] at h
  have hs := congrFun h s
  simpa only [Matrix.mulVec, dotProduct, booleanReconstructionMatrix,
    ite_mul, one_mul, zero_mul] using hs.symm

theorem integer_boolean_reconstruction_rows (y : Finset α → ℤ)
    (rows : Finset (Finset α)) (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (s : Finset α) :
    y s = ∑ t ∈ rows, if t ⊆ s then booleanCoefficient y t else 0 := by
  rw [integer_boolean_reconstruction y s]
  symm
  apply Finset.sum_subset (Finset.subset_univ rows)
  intro t _ ht
  simp only [hrows t ht, ite_self]

theorem integer_boolean_sites_bound (y : Finset α → ℤ) (rows : Finset (Finset α))
    (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    {H N : ℝ} (hH : 0 ≤ H) (hN : 0 < N)
    (hcoeff : ∀ t ∈ rows, |((booleanCoefficient y t : ℤ) : ℝ)| ≤ H * N) (s : Finset α) :
    |(y s : ℝ) / N| ≤ rows.card * H := by
  have hs : |(y s : ℝ)| ≤ (rows.card : ℝ) * (H * N) := by
    rw [integer_boolean_reconstruction_rows y rows hrows s, Int.cast_sum]
    calc
      _ ≤ ∑ t ∈ rows, |((if t ⊆ s then booleanCoefficient y t else 0 : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ rows, H * N := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs
        · exact hcoeff t ht
        · simp only [Int.cast_zero, abs_zero]
          positivity
      _ = _ := by simp
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  simpa only [mul_assoc] using hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3.ScalarSiteExpansion

open scoped NNReal

universe u v

variable {S : Type u} {e : ScalarSiteExpansion.{u,v} S}

theorem Bounds.mono {T D C H T' D' C' H' : ℝ} {L L' : ℝ≥0}
    (h : e.Bounds T D C L H) (hT : T ≤ T') (hD : D ≤ D') (hC : C ≤ C')
    (hL : L ≤ L') (hH : H ≤ H') : e.Bounds T' D' C' L' H' :=
  ⟨h.card_le.trans hT, h.period_pos, fun i => (h.period_le i).trans hD,
    h.coefficient_le.trans hC, h.factor_bound, fun i s r => (h.lipschitz i s r).weaken hL,
    fun i s r x hx => h.support i s r x (hH.trans hx)⟩

end Erdos3.ScalarSiteExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem selectedBooleanSiteRows_lipschitz (axis : A) (rows : Finset (Finset α)) :
    LipschitzWith ((2 : ℝ≥0) ^ Fintype.card α) (selectedBooleanSiteRows axis rows) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro t
  change |booleanCoefficient (fun s => x s axis) t - booleanCoefficient (fun s => y s axis) t| ≤ _
  apply (booleanCoefficient_sub_bound _ _ _ (H := dist x y) ?_).trans
  · simp only [NNReal.coe_pow, NNReal.coe_ofNat]
    gcongr
    · norm_num
    · exact Finset.card_le_univ _
  · intro s _
    exact (show |x s axis - y s axis| ≤ dist (x s) (y s) from
      dist_le_pi_dist (x s) (y s) axis).trans (dist_le_pi_dist x y s)

omit [Fintype α] [Fintype A] [DecidableEq A] in
theorem selectedBooleanSiteRows_integer (axis : A) (rows : Finset (Finset α))
    (N : A → ℕ) (y : Finset α → A → ℤ) :
    selectedBooleanSiteRows axis rows (fun s d => (y s d : ℝ) / N d) =
      fun t : rows => ((booleanCoefficient (fun s => y s axis) t : ℤ) : ℝ) / N axis := by
  funext t
  rw [selectedBooleanSiteRows, booleanCoefficient_div]
  congr 1
  exact (booleanCoefficient_map (Int.castRingHom ℝ) (fun s => y s axis) t).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

universe uα

theorem exists_bounded_grid_site_expansion
    {α : Type uα} [Fintype α] [DecidableEq α]
    (rows : Finset (Finset α)) (p : PMF (rows → ℤ)) {K Kmax : ℕ}
    (hK : 0 < K) (hKmax : K ≤ Kmax) {H ε P : ℝ} (hH : 0 ≤ H)
    (hsupport : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / K| ≤ H)
    (hε : 0 < ε) (hP : 0 ≤ P) (hHP : H + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (H + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((K : ℝ) ^ rows.card * (p (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
          e.integerEval K y‖ ≤ ε := by
  let F (x : Finset α → Unit → ℝ) : ℂ :=
    integerRowMassInterpolation K p (selectedBooleanSiteRows () rows x)
  have hKreal : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hKnn : (1 : ℝ≥0) ≤ K := by exact_mod_cast hK
  have hmax : (K : ℝ≥0) ≤ Kmax := by exact_mod_cast hKmax
  have hF (x) : ‖F x‖ ≤ (Kmax : ℝ≥0) ^ rows.card := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_of_nonneg (integerRowMassInterpolation_range hKreal.le p _).1]
    apply (integerRowMassInterpolation_range hKreal.le p _).2.trans
    simpa only [Fintype.card_coe, NNReal.coe_pow, NNReal.coe_natCast] using
      pow_le_pow_left₀ hKreal.le (show (K : ℝ) ≤ Kmax by exact_mod_cast hKmax) rows.card
  have hLF : LipschitzWith
      ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
        (2 : ℝ≥0) ^ Fintype.card α) F := by
    have h := (integerRowMassInterpolation_lipschitz (K : ℝ≥0) hKnn p).comp
      (selectedBooleanSiteRows_lipschitz () rows)
    have hc : LipschitzWith
        ((rows.card * (2 * (K : ℝ≥0) ^ 2) * (K : ℝ≥0) ^ rows.card) *
          (2 : ℝ≥0) ^ Fintype.card α) F := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [F, Function.comp_def, Fintype.card_coe, dist_eq_norm,
        ← Complex.ofReal_sub, Complex.norm_real, NNReal.coe_natCast] using h.dist_le_mul x y
    apply hc.weaken
    gcongr
  obtain ⟨N, hN, c, f, hc, hf, hLf, he⟩ := exists_grouped_site_approximation F
    ((Kmax : ℝ≥0) ^ rows.card) _ hF hLF
    (show 0 < H + 1 / 4 by linarith only [hH]) hε hP hHP
    (by simpa only [NNReal.coe_pow, NNReal.coe_natCast] using hcap) hLip hεP
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := Finset α × Unit → Fin N
      period := fun _ => 1
      coefficient := c
      factor := fun k u _ x => scalarSupportPlateau H x * f k u (fun _ => x) }
  refine ⟨e, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change (Fintype.card (Finset α × Unit → Fin N) : ℝ) ≤ _
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_unit,
      mul_one, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _).trans_eq (Real.exp_nat_mul _ _).symm
  · exact fun _ => zero_lt_one
  · intro k
    norm_num only [e, Nat.cast_one]
  · simpa only [Fintype.card_unit, mul_one] using hc
  · intro k u r x
    change ‖scalarSupportPlateau H x * f k u (fun _ => x)‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u r
    apply scalarSupportPlateau_mul_lipschitz H (fun x => f k u (fun _ => x)) _ (fun x => hf k u _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Fintype.card_unit, Nat.cast_one, dist_pi_const] using
      (hLf k u).dist_le_mul (fun _ => x) (fun _ => y)
  · intro k u r x hx
    change scalarSupportPlateau H x * f k u (fun _ => x) = 0
    rw [scalarSupportPlateau_zero hx, zero_mul]
  · intro y hy
    let target : ℂ := (((K : ℝ) ^ rows.card * (p (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ)
    have hkeep : target ≠ 0 → ∀ u, scalarSupportPlateau H ((y u : ℝ) / K) = 1 := by
      intro ht u
      have hp : p (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply ht
        simp only [target, hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      exact scalarSupportPlateau_one hH (hsupport y hy hp u)
    apply finite_site_cutoff_error target c (fun k u => f k u (fun _ => (y u : ℝ) / K))
      (fun u => scalarSupportPlateau H ((y u : ℝ) / K)) hε.le
      (fun u => scalarSupportPlateau_norm _ _) hkeep
    intro hcut
    have herr := he (fun u _ => (y u : ℝ) / K)
      (fun u _ => (scalarSupportPlateau_support _ _ (hcut u)).le)
    have heq : F (fun u _ => (y u : ℝ) / K) = target := by
      dsimp only [F, target]
      rw [show selectedBooleanSiteRows () rows (fun u _ => (y u : ℝ) / K) =
        (fun t : rows => ((booleanCoefficient y t : ℤ) : ℝ) / K) by
          simpa only using selectedBooleanSiteRows_integer () rows (fun _ => K) (fun u _ => y u)]
      rw [integerRowMassInterpolation_grid hKreal, Fintype.card_coe]
    rwa [heq] at herr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom

theorem allocatedPrincipalSides_inactive
    (hsmall : height ≤ S.value ^ degree) (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :
    allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ = side := by
  rw [layerIntegerPrincipalSlots_card]
  change integerAxisSideLength degree height S.value
    (principalProfileSize (R j) (Fintype.card (B ⟨j,Sum.inr i⟩))) = _
  simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false]

theorem allocatedSlicedGrid_cases
    (H : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (Q T : ℕ) (hQT : (Q : ℝ) / δ ≤ T) :
    height ≤ allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T ∨
      ((∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩) ∧
        ((S.value ^ degree < height ∧ ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∨
         (height ≤ S.value ^ degree ∧ 2 * denom ≤ height ∧
           ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)))) := by
  let K := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
  by_cases hK : height ≤ K
  · exact Or.inl hK
  have hlarge : 2 * denom ≤ height := by
    have : 2 * denom ≤ K := by dsimp [K, allocatedSlicedGridHeightCutoff]; omega
    omega
  have hside_bound {L h : ℕ} (hd : δ * L ≤ (h : ℝ)) (hh : h < Q) : L ≤ T := by
    have hl : (L : ℝ) ≤ (Q : ℝ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      have hh' : (h : ℝ) ≤ Q := Nat.cast_le.mpr hh.le
      simpa only [mul_comm] using hd.trans hh'
    exact_mod_cast hl.trans hQT
  have hsize : ∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩ := by
    intro b v
    by_contra hh
    have hL := hside_bound (hdense b v) (Nat.lt_of_not_ge hh)
    apply hK
    by_cases ha : S.value ^ degree < height
    · rw [allocatedPrincipalSides_active B U basis S j i ha b v] at hL
      have hb := hgrid.trans (Nat.pow_le_pow_left hL (layerTailDegree m + 1))
      exact hb.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
    · rw [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] at hL
      have hb := (inactiveSideLength_lower_power (Nat.zero_lt_succ j.val) (inactiveDenominator_pos _) hlarge).le
      have hc := hb.trans (Nat.mul_le_mul_left (denom * 2 ^ degree) (Nat.pow_le_pow_left hL degree))
      exact hc.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
  refine Or.inr ⟨hsize, ?_⟩
  by_cases ha : S.value ^ degree < height
  · refine Or.inl ⟨ha, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_active B U basis S j i ha b v] using hdense b v
  · refine Or.inr ⟨Nat.le_of_not_gt ha, hlarge, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] using hdense b v

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DenseSliceGridScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dense_slice_grid_cardinality {M C S δ : ℝ} (d t : ℕ)
    (hδ : 0 < δ) (hbase : M ^ d ≤ C ^ d * S ^ t) :
    M ^ d ≤ (C ^ d / δ ^ t) * (δ * S) ^ t := by
  calc
    M ^ d ≤ C ^ d * S ^ t := hbase
    _ = _ := by rw [mul_pow]; field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedAxisCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) *
    R j
local notation "scale" => basisAxisScale (b j) i
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

theorem exists_forecastInactive_sliced_fixed_bounded_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (c : ℤ) (hc : constantLaw c ≠ 0)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : scale ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ rows.card *
          (allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows
            (fun t => booleanCoefficient (fun _ : Finset α => c) t)
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ ε := by
  let p := allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r H step lower hH hsubset hcell j i rows
    (fun t => booleanCoefficient (fun _ : Finset α => c) t)
  have hrad : 0 ≤ radius := by
    have := (hR j).le
    positivity
  have hk : (0 : ℝ) < scale :=
    Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)
  have hs : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / scale| ≤ rows.card * radius := by
    intro y hy hm u
    apply integer_boolean_sites_bound y rows hy hrad hk _ u
    intro t ht
    have hb := forecastInactive_sliced_fixed_scaled_support_s2 B U b hR hσ S q r H step lower hH hsubset hcell j i hσ1 hgrid
      rows c hc (fun t => booleanCoefficient y t) hm ⟨t, ht⟩
    rw [abs_div, abs_of_pos hk] at hb
    exact (div_le_iff₀ hk).mp hb
  exact exists_bounded_grid_site_expansion rows p
    (basisAxisScale_pos (b j) i) hKmax (mul_nonneg (Nat.cast_nonneg _) hrad)
    hs hε hP hHP hcap hLip hεP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq hsize in
theorem exists_forecastInactive_sliced_fixed_site_expansion
    (c0 : ℤ) (hc0 : (constantLaw) c0 ≠ 0)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let freq := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val rows.card P V ζ)
    let cap := uniformSpectrumAbsoluteCap j.val rows.card t P V W
    let R0 := (rows.card : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j)
    ∀ {η Q : ℝ}, 0 < η → 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (η / (cap + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        ((uniformSpectrumSizeConstant j.val rows.card t P V W /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t)) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (uniformScaledRetainedDenominatorBound j.val rows.card t P V W ζ)
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows
            (fun t => booleanCoefficient (fun _ : Finset α => c0) t)
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + η := by
  intro V t W ζ freq cap R0 η Q hη hQ hRQ hηQ hLQ
  let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have hside : 0 < side := inactiveSideLength_pos (Nat.zero_lt_succ _) (inactiveDenominator_pos _)
  have hbase : (height : ℝ) ≤ cost * (side : ℝ) ^ degree := by
    exact_mod_cast (inactiveSideLength_lower_power (Nat.zero_lt_succ _) (inactiveDenominator_pos _) hlarge).le
  have hbound : (M : ℝ) ≤ ((torus : ℝ) * cost) * (side : ℝ) ^ degree :=
    hMK.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg torus))
  have hL : 0 ≤ δ * side := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * side) ^ t := by
    apply dense_slice_grid_cardinality rows.card t hδ
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg M) hbound rows.card
  have hKM : height ≤ M := by
    rw [hM]
    exact Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  obtain ⟨D, a, ω, hD, hmodes⟩ := uniformBlockSpectrumCover_modes (J := rows)
    (basisAxisScale_pos (basis j) i) hKM j.val t hL hW
    (by simpa only [Fintype.card_coe] using hcard) (U := P) (V := V) (ζ := ζ)
  let : ∀ k, NeZero (D k) := fun k => ⟨(hD k).ne'⟩
  obtain ⟨hF, hcap, hpoint⟩ := allocatedSupportedSlicedInactivePointApproximation_error_s2
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hsmall hlarge
    hδ hlength hstep A hA P hP hsP hstride hM rows hrows hB hε hε1
  have hRj : 0 ≤ R j := (hR j).le
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  obtain ⟨N, hN, hcount, β, f, hβ, hf, hLf, he⟩ := exists_affineCube_plateau_site_approximation_s2
    sources lower strides (PMF.pure c0) (basisAxisScale_pos (basis j) i) radius rows F D a ω
    (fun k hk => (hmodes k hk).2.2)
    (fun zeta t => booleanCoefficient (fun _ : Finset α => zeta) t) hscale
    hcap freq
    (fun k hk t => (by simpa only [Fintype.card_coe] using (hmodes k hk).2.1 t :
      |ω k t| ≤ uniformScaledRetainedFrequencyBound j.val rows.card P V ζ).trans (Real.le_coe_toNNReal _))
    (R := R0 + 1 / 4) (by positivity) hη hQ hRQ hηQ hLQ
  let g (k : PlateauSiteIndex α F N) (u : Finset α) (v : ZMod (D k.1)) (z : ℝ) : ℂ :=
    scalarSupportPlateau R0 z * f k u v z
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := PlateauSiteIndex α F N
      period := fun k => D k.1
      coefficient := β
      factor := g }
  refine ⟨e, ⟨?_, (fun k => hD k.1), ?_, hβ, ?_, ?_, ?_⟩, ?_⟩
  · exact hcount.trans (mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _))
  · intro k
    simpa only [Fintype.card_coe] using (hmodes k.1 k.1.property).1
  · intro k u v z
    change ‖scalarSupportPlateau R0 z * f k u v z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u v z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u v
    exact scalarSupportPlateau_mul_lipschitz R0 (f k u v) (hLf k u v) (hf k u v)
  · intro k u v z hz
    change scalarSupportPlateau R0 z * f k u v z = 0
    rw [scalarSupportPlateau_zero hz, zero_mul]
  · intro y hy
    let target : ℂ := (((height : ℝ) ^ rows.card *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows
        (fun t => booleanCoefficient (fun _ : Finset α => c0) t)
        (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ)
    let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
      ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
    have hkeep : target ≠ 0 → ∀ u, scalarSupportPlateau R0 ((y u : ℝ) / height) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows
          (fun t => booleanCoefficient (fun _ : Finset α => c0) t)
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [target, hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      have hmixed : allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x₀
          (fun t => booleanCoefficient y t) ≠ 0 := by
        unfold allocatedSupportedSlicedPhysicalGridPMF
        rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2 B U basis hR hσ S q r H step c hH hsubset hcell
          j i hgrid rows x₀]
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨c0, hc0, hmass⟩
      apply scalarSupportPlateau_one hR0
      apply integer_boolean_sites_bound y rows hy (by positivity) (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
      intro t ht
      have hb := allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2 B U basis hR hσ S q r H step c hH hsubset hcell
        j i hσ1 rows x₀ (fun t => booleanCoefficient y t) hmixed ⟨t, ht⟩
      have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
      rw [abs_div, abs_of_pos hk] at hb
      exact (div_le_iff₀ hk).mp hb
    apply finite_site_cutoff_error target β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / height))
      (fun u => scalarSupportPlateau R0 ((y u : ℝ) / height))
      (show 0 ≤ ε + η by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
    intro hcut
    have hsite := he y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le)
    have hp := hpoint (fun t => booleanCoefficient (fun _ : Finset α => c0) t)
      (fun t => booleanCoefficient y t)
    simp only [PMF.toMeasure_pure, MeasureTheory.integral_dirac] at hsite
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hp hsite)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => j.val + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card α) degree
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

variable (δ P ε : ℝ) (rows : Finset (Finset α))

local notation "V" => (torus : ℝ) * cost / δ ^ degree
local notation "t" => degree * rows.card
local notation "W" => ((torus : ℝ) * cost) ^ rows.card / δ ^ t
local notation "bias" => uniformBlockRetainedBias j.val rows.card t P V W ε
local notation "freq" => Real.toNNReal (uniformScaledRetainedFrequencyBound j.val rows.card P V bias)
local notation "cap" => uniformSpectrumAbsoluteCap j.val rows.card t P V W
local notation "sizeBound" => uniformSpectrumSizeConstant j.val rows.card t P V W /
  ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t)
local notation "periodBound" => uniformScaledRetainedDenominatorBound j.val rows.card t P V W bias
local notation "cutoff" => allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i
  (Nat.ceil (((((Fintype.card α + 1) * q) : ℕ) : ℝ) / δ))

include hq in
theorem exists_forecastInactive_sliced_fixed_site_all_cases_s2_oai
    (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (hsmall : height ≤ S.value ^ degree)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (c0 : ℤ) (hc0 : constantLaw c0 ≠ 0)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hrows : ∀ u ∈ rows, u.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card t ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {η Q : ℝ} (hη : 0 < η) (hQ : 0 ≤ Q)
    (hRQ : rows.card * radius + 1 / 4 ≤ Real.exp Q)
    (hηQ : (η / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q)
    (hshortCap : (cutoff : ℝ) ^ rows.card ≤ Real.exp Q)
    (hshortLip : ((rows.card * (2 * (cutoff : ℝ≥0) ^ 2) * (cutoff : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q)
    (hshortError : η⁻¹ ≤ Real.exp Q) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (max (sizeBound * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
          (Real.exp (Fintype.card (Finset α) * (4 * Q + 8))))
        (max periodBound 1)
        (max (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
          (Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q)))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ u ∉ rows, booleanCoefficient y u = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step lower hH hsubset hcell j i rows
            (fun u => booleanCoefficient (fun _ : Finset α => c0) u)
            (fun u => booleanCoefficient y u)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + η := by
  rcases allocatedSlicedGrid_cases B U basis S j i H hgrid hδ hdense
      ((Fintype.card α + 1) * q) _ (Nat.le_ceil _) with hbounded | ⟨hsize, hcases⟩
  · obtain ⟨e, he, herr⟩ := exists_forecastInactive_sliced_fixed_bounded_site_expansion
      B U basis hR hσ S q r H step lower hH hsubset hcell j i hσ1 hgrid c0 hc0 rows
      hbounded hη hQ hRQ hshortCap hshortLip hshortError
    refine ⟨e, he.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) le_rfl le_rfl, ?_⟩
    intro y hy
    exact (herr y hy).trans (le_add_of_nonneg_left hε.le)
  · rcases hcases with ⟨hactive, _⟩ | ⟨_, hlarge, hlength⟩
    · exact False.elim ((Nat.not_lt.mpr hsmall) hactive)
    · let M := torus * height
      let _ : NeZero M := ⟨(Nat.mul_pos (blockTorusFactor_pos _ _ _ _)
        (basisAxisScale_pos (basis j) i)).ne'⟩
      obtain ⟨e, he, herr⟩ := exists_forecastInactive_sliced_fixed_site_expansion
        B U basis hR hσ S q hq r H step lower hH hsubset hcell j i hsize c0 hc0
        hgrid hsmall hlarge hδ hlength hstep A hA P hP hsP hstride (M := M) rfl
        rows hrows hB hε hε1 hσ1 hη hQ hRQ hηQ hLQ
      exact ⟨e, he.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) le_rfl le_rfl, herr⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_site_all_cases_s2_oai.{uα, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_fixed_site_all_cases_s2_oai.{uα, u_1, u_2, u_3, u_4}
