-- Prove2me | solution 1 for OAI.Erdos3.chosen_stable_residue_affine_total_at_degree_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:51:26.010825+00:00
-- url     : https://prove2.me/submissions/de2a1825-1a31-4714-9220-368408c4cf42

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197
import Theorems.Thm_OAI_Erdos3_retained_residue_marginals_of_lengths_s2
import Theorems.Thm_OAI_Erdos3_stable_residue_kernel_total_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem additiveCharacterKernel_ne_top {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    additiveCharacterKernel χ ≠ ⊤ := by
  intro h
  apply hχ
  ext x
  change χ x = 1
  have hx : x ∈ additiveCharacterKernel χ := by rw [h]; trivial
  exact hx

variable [Fintype G]

theorem primePowerCharacter_kernel_index {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    p ≤ (additiveCharacterKernel χ).index := by
  have hd : (additiveCharacterKernel χ).index ∣ p ^ a := by
    rw [← hG, ← Nat.card_eq_fintype_card]
    exact (additiveCharacterKernel χ).index_dvd_card
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hbpos : 0 < b := by
    by_contra hn
    have hbzero : b = 0 := by omega
    rw [hbzero, pow_zero] at hb
    exact additiveCharacterKernel_ne_top hχ ((additiveCharacterKernel χ).index_eq_one.mp hb)
  rw [hb]
  simpa only [pow_one] using Nat.pow_le_pow_right hp.one_le hbpos

theorem primePowerCharacter_kernel_probability {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ≤ (p : ℝ)⁻¹ := by
  classical
  let K := additiveCharacterKernel χ
  have hindex := primePowerCharacter_kernel_index hp hG hχ
  have hc : (Fintype.card K : ℝ) * K.index = Fintype.card G := by
    have h : Fintype.card K * K.index = Fintype.card G := by
      simpa only [Nat.card_eq_fintype_card] using K.card_mul_index
    exact_mod_cast h
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcard : (Finset.univ.filter (fun x : G => χ x = 1)).card = Fintype.card K := by
    simp [K, additiveCharacterKernel, Fintype.card_subtype]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_boole, hcard]
  apply (div_le_iff₀ hN).mpr
  have hi : (p : ℝ) ≤ K.index := by exact_mod_cast hindex
  calc
    _ ≤ (p : ℝ)⁻¹ * ((Fintype.card K : ℝ) * K.index) := by
      apply (le_inv_mul_iff₀ hp0).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card K)]
    _ = _ := by rw [hc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy
namespace OAI

section

namespace Erdos3

theorem exp_neg_le_exp_neg_div_eight {A B : ℝ} (hAB : B + 4 ≤ A) :
    Real.exp (-A) ≤ Real.exp (-B) / 8 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    calc
      8 ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp (-(B + 4)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 4 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h8

theorem exp_neg_le_half_exp_neg {A B : ℝ} (hAB : B + 1 ≤ A) :
    Real.exp (-A) ≤ (1 / 2) * Real.exp (-B) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-(B + 1)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 1 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-B) / 2 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h2
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

theorem mem_lowDegreeCoordinateSets (b : ℕ) (S : Finset I) :
    S ∈ lowDegreeCoordinateSets I b ↔ S.card ≤ b := by
  simp only [lowDegreeCoordinateSets, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨j, hj, hcard⟩
    omega
  · intro h
    exact ⟨S.card, by omega, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

theorem mem_bounded (b : ℕ) (c : ProductCylinder X) :
    c ∈ bounded (X := X) b ↔ c.1.card ≤ b := by
  classical
  simp only [bounded, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mass_mono (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    {f g : (∀ i, X i) → ℝ} (hfg : ∀ x, f x ≤ g x) (c : ProductCylinder X) :
    c.mass μ base f ≤ c.mass μ base g :=
  (FiniteProbabilityWeights.pi μ).mean_mono (fun _ => hfg _)

end ProductCylinder

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

theorem bounded_card (b : ℕ) :
    (bounded (X := X) b).card =
      ∑ S ∈ lowDegreeCoordinateSets ι b, ∏ i : S, Fintype.card (X i.val) := by
  classical
  have he : bounded (X := X) b =
      (lowDegreeCoordinateSets ι b).sigma (fun S => (Finset.univ : Finset (∀ i : S, X i.val))) := by
    ext c
    simp only [mem_bounded, Finset.mem_sigma, mem_lowDegreeCoordinateSets, Finset.mem_univ, and_true]
  rw [he, Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_pi]

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem ProductMarginalsClose.mono {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s t : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (ht : t ≤ s) : ProductMarginalsClose μ rho eta t :=
  fun B hB x hx => h B (hB.trans ht) x hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricSpectralBudgets
namespace OAI

section

namespace Erdos3

theorem geometric_tail_after_cutoff {ε P κ B : ℝ} {r : ℕ}
    (hε : 0 < ε) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hB0 : 0 ≤ B) (hB : B ≤ Real.exp P)
    (hr : CyclicCrootSisask.spectralIterations ε P ≤ r) :
    κ ^ r * B ≤ ε / 16 := by
  have hp : κ ^ r ≤ (1 / 2 : ℝ) ^ CyclicCrootSisask.spectralIterations ε P :=
    (pow_le_pow_left₀ hκ0 hκhalf r).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hr)
  exact (mul_le_mul hp hB hB0 (by positivity)).trans
    (CyclicCrootSisask.half_pow_spectralIterations_mul_exp_le hε)

theorem inverse_power_low_level_bound {t κ A B L : ℝ} {d e : ℕ}
    (ht : 2 ≤ t) (hL : 0 ≤ L)
    (hAB : A ^ 2 * B ^ 2 ≤ L * t ^ d) (hκ : κ ≤ (t ^ (d + e))⁻¹) :
    κ * A ^ 2 * B ^ 2 ≤ (1 / 2 : ℝ) ^ e * L := by
  have ht0 : 0 < t := by linarith
  have hi : t⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) ht
  calc
    κ * A ^ 2 * B ^ 2 = κ * (A ^ 2 * B ^ 2) := by ring
    _ ≤ (t ^ (d + e))⁻¹ * (L * t ^ d) :=
      mul_le_mul hκ hAB (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
    _ = L * ((t ^ d)⁻¹ * t ^ d) * (t ^ e)⁻¹ := by rw [pow_add, mul_inv_rev]; ring
    _ = L * (t⁻¹) ^ e := by rw [inv_mul_cancel₀ (pow_ne_zero _ ht0.ne'), mul_one, inv_pow]
    _ ≤ L * (1 / 2 : ℝ) ^ e :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr ht0.le) hi e) hL
    _ = (1 / 2 : ℝ) ^ e * L := mul_comm _ _

theorem low_level_after_power_cutoff {ε P t κ A B L : ℝ} {d e : ℕ}
    (hε : 0 < ε) (ht : 2 ≤ t) (hL0 : 0 ≤ L) (hL : L ≤ Real.exp P)
    (hAB : A ^ 2 * B ^ 2 ≤ L * t ^ d) (hκ : κ ≤ (t ^ (d + e))⁻¹)
    (he : CyclicCrootSisask.spectralIterations ε P ≤ e) :
    κ * A ^ 2 * B ^ 2 ≤ ε / 16 := by
  exact (inverse_power_low_level_bound ht hL0 hAB hκ).trans
    (geometric_tail_after_cutoff hε (by norm_num) (by norm_num) hL0 hL he)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedCoreBudget
namespace OAI

section

namespace Erdos3

theorem retained_core_allowance_spec {ε : ℝ} (hε : 0 < ε) :
    0 < ε / (2 + ε) ∧ ε / (2 + ε) ≤ 1 ∧ (ε / (2 + ε)) * (2 + ε) ≤ ε := by
  have hd : 0 < 2 + ε := by linarith
  refine ⟨div_pos hε hd, (div_le_one hd).mpr (by linarith), ?_⟩
  exact le_of_eq (div_mul_cancel₀ ε hd.ne')

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineDegreeChoice
namespace OAI

section

namespace Erdos3

theorem affineFinalDegree_bounds (j r : ℕ) (shell Q : ℝ) :
    j + r ≤ affineFinalDegree j r shell Q ∧
    j + CyclicCrootSisask.spectralIterations shell Q ≤ affineFinalDegree j r shell Q := by
  unfold affineFinalDegree
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

theorem affineComparisonScale_bounds {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) :
    0 ≤ affineComparisonScale ε L T C ∧
    L + T + 2 ≤ affineComparisonScale ε L T C ∧
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤ affineComparisonScale ε L T C ∧
    C ≤ affineComparisonScale ε L T C := by
  have hn : (0 : ℝ) ≤ (affineRemovalDepth T + affineComparisonTail ε L T : ℕ) := Nat.cast_nonneg _
  unfold affineComparisonScale
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem affineComparisonScale_count {ι : Type*} [Fintype ι] {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C) :
    (Fintype.card ι : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) :=
  hcount.trans (Real.exp_le_exp.mpr (affineComparisonScale_bounds (ε := ε) hL hT hC).2.2.2)

theorem affineComparisonMoment_bounds {P : ℝ} (hP : 0 ≤ P) :
    2 ≤ affineComparisonMoment P ∧ Even (affineComparisonMoment P) ∧
    P ≤ (affineComparisonMoment P : ℝ) ∧ (affineComparisonMoment P : ℝ) ≤ P + 2 := by
  unfold affineComparisonMoment
  refine ⟨by omega, even_two_mul _, ?_, ?_⟩
  · have h := Nat.lt_floor_add_one (P / 2)
    push_cast
    linarith
  · have h := Nat.floor_le (by positivity : 0 ≤ P / 2)
    push_cast
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

theorem affineComparisonContraction_bounds {ξ P : ℝ} (hξ : 0 < ξ) (hP : 0 ≤ P) :
    0 < affineComparisonContraction ξ P ∧ affineComparisonContraction ξ P ≤ 1 / 2 ∧
    affineComparisonContraction ξ P * (8 * (1 + 2) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16 := by
  have ht : 2 ≤ P + 2 := by linarith
  have hthreshold : 2 ≤ affineComparisonPrimeThreshold ξ P := by
    unfold affineComparisonPrimeThreshold
    calc
      2 ≤ P + 2 := ht
      _ = (P + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hp : 0 < affineComparisonPrimeThreshold ξ P := by linarith
  refine ⟨inv_pos.mpr hp, ?_, ?_⟩
  · simpa only [affineComparisonContraction, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hthreshold
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hc : (147456 : ℝ) ≤ Real.exp 18 := by
      calc
        147456 ≤ (2 : ℝ) ^ 18 := by norm_num
        _ ≤ (Real.exp 1) ^ 18 := pow_le_pow_left₀ (by norm_num) htwo 18
        _ = _ := by rw [← Real.exp_nat_mul]; norm_num
    exact low_level_after_power_cutoff (d := 4) hξ ht (by norm_num) hc
      (by ring_nf; exact le_rfl) le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem mem_affineMandatoryPrimes {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (i : ι) :
    i ∈ affineMandatoryPrimes prime ξ P ↔ (prime i : ℝ) ≤ affineComparisonPrimeThreshold ξ P := by
  simp only [affineMandatoryPrimes, Finset.mem_filter, Finset.mem_univ, true_and]

theorem affineMandatoryPrimes_outside_inverse {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) {ξ P : ℝ} (hP : 0 ≤ P) (K : Finset ι)
    (hK : affineMandatoryPrimes prime ξ P ⊆ K) (i : ι) (hi : i ∉ K) :
    (prime i : ℝ)⁻¹ ≤ affineComparisonContraction ξ P := by
  have ht : 0 < affineComparisonPrimeThreshold ξ P := by unfold affineComparisonPrimeThreshold; positivity
  have hp : affineComparisonPrimeThreshold ξ P ≤ (prime i : ℝ) := by
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hi (hK ((mem_affineMandatoryPrimes prime ξ P i).mpr h))
  simpa only [affineComparisonContraction, one_div] using one_div_le_one_div_of_le ht hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_mono {f g : Ω → ℝ} (hfg : ∀ z, f z ≤ g z) (x : ∀ i, X i) :
    observedProductDensity μ p F f x ≤ observedProductDensity μ p F g x := by
  classical
  apply div_le_div_of_nonneg_right _ ((FiniteProbabilityWeights.pi μ).nonneg x)
  apply p.mean_mono
  intro z
  split_ifs
  · exact hfg z
  · exact le_rfl

theorem observedProductDensity_add (f g : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (fun z => f z + g z) x =
      observedProductDensity μ p F f x + observedProductDensity μ p F g x := by
  classical
  have he : p.fiberMean F x (fun z => f z + g z) = p.fiberMean F x f + p.fiberMean F x g := by
    unfold FiniteProbabilityWeights.fiberMean
    rw [← p.mean_add]
    congr 1
    funext z
    split_ifs <;> simp
  change p.fiberMean F x (fun z => f z + g z) / _ = p.fiberMean F x f / _ + p.fiberMean F x g / _
  rw [he, add_div]

theorem observedProductDensity_marginal_le (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (hf : ∀ z, f z ≤ 1) {η : ℝ} {r : ℕ}
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η r)
    (S : Finset ι) (hS : S.card ≤ r) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x ≤ 1 + η := by
  have hm : productConditionalMean μ S (observedProductDensity μ p F f) x ≤
      productConditionalMean μ S (observedProductDensity μ p F (fun _ => 1)) x :=
    (FiniteProbabilityWeights.pi μ).mean_mono
      (fun y => observedProductDensity_mono μ p F hf (productCoordinateMix S x y))
  have hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (x i))).ne'
  have hb := (abs_le.mp (hbase S hS x hx)).2
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

theorem cut_add_erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) :
    c.cut F w z + c.erase F w z = w z := by
  unfold cut erase
  split_ifs <;> simp

theorem cut_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.cut F w z := by
  unfold cut
  split_ifs <;> simp [hw]

theorem erase_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.erase F w z := by
  unfold erase
  split_ifs <;> simp [hw]

theorem cut_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.cut F w z ≤ w z := by
  unfold cut
  split_ifs <;> simp [hw]

theorem erase_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.erase F w z ≤ w z := by
  unfold erase
  split_ifs <;> simp [hw]

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

theorem density_cut (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.cut F w) x =
      if c.Contains x then observedProductDensity μ p F w x else 0 := by
  classical
  by_cases hx : c.Contains x
  · rw [if_pos hx]
    change p.fiberMean F x (c.cut F w) / _ = p.fiberMean F x w / _
    congr 1
    unfold FiniteProbabilityWeights.fiberMean
    congr 1
    funext z
    by_cases hz : F z = x
    · simp [cut, hz, hx]
    · simp [hz]
  · rw [if_neg hx]
    have he : p.fiberMean F x (c.cut F w) = 0 := by
      calc
        _ = p.mean (fun _ => 0) := by
          unfold FiniteProbabilityWeights.fiberMean
          congr 1
          funext z
          by_cases hz : F z = x
          · simp [cut, hz, hx]
          · simp [hz]
        _ = 0 := p.mean_const 0
    change p.fiberMean F x (c.cut F w) / _ = 0
    rw [he, zero_div]

theorem density_erase (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.erase F w) x =
      if c.Contains x then 0 else observedProductDensity μ p F w x := by
  classical
  have he : (fun z => c.cut F w z + c.erase F w z) = w := funext (c.cut_add_erase F w)
  have hs := observedProductDensity_add μ p F (c.cut F w) (c.erase F w) x
  rw [he, c.density_cut] at hs
  by_cases hx : c.Contains x
  · rw [if_pos hx] at hs ⊢
    linarith
  · rw [if_neg hx] at hs ⊢
    linarith

theorem mass_erase_self (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.mass μ base (observedProductDensity μ p F (c.erase F w)) = 0 := by
  have hc (y : ∀ i, X i) : c.Contains (productCoordinateMix c.1 (c.assignment base) y) := by
    intro i
    simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property
  change (FiniteProbabilityWeights.pi μ).mean
    (fun y => observedProductDensity μ p F (c.erase F w) (productCoordinateMix c.1 (c.assignment base) y)) = 0
  have he : (fun y => observedProductDensity μ p F (c.erase F w)
      (productCoordinateMix c.1 (c.assignment base) y)) = (fun _ => 0) := by
    funext y
    rw [c.density_erase, if_pos (hc y)]
  rw [he, FiniteProbabilityWeights.mean_const]

omit [∀ i, DecidableEq (X i)] in
theorem mass_erase_le (c d : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) :
    d.mass μ base (observedProductDensity μ p F (c.erase F w)) ≤
      d.mass μ base (observedProductDensity μ p F w) :=
  mass_mono μ base (observedProductDensity_mono μ p F (c.erase_le F w hw)) d

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)

theorem mass_cut_self : c.mass μ base (observedProductDensity μ p F (c.cut F w)) =
    c.mass μ base (observedProductDensity μ p F w) := by
  unfold mass productConditionalMean
  congr 1
  funext y
  rw [c.density_cut]
  apply if_pos
  intro i
  simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} {X : ι → Type*}

theorem removedCylinderWeights_length (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (cs : List (ProductCylinder X)) : (removedCylinderWeights F w cs).length = cs.length := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih => simp only [removedCylinderWeights, List.length_cons, ih]

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}

theorem CylinderRemovalChain.mem_mass_gt (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hw : ∀ z, 0 ≤ w z) {d : ProductCylinder X} (hd : d ∈ cs) :
    τ < d.mass μ base (observedProductDensity μ p F w) := by
  revert hw hd
  induction hchain with
  | nil => intro hw hd; simp only [List.not_mem_nil] at hd
  | @cons w v cs c hsize hmass hbounded rest ih =>
    intro hw hd
    rcases List.mem_cons.mp hd with hd | hd
    · subst d
      exact hmass
    · exact (ih (c.erase_nonneg F w hw) hd).trans_le (c.mass_erase_le d μ base p F w hw)

theorem CylinderRemovalChain.nodup [∀ i, DecidableEq (X i)]
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hτ : 0 ≤ τ) (hw : ∀ z, 0 ≤ w z) : cs.Nodup := by
  revert hw
  induction hchain with
  | nil => intro _; exact List.nodup_nil
  | @cons w v cs c hsize hmass hbounded rest ih =>
    intro hw
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (c.erase_nonneg F w hw)⟩
    intro hc
    have hm := rest.mem_mass_gt (c.erase_nonneg F w hw) hc
    rw [c.mass_erase_self] at hm
    linarith

end Erdos3

end

section

namespace Erdos3

theorem CylinderRemovalChain.removed_size_mass {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), cf.1.1.card ≤ j ∧
      τ < cf.1.mass μ base (observedProductDensity μ p F cf.2) := by
  induction hchain with
  | nil =>
    intro cf hcf
    simp only [removedCylinderWeights, List.zip_nil_left, List.not_mem_nil] at hcf
  | @cons w v cs d hsize hmass hbounded rest ih =>
    intro cf hcf
    change cf ∈ (d, d.cut F w) :: cs.zip (removedCylinderWeights F (d.erase F w) cs) at hcf
    rcases List.mem_cons.mp hcf with hcf | hcf
    · subst cf
      exact ⟨hsize, by rwa [d.mass_cut_self μ base p F w]⟩
    · exact ih cf hcf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem removedCylinderWeights_bounds {Ω ι : Type*} {X : ι → Type*}
    (F : Ω → ∀ i, X i) (w : Ω → ℝ) (cs : List (ProductCylinder X))
    (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1)
    {f : Ω → ℝ} (hf : f ∈ removedCylinderWeights F w cs) (z : Ω) :
    0 ≤ f z ∧ f z ≤ 1 := by
  induction cs generalizing w with
  | nil => simp only [removedCylinderWeights, List.not_mem_nil] at hf
  | cons c cs ih =>
    change f ∈ c.cut F w :: removedCylinderWeights F (c.erase F w) cs at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨c.cut_nonneg F w hw0 z, (c.cut_le F w hw0 z).trans (hw1 z)⟩
    · exact ih (c.erase F w) (c.erase_nonneg F w hw0)
        (fun x => (c.erase_le F w hw0 x).trans (hw1 x)) hf

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

omit [NeZero q] in
theorem residueColumnMap_single (V : J → G) (j : J) :
    residueColumnMap (q := q) V (Pi.single j (1 : ZMod q)) = V j := by
  simp [residueColumnMap, Pi.single_apply, ite_smul]

theorem additiveCharacter_zmod_smul (χ : AddChar G ℂ) (t : ZMod q) (x : G) :
    χ (t • x) = χ x ^ t.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val t, Nat.cast_smul_eq_nsmul]
  exact χ.map_nsmul_eq_pow t.val x

theorem residueColumn_character_zero_iff (V : J → G) (χ : AddChar G ℂ) :
    χ.compAddMonoidHom (residueColumnMap (q := q) V) = 0 ↔ ∀ j, χ (V j) = 1 := by
  constructor
  · intro h j
    have hh := DFunLike.congr_fun h (Pi.single j (1 : ZMod q))
    simpa only [AddChar.compAddMonoidHom_apply, residueColumnMap_single, AddChar.zero_apply] using hh
  · intro h
    ext t
    change χ (∑ j, t j • V j) = 1
    exact (additiveCharacterKernel χ).sum_mem (fun j _ => by
      change χ (t j • V j) = 1
      rw [additiveCharacter_zmod_smul, h, one_pow])

theorem residueColumn_character_mean (V : J → G) (χ : AddChar G ℂ) :
    (𝔼 t : J → ZMod q, χ (residueColumnMap (q := q) V t)) =
      if ∀ j, χ (V j) = 1 then 1 else 0 := by
  have h := AddChar.expect_eq_ite (χ.compAddMonoidHom (residueColumnMap (q := q) V))
  simpa only [AddChar.compAddMonoidHom_apply, residueColumn_character_zero_iff] using h

variable [Fintype G]

theorem finiteFourierCoeff_residueColumnAverage (V : J → G) (f : G → ℂ) (χ : AddChar G ℂ) :
    finiteFourierCoeff (residueColumnAverage (q := q) V f) χ =
      (if ∀ j, χ (V j) = 1 then 1 else 0) * finiteFourierCoeff f χ := by
  have htranslate (a : G) : finiteFourierCoeff (fun x => f (x + a)) χ =
      χ a * finiteFourierCoeff f χ := by
    have h := finiteFourierCoeff_translate f (-a) χ
    rw [AddChar.map_neg_eq_conj] at h
    simpa only [sub_neg_eq_add, Complex.star_def, starRingEnd_self_apply] using h
  unfold finiteFourierCoeff residueColumnAverage
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  change (𝔼 t : J → ZMod q, finiteFourierCoeff (fun x => f (x + residueColumnMap (q := q) V t)) χ) = _
  simp_rw [htranslate]
  rw [← Finset.expect_mul, residueColumn_character_mean]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J G : Type*} [Fintype J] [AddCommGroup G] [Fintype G]

theorem residueColumn_survival_probability (χ : AddChar G ℂ) :
    (𝔼 V : J → G, if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) =
      (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J := by
  have hpoint (V : J → G) :
      (if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) =
        ∏ j, if χ (V j) = 1 then (1 : ℝ) else 0 := by
    by_cases h : ∀ j, χ (V j) = 1
    · simp [h]
    · rw [if_neg h]
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  calc
    _ = 𝔼 V : J → G, ∏ j, if χ (V j) = 1 then (1 : ℝ) else 0 :=
      Finset.expect_congr rfl (fun V _ => hpoint V)
    _ = (∑ x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J /
        (Fintype.card G : ℝ) ^ Fintype.card J := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Nat.cast_pow]
      congr 1
      simpa using (Fintype.prod_sum
        (fun _j : J => fun x : G => if χ x = 1 then (1 : ℝ) else 0)).symm
    _ = _ := by rw [Fintype.expect_eq_sum_div_card, div_pow]

variable {q : ℕ} [NeZero q] [Module (ZMod q) G]

theorem residueColumnAverage_energy (V : J → G) (f : G → ℂ) :
    (𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) =
      ∑ χ : AddChar G ℂ,
        (if ∀ j, χ (V j) = 1 then (1 : ℝ) else 0) * ‖finiteFourierCoeff f χ‖ ^ 2 := by
  rw [← finiteFourier_parseval]
  apply Finset.sum_congr rfl
  intro χ _
  rw [finiteFourierCoeff_residueColumnAverage]
  split_ifs <;> simp

theorem residueColumnAverage_mean_energy (f : G → ℂ) :
    (𝔼 V : J → G, 𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) =
      ∑ χ : AddChar G ℂ,
        (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ^ Fintype.card J *
          ‖finiteFourierCoeff f χ‖ ^ 2 := by
  simp_rw [residueColumnAverage_energy]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [← Finset.expect_mul, residueColumn_survival_probability]

theorem primeAffine_contraction_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℂ) (hf : (𝔼 x, f x) = 0) :
    (𝔼 V : J → G, 𝔼 x : G, ‖residueColumnAverage (q := q) V f x‖ ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (𝔼 x : G, ‖f x‖ ^ 2) := by
  rw [residueColumnAverage_mean_energy]
  calc
    _ ≤ ∑ χ : AddChar G ℂ, (p : ℝ)⁻¹ ^ Fintype.card J *
        ‖finiteFourierCoeff f χ‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro χ _
      by_cases hχ : χ = 0
      · subst χ
        have hz : finiteFourierCoeff f 0 = 0 := by
          simpa [finiteFourierCoeff] using hf
        simp [hz]
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_pow_left₀
          (Finset.expect_nonneg (fun x _ => by split_ifs <;> norm_num))
          (primePowerCharacter_kernel_probability hp hG hχ) _
    _ = _ := by rw [← Finset.mul_sum, finiteFourier_parseval]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

theorem residueColumnAverage_ofReal (V : J → G) (f : G → ℝ) (x : G) :
    residueColumnAverage (q := q) V (fun y => (f y : ℂ)) x =
      (residueColumnRealAverage (q := q) V f x : ℂ) := by
  simp only [residueColumnAverage, residueColumnRealAverage, Fintype.expect_eq_sum_div_card,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

variable [Fintype G]

theorem primeAffine_real_contraction_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℝ) (hf : (𝔼 x, f x) = 0) :
    (𝔼 V : J → G, 𝔼 x : G, residueColumnRealAverage (q := q) V f x ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (𝔼 x : G, f x ^ 2) := by
  have hfc : (𝔼 x : G, (f x : ℂ)) = 0 := by
    have hc := congrArg (fun y : ℝ => (y : ℂ)) hf
    simpa only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum,
      Complex.ofReal_natCast, Complex.ofReal_zero] using hc
  have h := primeAffine_contraction_sq (q := q) (J := J) hp hG (fun x => (f x : ℂ)) hfc
  simpa only [residueColumnAverage_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G] [Fintype G]

theorem residueAffineKernel_centered_sq {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) (f : G → ℝ)
    (hf : (FiniteProbabilityWeights.uniform G).mean f = 0) :
    (residueAffineSource (J := J) (G := G)).mean (fun z => (residueAffineKernel (q := q) z).mean f ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (FiniteProbabilityWeights.uniform G).mean (fun x => f x ^ 2) := by
  simp only [residueAffineSource, FiniteProbabilityWeights.mean_prod, residueAffineKernel_mean,
    FiniteProbabilityWeights.uniform_mean]
  exact primeAffine_real_contraction_sq hp hG f (by simpa only [FiniteProbabilityWeights.uniform_mean] using hf)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateReference_weight_pos {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (i : ι) (x : σ → ZMod (q i)) :
    0 < (primeCoordinateReference (σ := σ) q i).weight x := by
  dsimp only [primeCoordinateReference, FiniteProbabilityWeights.uniform]
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_re {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    (residuePrimeCoordinateMean f lo N M a q I x).re =
      𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, (f (fun j => (z.val j).val)).re := by
  simp only [residuePrimeCoordinateMean, Fintype.expect_eq_sum_div_card,
    Complex.div_natCast_re, Complex.re_sum]
  congr 3 <;> exact Subsingleton.elim _ _

theorem residuePrimeCoordinateRealMean_bound {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℝ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ z ∈ translatedIntegerBox lo N, |f z| ≤ C) :
    |𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)| ≤ C := by
  classical
  by_cases hne : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)
  · let := hne
    rw [← FiniteProbabilityWeights.uniform_mean]
    apply FiniteProbabilityWeights.abs_mean_le_on_support
    intro z _
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro j
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z.val j).property).1)
  · let : IsEmpty (ResiduePrimeCoordinateCell lo N M a q I x) := not_nonempty_iff.mp hne
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_of_isEmpty, Nat.cast_zero,
      div_zero, abs_zero]
    exact hC

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

theorem affineComparisonTolerance_bounds {L T level : ℝ}
    (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) :
    0 < Real.exp (-T) ∧ Real.exp (-T) ≤ 1 ∧
    (Real.exp (-T))⁻¹ ≤ Real.exp T ∧ 0 < level ∧
    0 < affineStabilityTolerance T ∧ affineStabilityTolerance T ≤ Real.exp (-T) / 8 ∧
    0 < affineIncrementTolerance L T ∧ affineIncrementTolerance L T ≤ level * Real.exp (-T) / 8 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), ?_,
    (Real.exp_pos _).trans_le hlower, Real.exp_pos _, ?_, Real.exp_pos _, ?_⟩
  · simp only [Real.exp_neg, inv_inv, le_refl]
  · exact exp_neg_le_exp_neg_div_eight le_rfl
  · calc
      affineIncrementTolerance L T ≤ Real.exp (-(L + T)) / 8 := exp_neg_le_exp_neg_div_eight le_rfl
      _ ≤ level * Real.exp (-T) / 8 := by
        rw [neg_add, Real.exp_add]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlower (Real.exp_pos _).le) (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CylinderUniformMass
namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}

omit [∀ i, DecidableEq (X i)] in
theorem CylinderRemovalChain.size_le (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs) :
    ∀ d ∈ cs, d.1.card ≤ j := by
  induction hchain with
  | nil => simp
  | @cons w rem cs d hsize hmass hbounded rest ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hsize
    · exact ih c hc

theorem CylinderRemovalChain.removed_mass_le_two
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    {η : ℝ} (hη : η ≤ 1)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η j) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      cf.1.mass μ base (observedProductDensity μ p F cf.2) ≤ 2 := by
  intro cf hcf
  have hf := removedCylinderWeights_bounds F w cs (fun z => (hw z).1) (fun z => (hw z).2)
    (List.of_mem_zip hcf).2
  have hb := observedProductDensity_marginal_le μ p F hμ cf.2 (fun z => (hf z).2)
    hclose cf.1.1 (hchain.removed_size_mass cf hcf).1 (cf.1.assignment base)
  change productConditionalMean μ cf.1.1 (observedProductDensity μ p F cf.2) (cf.1.assignment base) ≤ 2
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem partial_assignment_card_le_exp {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {V : ℝ} (hV : 0 ≤ V)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) (S : Finset ι) {j : ℕ} (hS : S.card ≤ j) :
    (Fintype.card (∀ i : S, X i.val) : ℝ) ≤ Real.exp ((j : ℝ) * V) := by
  classical
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _i : S, Real.exp V := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hX i.val)
    _ = Real.exp ((S.card : ℝ) * V) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hV)

theorem ProductCylinder.bounded_card_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {P V : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) (j : ℕ) :
    ((ProductCylinder.bounded (X := X) j).card : ℝ) ≤ Real.exp ((j : ℝ) * (P + V + 1)) := by
  classical
  have he : ((ProductCylinder.bounded (X := X) j).card : ℝ) =
      ∑ S ∈ lowDegreeCoordinateSets ι j, (Fintype.card (∀ i : S, X i.val) : ℝ) := by
    simp only [ProductCylinder.bounded_card, Nat.cast_sum, Fintype.card_pi, Nat.cast_prod]
  rw [he]
  calc
    _ ≤ ∑ _S ∈ lowDegreeCoordinateSets ι j, Real.exp ((j : ℝ) * V) := by
      apply Finset.sum_le_sum
      intro S hS
      exact partial_assignment_card_le_exp hV hX S ((mem_lowDegreeCoordinateSets ι j S).mp hS)
    _ = ((lowDegreeCoordinateSets ι j).card : ℝ) * Real.exp ((j : ℝ) * V) := by simp
    _ ≤ Real.exp ((j : ℝ) * (P + 1)) * Real.exp ((j : ℝ) * V) :=
      mul_le_mul_of_nonneg_right (lowDegreeCoordinateSets_card_le_exp hP hcount j) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem CylinderRemovalChain.length_le_exp {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ P V : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hτ : 0 ≤ τ) (hw : ∀ z, 0 ≤ w z) (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) :
    (cs.length : ℝ) ≤ Real.exp ((j : ℝ) * (P + V + 1)) := by
  classical
  have hsub : cs.toFinset ⊆ ProductCylinder.bounded (X := X) j := by
    intro d hd
    exact (ProductCylinder.mem_bounded j d).mpr (hchain.size_le d (List.mem_toFinset.mp hd))
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (hchain.nodup hτ hw)] at hc
  exact (Nat.cast_le.mpr hc).trans (ProductCylinder.bounded_card_le_exp hP hV hcount hX j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedListError
namespace OAI

section

namespace Erdos3

theorem list_weighted_error_sum {α : Type*} (xs : List α) (P m e : α → ℝ) (C : ℝ)
    (h : ∀ x ∈ xs, P x ≤ C * m x + e x) :
    (xs.map P).sum ≤ C * (xs.map m).sum + (xs.map e).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CylinderShellCountBudget
namespace OAI

section

namespace Erdos3

theorem uniform_section_norm_product_le_exp {τ L T : ℝ} (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp T) :
    (3 * τ⁻¹) * (3 * Real.exp (L + T)) ≤ Real.exp (L + 2 * T + 4) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hM : 3 * τ⁻¹ ≤ Real.exp (T + 2) := by
    rw [Real.exp_add]
    exact (mul_le_mul h3 hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hN : 3 * Real.exp (L + T) ≤ Real.exp (L + T + 2) := by
    rw [Real.exp_add (L + T) 2]
    exact (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  calc
    _ ≤ Real.exp (T + 2) * Real.exp (L + T + 2) := mul_le_mul hM hN (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem retained_shell_prefactor_le_exp {m level v τ ε L T : ℝ} {i j : ℕ}
    (_hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hl0 : 0 ≤ level) (hl2 : level ≤ 2)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 ≤ ε)
    (hτinv : τ⁻¹ ≤ Real.exp T) (hij : i ≤ j) :
    m * level * (v + τ) * (6 + 2 * ε) * (2 : ℝ) ^ i *
      (3 * τ⁻¹) * (3 * Real.exp (L + T)) ≤ Real.exp (ε + L + 2 * T + j + 10) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  have hbase : m * level * (v + τ) * (6 + 2 * ε) ≤ 16 * (3 + ε) := by
    calc
      _ ≤ 2 * 2 * (1 + 1) * (6 + 2 * ε) := by gcongr
      _ = _ := by ring
  have hconstant : m * level * (v + τ) * (6 + 2 * ε) ≤ Real.exp (ε + 6) := by
    apply hbase.trans
    calc
      _ ≤ Real.exp 4 * Real.exp (ε + 2) :=
        mul_le_mul h16 (by linarith [Real.add_one_le_exp (ε + 2)]) (by linarith) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : (2 : ℝ) ^ i ≤ Real.exp j := by
    calc
      _ ≤ (Real.exp 1) ^ i := pow_le_pow_left₀ (by norm_num) htwo i
      _ = Real.exp i := by rw [← Real.exp_nat_mul]; simp
      _ ≤ _ := Real.exp_le_exp.mpr (by exact_mod_cast hij)
  have hn := uniform_section_norm_product_le_exp (L := L) hτ hτinv
  calc
    _ = (m * level * (v + τ) * (6 + 2 * ε)) * (2 : ℝ) ^ i *
        ((3 * τ⁻¹) * (3 * Real.exp (L + T))) := by ring
    _ ≤ Real.exp (ε + 6) * Real.exp j * Real.exp (L + 2 * T + 4) :=
      mul_le_mul (mul_le_mul hconstant hp (by positivity) (Real.exp_pos _).le) hn
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem list_map_sum_le_exp {α : Type*} (xs : List α) (f : α → ℝ) {U V : ℝ}
    (hlen : (xs.length : ℝ) ≤ Real.exp U) (hf : ∀ x ∈ xs, f x ≤ Real.exp V) :
    (xs.map f).sum ≤ Real.exp (U + V) := by
  have hs := list_weighted_error_sum xs f (fun _ => 1) (fun _ => 0) (Real.exp V)
    (fun x hx => by simpa using hf x hx)
  have hs' : (xs.map f).sum ≤ (xs.length : ℝ) * Real.exp V := by
    simpa [mul_comm] using hs
  exact (hs'.trans (mul_le_mul_of_nonneg_right hlen (Real.exp_pos _).le)).trans_eq (Real.exp_add U V).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem CylinderRemovalChain.shell_prefactor_le_exp {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ η P S V level v ε L T : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : η ≤ 1)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η j)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp S)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp V)
    (hl0 : 0 ≤ level) (hl2 : level ≤ 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hε : 0 ≤ ε)
    (hτinv : τ⁻¹ ≤ Real.exp T) :
    ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, Y i.val) : ℝ) *
        (cf.1.mass μ base (observedProductDensity μ p F cf.2) * level * (v + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))).sum ≤
      Real.exp ((j : ℝ) * (P + S + V + 2) + ε + L + 2 * T + 10) := by
  have hlen := hchain.length_le_exp hτ.le (fun z => (hw z).1) hP hS hcount hX
  have hlen' : ((cs.zip (removedCylinderWeights F w cs)).length : ℝ) ≤
      Real.exp ((j : ℝ) * (P + S + 1)) := by
    simpa only [List.length_zip, removedCylinderWeights_length, min_self] using hlen
  have hmass := hchain.removed_mass_le_two hμ hw hη hclose
  have hs := list_map_sum_le_exp (cs.zip (removedCylinderWeights F w cs))
    (fun cf => (Fintype.card (∀ i : cf.1.1, Y i.val) : ℝ) *
      (cf.1.mass μ base (observedProductDensity μ p F cf.2) * level * (v + τ) * (6 + 2 * ε) *
        (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))
    (V := (j : ℝ) * V + (ε + L + 2 * T + j + 10)) hlen' (by
      intro cf hcf
      obtain ⟨hsize, hpositive⟩ := hchain.removed_size_mass cf hcf
      have hm0 := (hτ.trans hpositive).le
      have hc := partial_assignment_card_le_exp hV hY cf.1.1 hsize
      have hp := retained_shell_prefactor_le_exp (L := L) hm0 (hmass cf hcf) hl0 hl2 hv0 hv1 hτ hτ1 hε hτinv hsize
      exact (mul_le_mul hc hp (by positivity) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm)
  exact hs.trans_eq (by congr 1; ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidueAccuracy
namespace OAI

section

namespace Erdos3

theorem affineComparisonAccuracy_bounds {P L T level : ℝ} (b : ℕ)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T) (hlevel : Real.exp (-L) ≤ level) :
    0 < affineComparisonAccuracy b P L T ∧ affineComparisonAccuracy b P L T < 1 ∧
    affineComparisonAccuracy b P L T ≤ Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ level * Real.exp (-T) / 8 ∧
    affineComparisonAccuracy b P L T ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)) := by
  have hp : 0 ≤ (P + 3) ^ 3 := by positivity
  have hb : 0 ≤ 2 * (b : ℝ) * (P + 2) := by positivity
  have hpos : 0 < affineComparisonAccuracyLog b P L T := by
    unfold affineComparisonAccuracyLog
    linarith
  refine ⟨Real.exp_pos _, ?_, ?_, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (by linarith)
  · exact exp_neg_le_exp_neg_div_eight (by unfold affineComparisonAccuracyLog; linarith)
  · calc
      _ ≤ Real.exp (-(L + T)) / 8 :=
        exp_neg_le_exp_neg_div_eight (by unfold affineComparisonAccuracyLog; linarith)
      _ ≤ level * Real.exp (-T) / 8 := by
        rw [neg_add, Real.exp_add]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlevel (Real.exp_pos _).le) (by norm_num)
  · exact exp_neg_le_half_exp_neg (by unfold affineComparisonAccuracyLog; linarith)

theorem affineComparisonAccuracy_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P L T : ℝ} (b : ℕ) (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    2 * affineComparisonAccuracy b P L T * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + affineComparisonAccuracy b P L T) ^ 2 ≤ Real.exp (-T) := by
  let η := affineComparisonAccuracy b P L T
  have he := affineComparisonAccuracy_bounds (level := Real.exp (-L)) b hP hL hT le_rfl
  have hη0 : 0 < η := he.1
  have hη1 : η < 1 := he.2.1
  have hc := lowDegreeCoordinateSets_card_le_exp hP hcount b
  have hc2 : ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 ≤
      Real.exp (2 * (b : ℝ) * (P + 1)) := by
    calc
      _ ≤ (Real.exp ((b : ℝ) * (P + 1))) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hp4 : (4 : ℝ) ^ b ≤ Real.exp (2 * (b : ℝ)) := by
    exact (pow_le_pow_left₀ (by norm_num) hfour b).trans_eq (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have hsq : (1 + η) ^ 2 ≤ 4 := by nlinarith
  have hsmall : η ≤ Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) / 8 := by
    apply exp_neg_le_exp_neg_div_eight
    unfold affineComparisonAccuracyLog
    have hp : 0 ≤ (P + 3) ^ 3 := by positivity
    linarith
  change 2 * η * _ ^ 2 * _ ^ b * (1 + η) ^ 2 ≤ _
  calc
    _ ≤ 2 * η * Real.exp (2 * (b : ℝ) * (P + 1)) * Real.exp (2 * (b : ℝ)) * 4 := by gcongr
    _ = 8 * η * (Real.exp (2 * (b : ℝ) * (P + 1)) * Real.exp (2 * (b : ℝ))) := by ring
    _ = 8 * η * Real.exp (2 * (b : ℝ) * (P + 2)) := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ 8 * (Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) / 8) * Real.exp (2 * (b : ℝ) * (P + 2)) := by gcongr
    _ = Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) * Real.exp (2 * (b : ℝ) * (P + 2)) := by ring
    _ = Real.exp (-T) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StableRetainedAtom
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_re_nonneg {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re) :
    0 ≤ (residuePrimeCoordinateMean g lo N M a q K base).re := by
  rw [residuePrimeCoordinateMean_re, Fintype.expect_eq_sum_div_card]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro z _
  apply hg
  apply (mem_translatedIntegerBox lo N _).mpr
  intro j
  exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z.val j).property).1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

theorem affineSampleKernel_centered_sq {p a : ℕ} (hp : p.Prime) (hq : q = p ^ a)
    (f : (I → ZMod q) → ℝ) (hf : (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f = 0) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f ^ 2) ≤
      (p : ℝ)⁻¹ ^ Fintype.card J * (FiniteProbabilityWeights.uniform (I → ZMod q)).mean (fun x => f x ^ 2) := by
  unfold affineSampleKernel
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => (residueAffineKernel (q := q) z).mean f ^ 2)]
  have hcard : Fintype.card (I → ZMod q) = p ^ (a * Fintype.card I) := by simp [hq, pow_mul]
  exact residueAffineKernel_centered_sq hp hcard f hf

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem inverse_prime_power_le_square {p ell : ℕ} {κ : ℝ}
    (hp : p.Prime) (hell : 2 ≤ ell) (_hκ : 0 ≤ κ) (hlarge : (p : ℝ)⁻¹ ≤ κ) :
    (p : ℝ)⁻¹ ^ ell ≤ κ ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hi1 : (p : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp1
  exact (pow_le_pow_of_le_one (inv_nonneg.mpr (Nat.cast_nonneg p)) hi1 hell).trans
    (pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg p)) hlarge 2)

theorem affineSampleKernel_centered_sq_of_inverse_le {J I : Type*} [Fintype J] [Fintype I]
    {q p a : ℕ} [NeZero q] {κ : ℝ} (hp : p.Prime) (hq : q = p ^ a)
    (hJ : 2 ≤ Fintype.card J) (hκ : 0 ≤ κ) (hlarge : (p : ℝ)⁻¹ ≤ κ)
    (f : (I → ZMod q) → ℝ) (hf : (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f = 0) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f ^ 2) ≤
      κ ^ 2 * (FiniteProbabilityWeights.uniform (I → ZMod q)).mean (fun y => f y ^ 2) := by
  exact (affineSampleKernel_centered_sq hp hq f hf).trans
    (mul_le_mul_of_nonneg_right (inverse_prime_power_le_square hp hJ hκ hlarge)
      ((FiniteProbabilityWeights.uniform (I → ZMod q)).mean_nonneg (fun _ => sq_nonneg _)))

theorem residue_function_alphabet_card_le_exp {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    {B : ℝ} (hq : (q : ℝ) ≤ Real.exp B) :
    (Fintype.card (I → ZMod q) : ℝ) ≤ Real.exp ((Fintype.card I : ℝ) * B) := by
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg q) hq _).trans_eq (Real.exp_nat_mul _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBaselineBounds
namespace OAI

section

namespace Erdos3

theorem residuePrimeCoordinateMean_re_le_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1) :
    (residuePrimeCoordinateMean g lo N M a q K base).re ≤ 1 := by
  have ha : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hg z hz).1]
    exact (hg z hz).2
  have h := residuePrimeCoordinateRealMean_bound (fun z => (g z).re) lo N M a q K base 1 zero_le_one ha
  rw [← residuePrimeCoordinateMean_re] at h
  exact (le_abs_self _).trans h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.StableCountedKernel
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem stable_residue_counted_kernel_total {Ω ι σ : Type*}
    [Fintype Ω]
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {j r b moment : ℕ} {level inc δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    {X : {i // i ∉ K} → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (sourceBase : ∀ i, X i)
    (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    {regK κ ε ξ shell sourceLog siteLog : ℝ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ sourceBase p F regK τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hregK : 1 ≤ regK)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1) (hmass : p.mean rem ≤ τ)
    (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ / 8) (hinc : inc ≤ level * τ / 8)
    (hη0 : 0 ≤ η) (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T)
    (hlog : L + T + 2 ≤ P) (hrP : ((j + r : ℕ) : ℝ) ≤ P)
    (hmoment : 2 ≤ moment) (heven : Even moment) (hPq : P ≤ (moment : ℝ)) (hqP : (moment : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)
    (hsourceclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hresGram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (kernel : ∀ i : {i // i ∉ K}, X i → FiniteProbabilityWeights (σ → ZMod (q i.val)))
    (C : {i // i ∉ K} → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i : {i // i ∉ K}, ∀ f : (σ → ZMod (q i.val)) → ℝ,
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean f = 0 →
      (μ i).mean (fun x => (kernel i x).mean f ^ 2) ≤ C i *
        (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean (fun y => f y ^ 2))
    (hK : ∀ i : {i // i ∉ K}, ∀ f : (σ → ZMod (q i.val)) → ℝ, (μ i).mean (fun x => (kernel i x).mean f) =
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean f)
    (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hslack : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i, C i ≤ κ ^ 2)
    (hlow : κ * (8 * (1 + regK) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16)
    (hrtail : CyclicCrootSisask.spectralIterations ξ (L + 2 * T + 4) ≤ r) (hrb : j + r ≤ b)
    (hshell : 0 < shell) (hb : j + CyclicCrootSisask.spectralIterations shell ((j : ℝ) * (P + sourceLog + siteLog + 2) + ε + L + 2 * T + 10) ≤ b)
    (hlevel2 : level ≤ 2) (hτ1 : τ ≤ 1)
    (hsourceLog : 0 ≤ sourceLog) (hsiteLog : 0 ≤ siteLog)
    (hsourceAlphabet : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp sourceLog)
    (hsiteAlphabet : ∀ i : {i // i ∉ K}, (Fintype.card (σ → ZMod (q i.val)) : ℝ) ≤ Real.exp siteLog) :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (kernel i) (hK i)
    productTruncatedPairing c (lowDegreeCoordinateSets {i // i ∉ K} b) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (3 + (1 + ε) * level * 3) := by
  have hP : 0 ≤ P := (Nat.cast_nonneg (j + r)).trans hrP
  have houtside : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hv0 := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  have hv1 := residuePrimeCoordinateMean_re_le_one g lo N M a q K base hg
  have hbudget := hchain.shell_prefactor_le_exp (Y := fun i : {i // i ∉ K} => σ → ZMod (q i.val)) (L := L)
    hμ hw hτ hτ1 hη.le (ProductMarginalsClose.mono μ hsourceclose (by omega))
    hP hsourceLog hsiteLog houtside hsourceAlphabet hsiteAlphabet hlevel.le hlevel2 hv0 hv1 hε hτinv
  exact stable_residue_kernel_total_s2 μ p F sourceBase siteBase hchain hμ hregK hw hrem hmass
    hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc hη0 hη hητ hηlevel hL hT hlower hτinv
    hlog hrP hmoment heven hPq hqP hcount hηsmall herror hclose hgram hsourceclose hresGram
    kernel C hC hbound hK hε hξ hξ1 hslack hκ0 hκhalf hcap hlow hrtail hrb hshell hb hbudget

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.InitialMaskedAffineComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*}

variable [Fintype J]

variable [Fintype Ω]

variable [Fintype ι]

variable [LinearOrder ι]

variable [Fintype σ]

variable {h g : (σ → ℤ) → ℂ}

variable {lo a : σ → ℤ}

variable {N : σ → ℕ}

variable {M : ℕ}

variable {q : ι → ℕ}

variable [∀ i, NeZero (q i)]

variable {j r b moment : ℕ}

variable {level inc δ η τ L T P : ℝ}

variable {K : Finset ι}

variable {base : ∀ i, σ → ZMod (q i)}

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {regK κ ε ξ shell modLog : ℝ}

variable {w rem : Ω → ℝ}

variable {cs : List (ProductCylinder (fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val)))}

variable (hchain : CylinderRemovalChain (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) sourceBase p F regK τ j r w rem cs)

variable (hregK : 1 ≤ regK)

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1)

variable (hmass : p.mean rem ≤ τ)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hlevel : 0 < level)

variable (hτ : 0 < τ)

variable (hδ : δ ≤ τ / 8)

variable (hinc : inc ≤ level * τ / 8)

variable (hη0 : 0 ≤ η)

variable (hη : η < 1)

variable (hητ : η ≤ τ / 8)

variable (hηlevel : η ≤ level * τ / 8)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hτinv : τ⁻¹ ≤ Real.exp T)

variable (hlog : L + T + 2 ≤ P)

variable (hrP : ((j + r : ℕ) : ℝ) ≤ P)

variable (hmoment : 2 ≤ moment)

variable (heven : Even moment)

variable (hPq : P ≤ (moment : ℝ))

variable (hqP : (moment : ℝ) ≤ P + 2)

variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)

variable (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))

variable (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)

variable (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))

variable (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))

variable (hresGram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hlarge : ∀ i ∉ K, (prime i : ℝ)⁻¹ ≤ κ)

variable (hε : 0 ≤ ε)

variable (hξ : 0 < ξ)

variable (hξ1 : ξ ≤ 1)

variable (hslack : ξ * (2 + ε) ≤ ε)

variable (hκ0 : 0 ≤ κ)

variable (hκhalf : κ ≤ 1 / 2)

variable (hlow : κ * (8 * (1 + regK) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16)

variable (hrtail : CyclicCrootSisask.spectralIterations ξ (L + 2 * T + 4) ≤ r)

variable (hrb : j + r ≤ b)

variable (hshell : 0 < shell)

variable (hb : j + CyclicCrootSisask.spectralIterations shell ((j : ℝ) * (P + ((Fintype.card (Option J × σ) : ℝ) * modLog) + ((Fintype.card σ : ℝ) * modLog) + 2) + ε + L + 2 * T + 10) ≤ b)

variable (hlevel2 : level ≤ 2)

variable (hτ1 : τ ≤ 1)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

include p F sourceBase siteBase hchain hregK hw hrem hmass hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc hη0 hη hητ hηlevel hL hT hlower hτinv hlog hrP hmoment heven hPq hqP hcount hηsmall herror hclose hgram hsourceclose hresGram prime power hprime hpower hJ hlarge hε hξ hξ1 hslack hκ0 hκhalf hlow hrtail hrb hshell hb hlevel2 hτ1 hmodLog hmoduli

theorem stable_residue_affine_total :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} b) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (3 + (1 + ε) * level * 3) := by
  let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
  have hμ : ∀ i x, 0 < (μ i).weight x := primeCoordinateReference_weight_pos _
  have hsourceAlphabet : ∀ i : {i // i ∉ K},
      (Fintype.card (Option J × σ → ZMod (q i.val)) : ℝ) ≤
        Real.exp ((Fintype.card (Option J × σ) : ℝ) * modLog) :=
    fun i => by
      simpa only [Fintype.card_fun, ZMod.card, Nat.cast_pow] using
        (residue_function_alphabet_card_le_exp (I := Option J × σ) (q := q i.val) (hmoduli i.val i.property))
  have hsiteAlphabet : ∀ i : {i // i ∉ K}, (Fintype.card (σ → ZMod (q i.val)) : ℝ) ≤
      Real.exp ((Fintype.card σ : ℝ) * modLog) :=
    fun i => by
      simpa only [Fintype.card_fun, ZMod.card, Nat.cast_pow] using
        (residue_function_alphabet_card_le_exp (I := σ) (q := q i.val) (hmoduli i.val i.property))
  have result := stable_residue_counted_kernel_total (Ω := Ω) (ι := ι) (σ := σ)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (j := j) (r := r) (b := b) (moment := moment) (level := level) (inc := inc)
    (δ := δ) (η := η) (τ := τ) (L := L) (T := T) (P := P) (K := K) (base := base)
    (X := fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val))
    (regK := regK) (κ := κ) (ε := ε) (ξ := ξ) (shell := shell)
    (sourceLog := (Fintype.card (Option J × σ) : ℝ) * modLog)
    (siteLog := (Fintype.card σ : ℝ) * modLog) (w := w) (rem := rem) (cs := cs)
    μ p F sourceBase siteBase hchain hμ hregK hw hrem hmass
    hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc hη0 hη hητ hηlevel hL hT hlower hτinv
    hlog hrP hmoment heven hPq hqP hcount hηsmall herror hclose hgram hsourceclose hresGram
    (fun i => affineSampleKernel (J := J) (I := σ) (q := q i.val)) (fun _ => κ ^ 2)
    (fun _ => sq_nonneg _) (fun i f hf => affineSampleKernel_centered_sq_of_inverse_le
      (hprime i.val) (hpower i.val) hJ hκ0 (hlarge i.val i.property) f hf)
    (fun i f => affineSampleKernel_preserves_mean (J := J) (I := σ) (q := q i.val) f)
    hε hξ hξ1 hslack hκ0 hκhalf (fun _ => le_rfl) hlow hrtail hrb hshell hb hlevel2 hτ1
    (by positivity) (by positivity) hsourceAlphabet hsiteAlphabet
  exact result

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.InitialMaskedAffineComparisonAtDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*} [Fintype J] [Fintype Ω] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {w rem : Ω → ℝ}

variable {cs : List (ProductCylinder (fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val)))}

variable (hchain : CylinderRemovalChain (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) sourceBase p F (2 : ℝ) (Real.exp (-T)) (affineRemovalDepth T) (affineComparisonTail ε L T) w rem cs)

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1)

variable (hmass : p.mean rem ≤ (Real.exp (-T)))

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T))))

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include hb p F sourceBase siteBase hchain hw hrem hmass hstable hupper hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

theorem chosen_stable_residue_affine_total_at_degree_s2_oai :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  have hscale := affineComparisonScale_bounds (ε := ε) hL hT hC
  have hlargeStep := affineMandatoryPrimes_outside_inverse (ι := ι) (ξ := (ε / (2 + ε))) (P := (affineComparisonScale ε L T C))
    prime hscale.1 K
  have hlarge := hlargeStep hmandatory
  have hmom := affineComparisonMoment_bounds hscale.1
  have hcnt : (Fintype.card ι : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) := affineComparisonScale_count (ι := ι) (ε := ε) hL hT hC hcount
  have hcnt' : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcnt
  have htol := affineComparisonTolerance_bounds hT hlower
  have heta := affineComparisonAccuracy_bounds (b) hscale.1 hL hT hlower
  have hgram := affineComparisonAccuracy_gram (ι := {i // i ∉ K}) (b) hscale.1 hL hT hcnt'
  have hxi := retained_core_allowance_spec hε
  have hκ := affineComparisonContraction_bounds hxi.1 hscale.1
  have hdeg := affineFinalDegree_bounds (affineRemovalDepth T) (affineComparisonTail ε L T) shell
    (((affineRemovalDepth T) : ℝ) * ((affineComparisonScale ε L T C) + (Fintype.card (Option J × σ) : ℝ) * modLog +
      (Fintype.card σ : ℝ) * modLog + 2) + ε + L + 2 * T + 10)
  have hs0 := retained_residue_marginals_of_lengths_s2 (ι := ι) (σ := σ)
    lo N M a q hM hpair K base hcop u
  have hs1 := hs0 (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T))) modLog dimLog
    (affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T) (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)
  have hs2 := hs1 hmodLog heta.2.1.le
  have he : Real.exp (-affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T) ≤ (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T) := by
    unfold affineComparisonAccuracy
    exact le_rfl
  have hs3 := hs2 he
  have hs4 := hs3 hmoduli hdim
  have hsite := hs4 hlength
  have hrank : (affineRemovalDepth T) + (affineComparisonTail ε L T) ≤ max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) := by
    have hmul : (affineRemovalDepth T) + (affineComparisonTail ε L T) ≤ ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1) := by
      calc
        (affineRemovalDepth T) + (affineComparisonTail ε L T) = ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * 1 := (Nat.mul_one _).symm
        _ ≤ ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1) := Nat.mul_le_mul_left _ (by omega)
    exact hmul.trans (le_max_left _ _)
  have hc0 := stable_residue_affine_total (Ω := Ω) (ι := ι) (σ := σ) (J := J)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (j := (affineRemovalDepth T)) (r := (affineComparisonTail ε L T)) (b := (b)) (moment := (affineComparisonMoment (affineComparisonScale ε L T C))) (level := level) (inc := (affineIncrementTolerance L T))
    (δ := (affineStabilityTolerance T)) (η := (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)) (τ := (Real.exp (-T))) (L := L) (T := T) (P := (affineComparisonScale ε L T C)) (K := K) (base := base)
    (regK := 2) (κ := (affineComparisonContraction (ε / (2 + ε)) (affineComparisonScale ε L T C))) (ε := ε) (ξ := (ε / (2 + ε))) (shell := shell) (modLog := modLog)
    (w := w) (rem := rem) (cs := cs)
    p F sourceBase siteBase hchain (by norm_num) hw hrem hmass hstable hupper hM hpair hcop u hg hh
  have hc1 := hc0 htol.2.2.2.1 htol.1 htol.2.2.2.2.2.1 htol.2.2.2.2.2.2.2
    heta.1.le heta.2.1 heta.2.2.1 heta.2.2.2.1 hL hT hlower htol.2.2.1
  have hc2 := hc1 hscale.2.1 hscale.2.2.1 hmom.1 hmom.2.1 hmom.2.2.1 hmom.2.2.2 hcnt heta.2.2.2.2
  have hc3 := hc2 (fun S hS => hsite.2 S (hS.trans hrank)) hsite.1 (hgram.trans htol.2.1) hsourceclose hgram
  have hc4a := hc3 prime power
  have hc4b := hc4a hprime hpower hJ
  have hc4 := hc4b hlarge
  have hc5 := hc4 hε.le hxi.1 hxi.2.1 hxi.2.2 hκ.1.le hκ.2.1 hκ.2.2
  have htail : CyclicCrootSisask.spectralIterations (ε / (2 + ε)) (L + 2 * T + 4) ≤ (affineComparisonTail ε L T) := by
    unfold affineComparisonTail
    exact le_rfl
  have hc6 := hc5 htail
    (hdeg.1.trans hb) hshell (hdeg.2.trans hb) hlevel2 htol.2.1 hmodLog hmoduli
  exact hc6

end

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.chosen_stable_residue_affine_total_at_degree_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.chosen_stable_residue_affine_total_at_degree_s2_oai.{u_1, u_2, u_3, u_4}
