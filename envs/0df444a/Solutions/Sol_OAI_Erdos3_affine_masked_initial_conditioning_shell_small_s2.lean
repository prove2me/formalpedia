-- Prove2me | solution 1 for OAI.Erdos3.affine_masked_initial_conditioning_shell_small_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:12:49.80843+00:00
-- url     : https://prove2.me/submissions/15f10162-a160-42d8-98a1-ca2115182958

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_residue_initial_conditioning_shell_of_lengths_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialConditioningBudget
namespace OAI

section

namespace Erdos3

theorem initial_conditioning_prefactor_le_exp {sourceRatio siteRatio V W : ℝ} (n : ℕ)
    (hs0 : 0 ≤ sourceRatio) (ht0 : 0 ≤ siteRatio)
    (hs : sourceRatio ≤ Real.exp ((n : ℝ) * V))
    (ht : siteRatio ≤ Real.exp ((n : ℝ) * W)) :
    9 * sourceRatio * siteRatio * (2 : ℝ) ^ n ≤ Real.exp ((n : ℝ) * (V + W + 1) + 4) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hn : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) htwo n
      _ = _ := by rw [← Real.exp_nat_mul]; simp
  have h9 : (9 : ℝ) ≤ Real.exp 4 := by
    calc
      9 ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp 4 * Real.exp ((n : ℝ) * V) * Real.exp ((n : ℝ) * W) * Real.exp (n : ℝ) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem initial_conditioning_error_small {sourceRatio siteRatio V W κ shell : ℝ} (n B : ℕ)
    (hs0 : 0 ≤ sourceRatio) (ht0 : 0 ≤ siteRatio)
    (hs : sourceRatio ≤ Real.exp ((n : ℝ) * V))
    (ht : siteRatio ≤ Real.exp ((n : ℝ) * W))
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hshell : 0 < shell)
    (hB : n + CyclicCrootSisask.spectralIterations shell ((n : ℝ) * (V + W + 1) + 4) ≤ B) :
    (2 : ℝ) ^ n * (κ ^ (B - n) * (sourceRatio * 3) * (siteRatio * 3)) ≤ shell / 16 := by
  have h := geometric_tail_after_cutoff hshell hκ0 hκhalf
    (by positivity : 0 ≤ 9 * sourceRatio * siteRatio * (2 : ℝ) ^ n)
    (initial_conditioning_prefactor_le_exp n hs0 ht0 hs ht)
    (show CyclicCrootSisask.spectralIterations shell ((n : ℝ) * (V + W + 1) + 4) ≤ B - n by omega)
  calc
    _ = κ ^ (B - n) * (9 * sourceRatio * siteRatio * (2 : ℝ) ^ n) := by ring
    _ ≤ shell / 16 := h

end Erdos3

end

end OAI
end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductReferenceFiber
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productFiberMass_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x = ∏ i ∈ S, (μ i).weight (x i) := by
  classical
  have hind : ∀ y : ∀ i, X i, productFiberIndicator S x y =
      ∏ i, (if i ∈ S then if y i = x i then (1 : ℝ) else 0 else 1) := by
    intro y
    unfold productFiberIndicator
    split_ifs with h
    · symm
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ S
      · simp only [hi, h i hi, ite_true]
      · simp only [hi, ite_false]
    · push Not at h
      obtain ⟨i, hi, heq⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, heq, ite_true, ite_false]
  simp only [productFiberMass, hind, FiniteProbabilityWeights.pi, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (y : X i) => (μ i).weight y *
    (if i ∈ S then if y = x i then (1 : ℝ) else 0 else 1))]
  have hsum : ∀ i, (∑ y : X i, (μ i).weight y * (if i ∈ S then if y = x i then 1 else 0 else 1)) =
      if i ∈ S then (μ i).weight (x i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simpa only [hi, ite_false, mul_one] using (μ i).total
  simp only [hsum]
  rw [Finset.prod_ite]
  simp

theorem productFiberMass_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (X i))).weight S x =
      ∏ i ∈ S, (Fintype.card (X i) : ℝ)⁻¹ := by
  rw [productFiberMass_pi]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedPrimePowers_pairwise_coprime {ι : Type*}
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) :
    Pairwise (fun i j => (prime i ^ power i).Coprime (prime j ^ power j)) := by
  intro i j hij
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
  intro heq
  exact hij (hinj heq)

end Erdos3

end

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

section

namespace Erdos3

open scoped Classical

theorem affineInitialPrimeMask_contains {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM : ℕ) :
    affineMandatoryPrimes prime ξ P ⊆ affineInitialPrimeMask prime ξ P sourceM siteM ∧
    periodPrimeCoordinates prime sourceM ⊆ affineInitialPrimeMask prime ξ P sourceM siteM ∧
    periodPrimeCoordinates prime siteM ⊆ affineInitialPrimeMask prime ξ P sourceM siteM := by
  exact ⟨Finset.subset_union_left.trans Finset.subset_union_left,
    Finset.subset_union_right.trans Finset.subset_union_left, Finset.subset_union_right⟩

theorem affineInitialPrimeMask_outside_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    {ξ P : ℝ} {sourceM siteM : ℕ} (K : Finset ι)
    (hK : affineInitialPrimeMask prime ξ P sourceM siteM ⊆ K)
    (i : ι) (hi : i ∉ K) :
    sourceM.Coprime (prime i ^ power i) ∧ siteM.Coprime (prime i ^ power i) := by
  have hcontains := affineInitialPrimeMask_contains prime ξ P sourceM siteM
  have hcop (M : ℕ) (hM : periodPrimeCoordinates prime M ⊆ K) : M.Coprime (prime i ^ power i) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (hprime i).coprime_iff_not_dvd.mpr
    intro hd
    exact hi (hM ((mem_periodPrimeCoordinates prime M i).mpr hd))
  exact ⟨hcop sourceM (hcontains.2.1.trans hK), hcop siteM (hcontains.2.2.trans hK)⟩

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem affineSamplerPrimeMask_contains {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM D : ℕ) :
    affineInitialPrimeMask prime ξ P sourceM siteM ⊆
      affineSamplerPrimeMask prime ξ P sourceM siteM D ∧
    periodPrimeCoordinates prime D ⊆ affineSamplerPrimeMask prime ξ P sourceM siteM D :=
  ⟨Finset.subset_union_left, Finset.subset_union_right⟩

theorem affineSamplerPrimeMask_outside {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    {ξ P : ℝ} {sourceM siteM D : ℕ} (hP : 0 ≤ P) (K : Finset ι)
    (hK : affineSamplerPrimeMask prime ξ P sourceM siteM D ⊆ K)
    (i : ι) (hi : i ∉ K) :
    sourceM.Coprime (prime i ^ power i) ∧ siteM.Coprime (prime i ^ power i) ∧
    D.Coprime (prime i ^ power i) ∧ (prime i : ℝ)⁻¹ ≤ affineComparisonContraction ξ P := by
  have hcontains := affineSamplerPrimeMask_contains prime ξ P sourceM siteM D
  have hbase := affineInitialPrimeMask_outside_coprime prime power hprime K (hcontains.1.trans hK) i hi
  have hD : D.Coprime (prime i ^ power i) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (hprime i).coprime_iff_not_dvd.mpr
    intro hd
    exact hi (hK (hcontains.2 ((mem_periodPrimeCoordinates prime D i).mpr hd)))
  have hmandatory := (affineInitialPrimeMask_contains prime ξ P sourceM siteM).1.trans (hcontains.1.trans hK)
  exact ⟨hbase.1, hbase.2, hD, affineMandatoryPrimes_outside_inverse prime hP K hmandatory i hi⟩

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateReference_fiber {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x =
      (((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ)⁻¹ := by
  change productFiberMass (FiniteProbabilityWeights.pi
    (fun i => FiniteProbabilityWeights.uniform (σ → ZMod (q i)))).weight I x = _
  rw [productFiberMass_uniform]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_prod,
    Finset.prod_inv_distrib, Finset.prod_pow]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMassRatio_eq_count {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMassRatio lo N M a q I x =
      ((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ *
        Fintype.card (ResiduePrimeCoordinateCell lo N M a q I x) /
        Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) := by
  rw [residuePrimeCoordinateMassRatio, primeCoordinateReference_fiber, div_inv_eq_mul]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateProduct_le_exp {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (I : Finset ι) (p : ℝ) (hq : ∀ i, (q i : ℝ) ≤ Real.exp p) :
    ((∏ i ∈ I, q i : ℕ) : ℝ) ≤ Real.exp (p * I.card) := by
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ I, (q i : ℝ)) ≤ ∏ _i ∈ I, Real.exp p :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hq i)
    _ = Real.exp ((I.card : ℝ) * p) := by rw [Finset.prod_const, Real.exp_nat_mul]
    _ = Real.exp (p * I.card) := by rw [mul_comm]

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] {q : ℕ} [NeZero q]

theorem affinePeriodParameterLaw_mean (D : ℕ) (a : J → ℤ)
    (f : (J → ZMod q) → ℝ) :
    (affinePeriodParameterLaw D a).mean f =
      (FiniteProbabilityWeights.uniform (J → ZMod q)).mean
        (fun s => f (fun j => (a j : ZMod q) + (D : ZMod q) * s j)) :=
  FiniteProbabilityWeights.fiberLaw_mean _ _ _

theorem affinePeriodParameterLaw_uniform (D : ℕ) (a : J → ℤ) (hD : D.Coprime q) :
    affinePeriodParameterLaw (q := q) D a =
      FiniteProbabilityWeights.uniform (J → ZMod q) := by
  let e : (J → ZMod q) ≃ (J → ZMod q) :=
    Equiv.piCongrRight (fun j => (ZMod.unitOfCoprime D hD).mulLeft.trans
      (Equiv.addLeft (a j : ZMod q)))
  have hm (f : (J → ZMod q) → ℝ) :
      (affinePeriodParameterLaw D a).mean f =
        (FiniteProbabilityWeights.uniform (J → ZMod q)).mean f := by
    rw [affinePeriodParameterLaw_mean]
    exact FiniteProbabilityWeights.uniform_mean_equiv e f
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  have h := hm (fun y => if y = x then (1 : ℝ) else 0)
  simpa only [FiniteProbabilityWeights.mean, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

theorem affineSampleParameterKernel_sq (i : ι)
    (π : FiniteProbabilityWeights (J → ZMod (q i))) (f : (σ → ZMod (q i)) → ℝ) :
    (primeCoordinateReference (σ := Option J × σ) q i).mean
      (fun z => (affineSampleParameterKernel π z).mean f ^ 2) ≤
      (primeCoordinateReference (σ := σ) q i).mean (fun y => f y ^ 2) := by
  calc
    _ ≤ (primeCoordinateReference (σ := Option J × σ) q i).mean
        (fun z => (affineSampleParameterKernel π z).mean (fun y => f y ^ 2)) :=
      FiniteProbabilityWeights.mean_mono _ (fun z => (affineSampleParameterKernel π z).mean_square_le f)
    _ = _ := affineSampleParameterKernel_preserves_mean π (fun y => f y ^ 2)

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem affineParameterProductCoupling_outside
    (π : ∀ i, FiniteProbabilityWeights (J → ZMod (q i))) (K : Finset ι)
    (hπ : ∀ i ∉ K, π i = FiniteProbabilityWeights.uniform (J → ZMod (q i))) :
    (fun i : {i // i ∉ K} => affineParameterProductCoupling (σ := σ) q π i.val) =
      affineSampleProductCoupling (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val) := by
  funext i
  change affineSampleParameterCoupling (π i.val) = affineSampleCoupling
  rw [hπ i.val i.property]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

theorem affinePeriodProductCoupling_outside (D : ℕ) (a : J → ℤ) (K : Finset ι)
    (hD : ∀ i ∉ K, D.Coprime (q i)) :
    (fun i : {i // i ∉ K} => affinePeriodProductCoupling (σ := σ) q D a i.val) =
      affineSampleProductCoupling (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val) :=
  affineParameterProductCoupling_outside q _ K
    (fun i hi => affinePeriodParameterLaw_uniform D a (hD i hi))

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem affinePeriodParameterKernel_centered_sq
    (D : ℕ) (a : J → ℤ) (K : Finset ι) (prime power : ι → ℕ)
    (hprime : ∀ i, (prime i).Prime) (hpower : ∀ i, q i = prime i ^ power i)
    (hD : ∀ i ∉ K, D.Coprime (q i))
    {κ : ℝ} (hκ : 0 ≤ κ) (hJ : 2 ≤ Fintype.card J)
    (hlarge : ∀ i ∉ K, (prime i : ℝ)⁻¹ ≤ κ)
    (i : ι) (f : (σ → ZMod (q i)) → ℝ)
    (hf : (primeCoordinateReference (σ := σ) q i).mean f = 0) :
    (primeCoordinateReference (σ := Option J × σ) q i).mean
      (fun z => (affineSampleParameterKernel (affinePeriodParameterLaw D a) z).mean f ^ 2) ≤
      (if i ∈ K then 1 else κ ^ 2) *
        (primeCoordinateReference (σ := σ) q i).mean (fun y => f y ^ 2) := by
  by_cases hi : i ∈ K
  · rw [if_pos hi, one_mul]
    exact affineSampleParameterKernel_sq q i _ f
  · rw [if_neg hi, affinePeriodParameterLaw_uniform D a (hD i hi)]
    exact affineSampleKernel_centered_sq_of_inverse_le (hprime i) (hpower i) hJ hκ (hlarge i hi) f hf

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMaskedInitialShell
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)

include hpair u

omit hne hpair in
theorem residuePrimeCoordinateMassRatio_pos : 0 < residuePrimeCoordinateMassRatio lo N M a q K base := by
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base) := ⟨u⟩
  let : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) := ⟨u.val⟩
  have hp : 0 < ∏ i ∈ K, q i := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))
  rw [residuePrimeCoordinateMassRatio_eq_count]
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePrimeCoordinateMassRatio_le_prime_product {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) :
    residuePrimeCoordinateMassRatio lo N M a q K base ≤ ((∏ i ∈ K, q i : ℕ) : ℝ) ^ Fintype.card σ := by
  let : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) := ⟨u.val⟩
  have hB : (0 : ℝ) < Fintype.card (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) := by
    exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (ResiduePrimeCoordinateCell lo N M a q K base) : ℝ) ≤
      Fintype.card (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) :=
    Nat.cast_le.mpr (Fintype.card_subtype_le _)
  have hratio : (Fintype.card (ResiduePrimeCoordinateCell lo N M a q K base) : ℝ) /
      Fintype.card (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a) ≤ 1 := by
    apply (div_le_iff₀ hB).mpr
    simpa only [one_mul] using hcard
  rw [residuePrimeCoordinateMassRatio_eq_count, mul_div_assoc]
  exact mul_le_of_le_one_right (by positivity) hratio

theorem residuePrimeCoordinateMassRatio_le_exp {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (modLog : ℝ)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog) :
    residuePrimeCoordinateMassRatio lo N M a q K base ≤
      Real.exp ((K.card : ℝ) * Fintype.card σ * modLog) := by
  have hprod := primeCoordinateProduct_le_exp q K modLog hmoduli
  calc
    _ ≤ ((∏ i ∈ K, q i : ℕ) : ℝ) ^ Fintype.card σ :=
      residuePrimeCoordinateMassRatio_le_prime_product lo N M a q K base u
    _ ≤ (Real.exp (modLog * K.card)) ^ Fintype.card σ :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hprod _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_initial_conditioning_shell_small {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (kernel : ∀ i, (σ → ZMod (q i)) → FiniteProbabilityWeights (τ → ZMod (q i)))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : (τ → ZMod (q i)) → ℝ), (primeCoordinateReference (σ := τ) q i).mean f = 0 →
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f ^ 2) ≤
        C i * (primeCoordinateReference (σ := τ) q i).mean (fun y => f y ^ 2))
    (hmean : ∀ i (f : (τ → ZMod (q i)) → ℝ),
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f) =
        (primeCoordinateReference (σ := τ) q i).mean f)
    (w : (σ → ℤ) → ℝ) (f : (τ → ℤ) → ℝ) (B : ℕ)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i ∉ K, C i ≤ κ ^ 2)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hcopX : ∀ i ∉ K, MX.Coprime (q i)) (hcopY : ∀ i ∉ K, MY.Coprime (q i))
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card σ : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card τ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ))
    (shell : ℝ) (hshell : 0 < shell)
    (hB : K.card + CyclicCrootSisask.spectralIterations shell
      ((K.card : ℝ) * ((Fintype.card σ : ℝ) * modLog + (Fintype.card τ : ℝ) * modLog + 1) + 4) ≤ B) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (primeCoordinateReference (σ := σ) q i)
      (primeCoordinateReference (σ := τ) q i) (kernel i) (hmean i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 := by
  have hsmallX : residuePrimeCoordinateMassRatio loX NX MX aX q K baseX ≤
      Real.exp ((K.card : ℝ) * ((Fintype.card σ : ℝ) * modLog)) := by
    simpa only [mul_assoc] using residuePrimeCoordinateMassRatio_le_exp loX NX MX aX q K baseX uX modLog hmoduli
  have hsmallY : residuePrimeCoordinateMassRatio loY NY MY aY q K baseY ≤
      Real.exp ((K.card : ℝ) * ((Fintype.card τ : ℝ) * modLog)) := by
    simpa only [mul_assoc] using residuePrimeCoordinateMassRatio_le_exp loY NY MY aY q K baseY uY modLog hmoduli
  have hbudget := initial_conditioning_error_small K.card B
    (residuePrimeCoordinateMassRatio_pos loX NX MX aX q K baseX uX).le
    (residuePrimeCoordinateMassRatio_pos loY NY MY aY q K baseY uY).le
    hsmallX hsmallY hκ0 hκhalf hshell hB
  have hresult := residue_initial_conditioning_shell_of_lengths_s2
    loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY kernel C hC hbound hmean
    w f B (by omega) hκ0 (by linarith) hcap hMX hMY hcopX hcopY hw hf P modLog dimX dimY hP hmodLog
    hcount (fun i _ => hmoduli i) hdimX hdimY hlengthX hlengthY
  exact hresult.trans hbudget

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_period_initial_conditioning_shell_small {ι J σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
    (loX : (Option J × σ) → ℤ) (NX : (Option J × σ) → ℕ) (MX : ℕ) (aX : (Option J × σ) → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : σ → ℤ) (NY : σ → ℕ) (MY : ℕ) (aY : σ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, (Option J × σ) → ZMod (q i)) (baseY : ∀ i, σ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (D : ℕ) (a : J → ℤ) (hDcop : ∀ i ∉ K, D.Coprime (q i))
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hpower : ∀ i, q i = prime i ^ power i) (hJ : 2 ≤ Fintype.card J)
    (w : ((Option J × σ) → ℤ) → ℝ) (f : (σ → ℤ) → ℝ) (B : ℕ)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hlarge : ∀ i ∉ K, (prime i : ℝ)⁻¹ ≤ κ)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hcopX : ∀ i ∉ K, MX.Coprime (q i)) (hcopY : ∀ i ∉ K, MY.Coprime (q i))
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card σ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ))
    (shell : ℝ) (hshell : 0 < shell)
    (hB : K.card + CyclicCrootSisask.spectralIterations shell
      ((K.card : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B) :
    let c := affinePeriodProductCoupling (σ := σ) q D a
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 := by
  let kernel := fun i => affineSampleParameterKernel (I := σ) (affinePeriodParameterLaw (q := q i) D a)
  let C := fun i => if i ∈ K then (1 : ℝ) else κ ^ 2
  have hC (i : ι) : 0 ≤ C i := by
    dsimp only [C]
    split_ifs <;> positivity
  have hbound := affinePeriodParameterKernel_centered_sq (σ := σ) q D a K prime power
    hprime hpower hDcop hκ0 hJ hlarge
  have hmean := fun i => affineSampleParameterKernel_preserves_mean (I := σ)
    (affinePeriodParameterLaw (q := q i) D a)
  have hcap (i : ι) (hi : i ∉ K) : C i ≤ κ ^ 2 := by simp only [C, if_neg hi, le_refl]
  have hresult := residue_initial_conditioning_shell_small
    loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY
    kernel C hC hbound hmean w f B hκ0 hκhalf hcap hMX hMY hcopX hcopY hw hf
    P modLog dimX dimY hP hmodLog hcount hmoduli hdimX hdimY hlengthX hlengthY shell hshell hB
  change
    |productAtomTruncatedPairing (affinePeriodProductCoupling (σ := σ) q D a) (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass (affinePeriodProductCoupling (σ := σ) q D a) K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          productTruncatedPairing (fun i : {i // i ∉ K} => affinePeriodProductCoupling (σ := σ) q D a i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 at hresult
  rw [affinePeriodProductCoupling_outside q D a K hDcop] at hresult
  exact hresult

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_masked_initial_conditioning_shell_small_s2_oai {ι J σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
    (loX : (Option J × σ) → ℤ) (NX : (Option J × σ) → ℕ) (MX : ℕ) (aX : (Option J × σ) → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : σ → ℤ) (NY : σ → ℕ) (MY : ℕ) (aY : σ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (K : Finset ι) (baseX : ∀ i, (Option J × σ) → ZMod (q i)) (baseY : ∀ i, σ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (D : ℕ) (a : J → ℤ)
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hpower : ∀ i, q i = prime i ^ power i) (hinj : Function.Injective prime) (hJ : 2 ≤ Fintype.card J)
    (w : ((Option J × σ) → ℤ) → ℝ) (f : (σ → ℤ) → ℝ) (B : ℕ)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (ξ : ℝ) (hξ : 0 < ξ) (hmask : affineSamplerPrimeMask prime ξ P MX MY D ⊆ K)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card σ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ))
    (shell : ℝ) (hshell : 0 < shell)
    (hB : K.card + CyclicCrootSisask.spectralIterations shell
      ((K.card : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B) :
    let c := affinePeriodProductCoupling (σ := σ) q D a
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 := by
  have hpair : Pairwise (fun i k => (q i).Coprime (q k)) := by
    intro i k hik
    rw [hpower i, hpower k]
    exact selectedPrimePowers_pairwise_coprime prime power hprime hinj hik
  have houtside := affineSamplerPrimeMask_outside prime power hprime hP K hmask
  have hcopX (i : ι) (hi : i ∉ K) : MX.Coprime (q i) := by
    rw [hpower i]
    exact (houtside i hi).1
  have hcopY (i : ι) (hi : i ∉ K) : MY.Coprime (q i) := by
    rw [hpower i]
    exact (houtside i hi).2.1
  have hDcop (i : ι) (hi : i ∉ K) : D.Coprime (q i) := by
    rw [hpower i]
    exact (houtside i hi).2.2.1
  have hlarge (i : ι) (hi : i ∉ K) : (prime i : ℝ)⁻¹ ≤ affineComparisonContraction ξ P :=
    (houtside i hi).2.2.2
  have hκ := affineComparisonContraction_bounds hξ hP
  exact affine_period_initial_conditioning_shell_small
    loX NX MX aX hneX loY NY MY aY hneY q hpair K baseX baseY uX uY
    D a hDcop prime power hprime hpower hJ w f B hκ.1.le hκ.2.1 hlarge
    hMX hMY hcopX hcopY hw hf P modLog dimX dimY hP hmodLog hcount hmoduli
    hdimX hdimY hlengthX hlengthY shell hshell hB

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.affine_masked_initial_conditioning_shell_small_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.affine_masked_initial_conditioning_shell_small_s2_oai.{u_1, u_2, u_3}
