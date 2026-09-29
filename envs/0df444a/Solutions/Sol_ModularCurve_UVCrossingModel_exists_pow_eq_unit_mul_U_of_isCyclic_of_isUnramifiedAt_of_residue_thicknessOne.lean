-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ca97b665-fc8d-553c-b62b-87e6f54540c5

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_isRegularLocalRing
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_eq_two
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Theorems.Thm_Ideal_finite_setOf_height_eq_one_and_mem
import Theorems.Thm_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
import Theorems.Thm_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
namespace KummerNorm44

section Residue

variable {W : Type*} [CommRing W] [IsLocalRing W]

noncomputable def resHom (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) :
    UVCrossingModel W c →+* IsLocalRing.ResidueField W :=
  Ideal.Quotient.lift (uvCrossingIdeal W c)
    ((IsLocalRing.residue W).comp (MvPowerSeries.constantCoeff (σ := Fin 2) (R := W)))
    (by
      intro f hf
      change f ∈ Ideal.span _ at hf
      rw [Ideal.mem_span_singleton] at hf
      obtain ⟨g, rfl⟩ := hf
      show (IsLocalRing.residue W) (MvPowerSeries.constantCoeff _) = 0
      rw [IsLocalRing.residue_eq_zero_iff, map_mul, map_sub, map_mul,
        MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, zero_mul, zero_sub]
      exact Ideal.mul_mem_right _ _ (neg_mem hc))

theorem resHom_mk (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (f : MvPowerSeries (Fin 2) W) :
    resHom c hc (UVCrossingModel.mk c f) = IsLocalRing.residue W (MvPowerSeries.constantCoeff f) :=
  rfl

theorem resHom_const (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (w : W) :
    resHom c hc (const c w) = IsLocalRing.residue W w := by
  change resHom c hc (UVCrossingModel.mk c (MvPowerSeries.C w)) = _
  rw [resHom_mk, MvPowerSeries.constantCoeff_C]

theorem resHom_U (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) : resHom c hc (U c) = 0 := by
  change resHom c hc (UVCrossingModel.mk c (MvPowerSeries.X 0)) = _
  rw [resHom_mk, MvPowerSeries.constantCoeff_X, map_zero]

theorem resHom_V (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) : resHom c hc (V c) = 0 := by
  change resHom c hc (UVCrossingModel.mk c (MvPowerSeries.X 1)) = _
  rw [resHom_mk, MvPowerSeries.constantCoeff_X, map_zero]

theorem resHom_surjective (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) :
    Function.Surjective (resHom c hc) := by
  intro x
  obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨const c w, resHom_const c hc w⟩

theorem ker_resHom (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) [IsLocalRing (UVCrossingModel W c)] :
    RingHom.ker (resHom c hc) = IsLocalRing.maximalIdeal (UVCrossingModel W c) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (resHom_surjective c hc))

theorem mem_maximalIdeal_iff_resHom (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (a : UVCrossingModel W c) :
    a ∈ IsLocalRing.maximalIdeal (UVCrossingModel W c) ↔ resHom c hc a = 0 := by
  rw [← ker_resHom c hc, RingHom.mem_ker]

theorem isUnit_iff_resHom (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (a : UVCrossingModel W c) :
    IsUnit a ↔ resHom c hc a ≠ 0 := by
  rw [Ne, ← mem_maximalIdeal_iff_resHom c hc, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

theorem isUnit_mk_iff (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (f : MvPowerSeries (Fin 2) W) :
    IsUnit (UVCrossingModel.mk c f) ↔ IsUnit (MvPowerSeries.constantCoeff f) := by
  rw [isUnit_iff_resHom c hc, resHom_mk, Ne, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem isUnit_const_iff (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (w : W) :
    IsUnit (const c w) ↔ IsUnit w := by
  change IsUnit (UVCrossingModel.mk c (MvPowerSeries.C w)) ↔ _
  rw [isUnit_mk_iff c hc, MvPowerSeries.constantCoeff_C]

theorem exists_const_mul_sub_one_mem (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)] (u : (UVCrossingModel W c)ˣ) :
    ∃ u₀ : Wˣ, (u : UVCrossingModel W c) * const c (↑u₀⁻¹ : W) - 1 ∈
      IsLocalRing.maximalIdeal (UVCrossingModel W c) := by
  obtain ⟨f, hf⟩ := UVCrossingModel.mk_surjective c (u : UVCrossingModel W c)
  have hu : IsUnit (MvPowerSeries.constantCoeff f) := by
    rw [← isUnit_mk_iff c hc, hf]; exact u.isUnit
  refine ⟨hu.unit, ?_⟩
  rw [mem_maximalIdeal_iff_resHom c hc, map_sub, map_one, map_mul, ← hf, resHom_mk, resHom_const,
    ← map_mul, IsUnit.mul_val_inv, map_one, sub_self]

end Residue

section Hensel

theorem exists_isUnit_pow_eq {S : Type*} [CommRing S] [IsLocalRing S]
    [HenselianRing S (IsLocalRing.maximalIdeal S)]
    (n : ℕ) (hn : IsUnit (n : S)) (a : S) (ha : a - 1 ∈ IsLocalRing.maximalIdeal S) :
    ∃ w : S, IsUnit w ∧ w ^ n = a := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨w, hw, hw1⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal S)
    (Polynomial.X ^ n - Polynomial.C a) (Polynomial.monic_X_pow_sub_C a hn0) 1
    (by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
        Polynomial.eval_C]
      rw [← Ideal.neg_mem_iff, neg_sub]; exact ha)
    (by
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        sub_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        one_pow, mul_one]
      exact hn.map _)
  refine ⟨w, ?_, ?_⟩
  · by_contra h
    have hw' : w ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr h
    have h1 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      have := Ideal.sub_mem _ hw' hw1; simp at this
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · have := hw
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] at this
    exact this

end Hensel

section ModelMap

variable {W : Type*} [CommRing W]

noncomputable def liftHom (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) :
    MvPowerSeries (Fin 2) W →+* MvPowerSeries (Fin 2) W :=
  (MvPowerSeries.expand n hn).toRingHom.comp (MvPowerSeries.rescale c)

theorem rescale_C' (c : Fin 2 → W) (w : W) :
    MvPowerSeries.rescale c (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = MvPowerSeries.C w := by
  classical
  ext e
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem rescale_X' (c : Fin 2 → W) (i : Fin 2) :
    MvPowerSeries.rescale c (MvPowerSeries.X i : MvPowerSeries (Fin 2) W) =
      MvPowerSeries.C (c i) * MvPowerSeries.X i := by
  classical
  ext e
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs with h
  · subst h; simp
  · simp

theorem liftHom_C (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) (w : W) :
    liftHom n hn c (MvPowerSeries.C w) = MvPowerSeries.C w := by
  simp [liftHom, rescale_C', MvPowerSeries.expand_C]

theorem liftHom_X (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) (i : Fin 2) :
    liftHom n hn c (MvPowerSeries.X i) = MvPowerSeries.C (c i) * MvPowerSeries.X i ^ n := by
  simp [liftHom, rescale_X', MvPowerSeries.expand_C, MvPowerSeries.expand_X]

theorem liftHom_crossing_mem (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) (hc : c 0 * c 1 = 1)
    (π : W) (m : ℕ) :
    liftHom n hn c ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
        MvPowerSeries.C (π ^ (m * n))) ∈ uvCrossingIdeal W (π ^ m) := by
  change _ ∈ Ideal.span _
  rw [Ideal.mem_span_singleton, map_sub, map_mul, liftHom_X, liftHom_X, liftHom_C]
  have : MvPowerSeries.C (c 0) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ^ n *
      (MvPowerSeries.C (c 1) * MvPowerSeries.X 1 ^ n) - MvPowerSeries.C (π ^ (m * n)) =
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1) ^ n -
        (MvPowerSeries.C (π ^ m)) ^ n := by
    rw [← map_pow, ← pow_mul, mul_pow]
    have h1 : MvPowerSeries.C (c 0) * MvPowerSeries.C (c 1) = (1 : MvPowerSeries (Fin 2) W) := by
      rw [← map_mul, hc, map_one]
    linear_combination (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ^ n *
      (MvPowerSeries.X 1) ^ n * h1
  rw [this]
  exact sub_dvd_pow_sub_pow _ _ n

noncomputable def modelMap (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) (hc : c 0 * c 1 = 1) (π : W) (m : ℕ) :
    UVCrossingModel W (π ^ (m * n)) →+* UVCrossingModel W (π ^ m) :=
  Ideal.quotientMap (uvCrossingIdeal W (π ^ m)) (liftHom n hn c) (by
    change Ideal.span _ ≤ _
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact liftHom_crossing_mem n hn c hc π m)

variable (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) (hc : c 0 * c 1 = 1) (π : W) (m : ℕ)

theorem modelMap_mk (f : MvPowerSeries (Fin 2) W) :
    modelMap n hn c hc π m (UVCrossingModel.mk _ f) = UVCrossingModel.mk _ (liftHom n hn c f) :=
  rfl

theorem modelMap_const (w : W) :
    modelMap n hn c hc π m (const _ w) = const _ w := by
  change modelMap n hn c hc π m (UVCrossingModel.mk _ (MvPowerSeries.C w)) = UVCrossingModel.mk _ _
  rw [modelMap_mk, liftHom_C]

theorem modelMap_U :
    modelMap n hn c hc π m (U _) = const _ (c 0) * U (π ^ m) ^ n := by
  change modelMap n hn c hc π m (UVCrossingModel.mk _ (MvPowerSeries.X 0)) =
    UVCrossingModel.mk _ _ * UVCrossingModel.mk _ _ ^ n
  rw [modelMap_mk, liftHom_X, map_mul, map_pow]

theorem modelMap_V :
    modelMap n hn c hc π m (V _) = const _ (c 1) * V (π ^ m) ^ n := by
  change modelMap n hn c hc π m (UVCrossingModel.mk _ (MvPowerSeries.X 1)) =
    UVCrossingModel.mk _ _ * UVCrossingModel.mk _ _ ^ n
  rw [modelMap_mk, liftHom_X, map_mul, map_pow]

end ModelMap

end KummerNorm44

namespace KummerNorm44

section Generation

variable {W : Type*} [CommRing W]

noncomputable def blockPart (n i j : ℕ) (F : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  fun e => MvPowerSeries.coeff (n • e + (Finsupp.single 0 i + Finsupp.single 1 j)) F

theorem coeff_blockPart (n i j : ℕ) (F : MvPowerSeries (Fin 2) W) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (blockPart n i j F) =
      MvPowerSeries.coeff (n • e + (Finsupp.single 0 i + Finsupp.single 1 j)) F := by
  rw [MvPowerSeries.coeff_apply]; rfl

theorem ev0 (i j : ℕ) : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j : Fin 2 →₀ ℕ) 0 = i := by simp

theorem ev1 (i j : ℕ) : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j : Fin 2 →₀ ℕ) 1 = j := by simp

theorem dpair_le_iff (i j : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j ≤ e ↔ i ≤ e 0 ∧ j ≤ e 1 := by
  rw [Finsupp.le_def]
  constructor
  · intro h; exact ⟨by simpa [ev0] using h 0, by simpa [ev1] using h 1⟩
  · rintro ⟨h0, h1⟩ k
    fin_cases k
    · simpa [ev0] using h0
    · simpa [ev1] using h1

theorem sum_monomial_mul_expand_blockPart (n : ℕ) (hn : n ≠ 0) (F : MvPowerSeries (Fin 2) W) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      MvPowerSeries.monomial (Finsupp.single 0 i + Finsupp.single 1 j) (1 : W) *
        MvPowerSeries.expand n hn (blockPart n i j F)) = F := by
  classical
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  ext e
  simp only [map_sum, MvPowerSeries.coeff_monomial_mul, one_mul]
  have hdm0 := Nat.div_add_mod (e 0) n
  have hdm1 := Nat.div_add_mod (e 1) n
  rw [Finset.sum_eq_single_of_mem (e 0 % n) (Finset.mem_range.mpr (Nat.mod_lt _ hpos)),
    Finset.sum_eq_single_of_mem (e 1 % n) (Finset.mem_range.mpr (Nat.mod_lt _ hpos))]
  ·
    have hle : Finsupp.single (0 : Fin 2) (e 0 % n) + Finsupp.single 1 (e 1 % n) ≤ e := by
      rw [dpair_le_iff]; exact ⟨Nat.mod_le _ _, Nat.mod_le _ _⟩
    rw [if_pos hle]
    have hq : e - (Finsupp.single (0 : Fin 2) (e 0 % n) + Finsupp.single 1 (e 1 % n)) =
        n • (Finsupp.single (0 : Fin 2) (e 0 / n) + Finsupp.single 1 (e 1 / n)) := by
      ext k
      rw [Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul]
      fin_cases k
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ev0]; omega
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ev1]; omega
    have he : n • (Finsupp.single (0 : Fin 2) (e 0 / n) + Finsupp.single 1 (e 1 / n)) +
        (Finsupp.single (0 : Fin 2) (e 0 % n) + Finsupp.single 1 (e 1 % n)) = e := by
      ext k
      rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      fin_cases k
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ev0]; omega
      · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ev1]; omega
    rw [hq, MvPowerSeries.coeff_expand_smul, coeff_blockPart, he]
  ·
    intro j hj hne
    split_ifs with hle
    · apply MvPowerSeries.coeff_expand_of_not_dvd (i := 1)
      rw [dpair_le_iff] at hle
      rw [Finsupp.tsub_apply, ev1]
      rintro ⟨k, hk⟩
      apply hne
      have hjn : j < n := Finset.mem_range.mp hj
      have : e 1 = n * k + j := by omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hjn]
    · rfl
  ·
    intro i hi hne
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs with hle
    · apply MvPowerSeries.coeff_expand_of_not_dvd (i := 0)
      rw [dpair_le_iff] at hle
      rw [Finsupp.tsub_apply, ev0]
      rintro ⟨k, hk⟩
      apply hne
      have hin : i < n := Finset.mem_range.mp hi
      have : e 0 = n * k + i := by omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hin]
    · rfl

variable (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) (hc : c 0 * c 1 = 1) (π : W) (m : ℕ)

theorem expand_eq_liftHom_rescale (c' : Fin 2 → W) (hc' : ∀ i, c' i * c i = 1)
    (G : MvPowerSeries (Fin 2) W) :
    MvPowerSeries.expand n hn G = liftHom n hn c (MvPowerSeries.rescale c' G) := by
  simp only [liftHom, RingHom.coe_comp, Function.comp_apply, MvPowerSeries.rescale_rescale]
  have : c' * c = 1 := funext hc'
  rw [this, MvPowerSeries.rescale_one]
  rfl

theorem exists_eq_sum_modelMap_mul (c' : Fin 2 → W) (hc' : ∀ i, c' i * c i = 1)
    (r : UVCrossingModel W (π ^ m)) :
    ∃ g : ℕ → ℕ → UVCrossingModel W (π ^ (m * n)),
      r = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        modelMap n hn c hc π m (g i j) * (U (π ^ m) ^ i * V (π ^ m) ^ j) := by
  obtain ⟨F, rfl⟩ := UVCrossingModel.mk_surjective (π ^ m) r
  refine ⟨fun i j => UVCrossingModel.mk _ (MvPowerSeries.rescale c' (blockPart n i j F)), ?_⟩
  conv_lhs => rw [← sum_monomial_mul_expand_blockPart n hn F]
  simp only [map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [modelMap_mk, ← expand_eq_liftHom_rescale n hn c c' hc', mul_comm]
  congr 1
  change UVCrossingModel.mk _ _ = UVCrossingModel.mk _ (MvPowerSeries.X 0) ^ i *
    UVCrossingModel.mk _ (MvPowerSeries.X 1) ^ j
  rw [← map_pow, ← map_pow, ← map_mul, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.monomial_mul_monomial, mul_one]

theorem moduleFinite_modelMap (c' : Fin 2 → W) (hc' : ∀ i, c' i * c i = 1) :
    letI := (modelMap n hn c hc π m).toAlgebra
    Module.Finite (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ m)) := by
  letI := (modelMap n hn c hc π m).toAlgebra
  classical
  let S : Finset (UVCrossingModel W (π ^ m)) :=
    (Finset.range n ×ˢ Finset.range n).image fun p => U (π ^ m) ^ p.1 * V (π ^ m) ^ p.2
  refine ⟨⟨S, ?_⟩⟩
  rw [Submodule.eq_top_iff']
  intro r
  obtain ⟨g, hg⟩ := exists_eq_sum_modelMap_mul n hn c hc π m c' hc' r
  rw [hg]
  refine Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun j hj => ?_
  have : modelMap n hn c hc π m (g i j) * (U (π ^ m) ^ i * V (π ^ m) ^ j) =
      g i j • (U (π ^ m) ^ i * V (π ^ m) ^ j) := (Algebra.smul_def _ _).symm
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [S, Finset.coe_image, Finset.coe_product, Finset.coe_range, Set.mem_image,
    Set.mem_prod, Set.mem_Iio, Prod.exists]
  exact ⟨i, j, ⟨Finset.mem_range.mp hi, Finset.mem_range.mp hj⟩, rfl⟩

end Generation

end KummerNorm44

namespace KummerNorm44

section Injective

variable {W : Type*} [CommRing W]

theorem X_mul_X_eq_monomial :
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 =
      MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]

theorem coeff_single_crossing_mul (c : W) (s : Fin 2) (a : ℕ) (Q : MvPowerSeries (Fin 2) W) :
    MvPowerSeries.coeff (Finsupp.single s a)
      (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C c) * Q) =
      -(c * MvPowerSeries.coeff (Finsupp.single s a) Q) := by
  classical
  rw [sub_mul, map_sub, MvPowerSeries.coeff_C_mul, X_mul_X_eq_monomial,
    MvPowerSeries.coeff_monomial_mul, if_neg, zero_sub]
  rw [dpair_le_iff]
  fin_cases s <;> simp

theorem coeff_single_liftHom (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) (s : Fin 2) (k : ℕ)
    (G : MvPowerSeries (Fin 2) W) :
    MvPowerSeries.coeff (Finsupp.single s (n * k)) (liftHom n hn c G) =
      c s ^ k * MvPowerSeries.coeff (Finsupp.single s k) G := by
  have : Finsupp.single s (n * k) = n • Finsupp.single s k := by
    rw [Finsupp.smul_single, smul_eq_mul]
  simp only [liftHom, RingHom.coe_comp, Function.comp_apply]
  rw [this]
  erw [MvPowerSeries.coeff_expand_smul]
  rw [MvPowerSeries.coeff_rescale, Finsupp.prod_single_index (h := fun s m => c s ^ m) (pow_zero _)]

theorem axis_coeff_mem_of_liftHom_mem (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W)
    (hc0 : IsUnit (c 0)) (hc1 : IsUnit (c 1)) (π : W) (m : ℕ) (hm : m ≠ 0)
    (G : MvPowerSeries (Fin 2) W) (hG : liftHom n hn c G ∈ uvCrossingIdeal W (π ^ m))
    (s : Fin 2) (k : ℕ) : MvPowerSeries.coeff (Finsupp.single s k) G ∈ Ideal.span {π} := by
  change _ ∈ Ideal.span _ at hG
  rw [Ideal.mem_span_singleton] at hG
  obtain ⟨Q, hQ⟩ := hG
  have h := coeff_single_liftHom n hn c s k G
  rw [hQ, coeff_single_crossing_mul] at h
  have hu : IsUnit (c s ^ k) := by
    fin_cases s
    · exact hc0.pow k
    · exact hc1.pow k
  rw [← Ideal.unit_mul_mem_iff_mem _ hu, ← h]
  refine neg_mem (Ideal.mul_mem_right _ _ ?_)
  exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self π) m (Nat.pos_of_ne_zero hm)

theorem exists_eq_C_mul_add_X_mul_X_mul (π : W) (G : MvPowerSeries (Fin 2) W)
    (h : ∀ (s : Fin 2) (k : ℕ), MvPowerSeries.coeff (Finsupp.single s k) G ∈ Ideal.span {π}) :
    ∃ G₁ G₂ : MvPowerSeries (Fin 2) W,
      G = MvPowerSeries.C π * G₁ + MvPowerSeries.X 0 * MvPowerSeries.X 1 * G₂ := by
  classical
  have hax : ∀ e : Fin 2 →₀ ℕ, e 0 = 0 ∨ e 1 = 0 → ∃ b : W, b * π = MvPowerSeries.coeff e G := by
    intro e he
    have : ∃ (s : Fin 2) (k : ℕ), e = Finsupp.single s k := by
      rcases he with h0 | h1
      · refine ⟨1, e 1, ?_⟩
        ext k; fin_cases k
        · simp only [Fin.zero_eta, Fin.isValue]; simp [h0]
        · simp only [Fin.mk_one, Fin.isValue]; simp
      · refine ⟨0, e 0, ?_⟩
        ext k; fin_cases k
        · simp only [Fin.zero_eta, Fin.isValue]; simp
        · simp only [Fin.mk_one, Fin.isValue]; simp [h1]
    obtain ⟨s, k, rfl⟩ := this
    exact Ideal.mem_span_singleton'.mp (h s k)
  choose b hb using hax
  refine ⟨fun e => if he : e 0 = 0 ∨ e 1 = 0 then b e he else 0,
    fun e => MvPowerSeries.coeff (e + (Finsupp.single 0 1 + Finsupp.single 1 1)) G, ?_⟩
  ext e
  rw [map_add, MvPowerSeries.coeff_C_mul, X_mul_X_eq_monomial, MvPowerSeries.coeff_monomial_mul,
    one_mul]
  by_cases he : e 0 = 0 ∨ e 1 = 0
  · rw [if_neg]
    · change MvPowerSeries.coeff e G = π * (if he : e 0 = 0 ∨ e 1 = 0 then b e he else 0) + 0
      rw [dif_pos he, add_zero, mul_comm, hb]
    · rw [dpair_le_iff]; omega
  · have hle : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 ≤ e := by
      rw [dpair_le_iff]; omega
    rw [if_pos hle]
    change MvPowerSeries.coeff e G = π * (if he : e 0 = 0 ∨ e 1 = 0 then b e he else 0) +
      MvPowerSeries.coeff (e - (Finsupp.single 0 1 + Finsupp.single 1 1) +
        (Finsupp.single 0 1 + Finsupp.single 1 1)) G
    rw [dif_neg he, mul_zero, zero_add, tsub_add_cancel_of_le hle]

theorem U_mul_V_eq_const (c : W) : U c * V c = const c c := by
  change UVCrossingModel.mk c _ * UVCrossingModel.mk c _ = UVCrossingModel.mk c _
  rw [← map_mul]
  apply (Ideal.Quotient.eq).mpr
  change _ ∈ Ideal.span _
  exact Ideal.subset_span rfl

theorem const_mul (c a b : W) : const c a * const c b = const c (a * b) := by
  exact (map_mul (constHom c) a b).symm

theorem const_mem_nonZeroDivisors_of_pow (c π : W) (m : ℕ) (hm : m ≠ 0)
    (h : const c (π ^ m) ∈ nonZeroDivisors (UVCrossingModel W c)) :
    const c π ∈ nonZeroDivisors (UVCrossingModel W c) := by
  rw [mem_nonZeroDivisors_iff_right] at h ⊢
  intro x hx
  apply h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [show const c (π ^ (k + 1)) = const c π ^ (k + 1) from map_pow (constHom c) π (k + 1),
    pow_succ', ← mul_assoc, hx, zero_mul]

theorem modelMap_injective [IsNoetherianRing W] [IsLocalRing W]
    (n : ℕ) (hn : n ≠ 0) (c : Fin 2 → W) (hc : c 0 * c 1 = 1)
    (hc0 : IsUnit (c 0)) (hc1 : IsUnit (c 1))
    (π : W) (hπ : π ∈ IsLocalRing.maximalIdeal W) (hπ0 : π ∈ nonZeroDivisors W)
    (m : ℕ) (hm : m ≠ 0)
    [IsLocalRing (UVCrossingModel W (π ^ (m * n)))] :
    Function.Injective (modelMap n hn c hc π m) := by
  classical
  set φ := modelMap n hn c hc π m
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ (m * n))) :=
    ModularCurve.UVCrossingModel.isNoetherianRing _
  rw [RingHom.injective_iff_ker_eq_bot]

  have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm hn)
  have hπmn : π ^ (m * n) ∈ IsLocalRing.maximalIdeal W := Ideal.pow_mem_of_mem _ hπ _ hmn
  have hnzd : const (π ^ m) π ∈ nonZeroDivisors (UVCrossingModel W (π ^ m)) :=
    const_mem_nonZeroDivisors_of_pow _ π m hm
      (ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors (pow_mem hπ0 m))
  have key : ∀ r ∈ RingHom.ker φ, ∃ r' ∈ RingHom.ker φ, r = const (π ^ (m * n)) π * r' := by
    intro r hr
    obtain ⟨G, rfl⟩ := UVCrossingModel.mk_surjective _ r
    rw [RingHom.mem_ker] at hr
    change UVCrossingModel.mk _ (liftHom n hn c G) = 0 at hr
    have hG : liftHom n hn c G ∈ uvCrossingIdeal W (π ^ m) := Ideal.Quotient.eq_zero_iff_mem.mp hr
    obtain ⟨G₁, G₂, hG12⟩ := exists_eq_C_mul_add_X_mul_X_mul π G
      (axis_coeff_mem_of_liftHom_mem n hn c hc0 hc1 π m hm G hG)
    refine ⟨UVCrossingModel.mk _ G₁ + const _ (π ^ (m * n - 1)) * UVCrossingModel.mk _ G₂, ?_, ?_⟩
    swap
    · rw [hG12, map_add, map_mul, map_mul, map_mul]
      change const _ π * _ + U _ * V _ * _ = _
      rw [U_mul_V_eq_const, mul_add, ← mul_assoc, const_mul, ← pow_succ', Nat.sub_add_cancel hmn]
    ·
      rw [RingHom.mem_ker]
      have h0 : φ (const (π ^ (m * n)) π) * φ (UVCrossingModel.mk _ G₁ +
          const _ (π ^ (m * n - 1)) * UVCrossingModel.mk _ G₂) = 0 := by
        rw [← map_mul]
        have : const (π ^ (m * n)) π * (UVCrossingModel.mk _ G₁ +
            const _ (π ^ (m * n - 1)) * UVCrossingModel.mk _ G₂) = UVCrossingModel.mk _ G := by
          rw [hG12, map_add, map_mul, map_mul, map_mul]
          change _ = const _ π * _ + U _ * V _ * _
          rw [U_mul_V_eq_const, mul_add, ← mul_assoc, const_mul, ← pow_succ', Nat.sub_add_cancel hmn]
        rw [this]; exact hr
      rw [show φ (const (π ^ (m * n)) π) = const (π ^ m) π from modelMap_const n hn c hc π m π]
        at h0
      exact (mem_nonZeroDivisors_iff_right.mp hnzd) _ (by rwa [mul_comm] at h0)
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {const (π ^ (m * n)) π})
  · exact IsNoetherian.noetherian _
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := key r hr
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hr'
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    rw [mem_nonunits_iff, isUnit_const_iff _ hπmn]
    exact (IsLocalRing.mem_maximalIdeal _).mp hπ

end Injective

end KummerNorm44

namespace KummerNorm44

section Irreducible

variable {W : Type*} [CommRing W]

noncomputable def axisRes : MvPowerSeries (Fin 2) W →+* PowerSeries W where
  toFun G := PowerSeries.mk fun l => MvPowerSeries.coeff (Finsupp.single 1 l) G
  map_one' := by
    classical
    ext l
    rw [PowerSeries.coeff_mk, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
    simp [Finsupp.single_eq_zero]
  map_mul' A B := by
    classical
    ext l
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
      Finsupp.antidiagonal_single, Finset.sum_map]
    simp [PowerSeries.coeff_mk]
  map_zero' := by ext l; simp [PowerSeries.coeff_mk]
  map_add' A B := by ext l; simp [PowerSeries.coeff_mk]

theorem coeff_axisRes (G : MvPowerSeries (Fin 2) W) (l : ℕ) :
    PowerSeries.coeff l (axisRes G) = MvPowerSeries.coeff (Finsupp.single 1 l) G := by
  unfold axisRes
  simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, PowerSeries.coeff_mk]

theorem axisRes_X_zero : axisRes (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) = 0 := by
  classical
  ext l
  rw [coeff_axisRes, MvPowerSeries.coeff_X, map_zero, if_neg]
  intro h
  have := congrArg (fun f => f 0) h
  simp at this

theorem axisRes_C (w : W) : axisRes (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = PowerSeries.C w := by
  classical
  ext l
  rw [coeff_axisRes, MvPowerSeries.coeff_C, PowerSeries.coeff_C]
  simp [Finsupp.single_eq_zero]

variable [IsLocalRing W]

noncomputable def tau (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) :
    UVCrossingModel W c →+* PowerSeries (IsLocalRing.ResidueField W) :=
  Ideal.Quotient.lift (uvCrossingIdeal W c)
    ((PowerSeries.map (IsLocalRing.residue W)).comp axisRes)
    (by
      intro f hf
      change f ∈ Ideal.span _ at hf
      rw [Ideal.mem_span_singleton] at hf
      obtain ⟨g, rfl⟩ := hf
      simp only [RingHom.comp_apply, map_mul, map_sub, axisRes_X_zero, zero_mul, zero_sub, axisRes_C,
        map_neg, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff c).mpr hc, map_zero, neg_zero])

theorem tau_mk (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (G : MvPowerSeries (Fin 2) W) :
    tau c hc (UVCrossingModel.mk c G) = PowerSeries.map (IsLocalRing.residue W) (axisRes G) :=
  rfl

theorem tau_U (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) : tau c hc (U c) = 0 := by
  change tau c hc (UVCrossingModel.mk c (MvPowerSeries.X 0)) = 0
  rw [tau_mk, axisRes_X_zero, map_zero]

theorem residue_constantCoeff_eq_zero_of_tau (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    (G : MvPowerSeries (Fin 2) W) (h : tau c hc (UVCrossingModel.mk c G) = 0) :
    IsLocalRing.residue W (MvPowerSeries.constantCoeff G) = 0 := by
  have := congrArg (PowerSeries.coeff 0) h
  rw [tau_mk, PowerSeries.coeff_map, coeff_axisRes, Finsupp.single_zero,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_zero] at this
  exact this

theorem residue_coeff10_eq (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    (G G' : MvPowerSeries (Fin 2) W) (h : UVCrossingModel.mk c G = UVCrossingModel.mk c G') :
    IsLocalRing.residue W (MvPowerSeries.coeff (Finsupp.single 0 1) G) =
      IsLocalRing.residue W (MvPowerSeries.coeff (Finsupp.single 0 1) G') := by
  have hsub : G - G' ∈ uvCrossingIdeal W c := (Ideal.Quotient.eq).mp h
  change _ ∈ Ideal.span _ at hsub
  rw [Ideal.mem_span_singleton] at hsub
  obtain ⟨Q, hQ⟩ := hsub
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) hQ
  rw [map_sub, coeff_single_crossing_mul] at this
  rw [← sub_eq_zero, ← map_sub, this, map_neg, map_mul, (IsLocalRing.residue_eq_zero_iff c).mpr hc,
    zero_mul, neg_zero]

theorem residue_coeff10_eq_zero_of_mem_sq (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    (r : UVCrossingModel W c) (hr : r ∈ RingHom.ker (tau c hc) ^ 2)
    (G : MvPowerSeries (Fin 2) W) (hG : UVCrossingModel.mk c G = r) :
    IsLocalRing.residue W (MvPowerSeries.coeff (Finsupp.single 0 1) G) = 0 := by
  classical
  rw [pow_two, ← Ideal.smul_eq_mul] at hr
  revert G
  refine Submodule.smul_induction_on hr ?_ ?_
  · intro a ha b hb G hG
    obtain ⟨A, rfl⟩ := UVCrossingModel.mk_surjective c a
    obtain ⟨B, rfl⟩ := UVCrossingModel.mk_surjective c b
    rw [RingHom.mem_ker] at ha hb
    have hA := residue_constantCoeff_eq_zero_of_tau c hc A ha
    have hB := residue_constantCoeff_eq_zero_of_tau c hc B hb
    rw [residue_coeff10_eq c hc G (A * B) (by rw [hG, smul_eq_mul, map_mul])]
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map,
      Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst,
      Prod.map_snd, Prod.map_apply, zero_add, Finsupp.single_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_add, map_mul, hA, hB, zero_mul, mul_zero,
      add_zero]
  · intro x y hx hy G hG
    obtain ⟨X, rfl⟩ := UVCrossingModel.mk_surjective c x
    obtain ⟨Y, rfl⟩ := UVCrossingModel.mk_surjective c y
    rw [residue_coeff10_eq c hc G (X + Y) (by rw [hG, map_add]), map_add, map_add, hx X rfl,
      hy Y rfl, add_zero]

theorem irreducible_X_pow_sub_C_unit_mul_U (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsDomain (UVCrossingModel W c)] [IsLocalRing (UVCrossingModel W c)]
    (n : ℕ) (hn : n ≠ 0) (u : (UVCrossingModel W c)ˣ) :
    Irreducible (Polynomial.X ^ n - Polynomial.C ((u : UVCrossingModel W c) * U c)) := by
  classical
  set P := RingHom.ker (tau c hc) with hP
  have hprime : P.IsPrime := RingHom.ker_isPrime _
  have hmonic := Polynomial.monic_X_pow_sub_C ((u : UVCrossingModel W c) * U c) hn
  have hUmem : (u : UVCrossingModel W c) * U c ∈ P := by
    rw [hP, RingHom.mem_ker, map_mul, tau_U, mul_zero]
  refine Polynomial.IsEisensteinAt.irreducible (𝓟 := P)
    { leading := ?_, mem := fun {k} hk => ?_, notMem := ?_ } hprime hmonic.isPrimitive
    (by rw [Polynomial.natDegree_X_pow_sub_C]; exact Nat.pos_of_ne_zero hn)
  · rw [hmonic.leadingCoeff]
    exact (Ideal.ne_top_iff_one P).mp hprime.ne_top
  · rw [Polynomial.natDegree_X_pow_sub_C] at hk
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hk.ne]
    split_ifs
    · rw [zero_sub]; exact neg_mem hUmem
    · rw [sub_zero]; exact zero_mem P
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg (Ne.symm hn),
      if_pos rfl, zero_sub]
    intro hmem
    have hmem' : (u : UVCrossingModel W c) * U c ∈ P ^ 2 := by
      have := neg_mem hmem; rwa [neg_neg] at this
    obtain ⟨A, hA⟩ := UVCrossingModel.mk_surjective c (u : UVCrossingModel W c)
    have hres := residue_coeff10_eq_zero_of_mem_sq c hc _ hmem' (A * MvPowerSeries.X 0)
      (by rw [map_mul, hA]; rfl)
    have hcoeff : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (A * MvPowerSeries.X 0) =
        MvPowerSeries.constantCoeff A := by
      rw [mul_comm, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, if_pos le_rfl, one_mul,
        tsub_self, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [hcoeff, IsLocalRing.residue_eq_zero_iff] at hres
    have hu : IsUnit (MvPowerSeries.constantCoeff A) := by
      rw [← isUnit_mk_iff c hc, hA]; exact u.isUnit
    exact (IsLocalRing.mem_maximalIdeal _).mp hres hu

end Irreducible

end KummerNorm44

namespace KummerClass44

open KummerNorm44

section Twist

variable {W : Type*} [CommRing W]

theorem rescale_crossing (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (c : W) :
    MvPowerSeries.rescale z ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
      MvPowerSeries.C c) = MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C c := by
  rw [map_sub, map_mul, rescale_X', rescale_X', rescale_C']
  have h1 : MvPowerSeries.C (z 0) * MvPowerSeries.C (z 1) = (1 : MvPowerSeries (Fin 2) W) := by
    rw [← map_mul, hz, map_one]
  linear_combination (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 * h1

private noncomputable def _root_.KummerClass44.twist (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (c : W) :
    UVCrossingModel W c →+* UVCrossingModel W c :=
  Ideal.quotientMap (uvCrossingIdeal W c) (MvPowerSeries.rescale z) (by
    change Ideal.span _ ≤ _
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, rescale_crossing z hz c]
    exact Ideal.subset_span rfl)

p2m_export "KummerClass44" "twist"
variable (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (c : W)

theorem twist_mk (f : MvPowerSeries (Fin 2) W) :
    twist z hz c (UVCrossingModel.mk c f) = UVCrossingModel.mk c (MvPowerSeries.rescale z f) := rfl

theorem twist_const (w : W) : twist z hz c (const c w) = const c w := by
  change twist z hz c (UVCrossingModel.mk c (MvPowerSeries.C w)) = UVCrossingModel.mk c _
  rw [twist_mk, rescale_C']

theorem twist_U : twist z hz c (U c) = const c (z 0) * U c := by
  change twist z hz c (UVCrossingModel.mk c (MvPowerSeries.X 0)) = UVCrossingModel.mk c _ * UVCrossingModel.mk c _
  rw [twist_mk, rescale_X', map_mul]

theorem twist_V : twist z hz c (V c) = const c (z 1) * V c := by
  change twist z hz c (UVCrossingModel.mk c (MvPowerSeries.X 1)) = UVCrossingModel.mk c _ * UVCrossingModel.mk c _
  rw [twist_mk, rescale_X', map_mul]

theorem twist_comp (z' : Fin 2 → W) (hz' : z' 0 * z' 1 = 1) (r : UVCrossingModel W c) :
    twist z hz c (twist z' hz' c r) = twist (z' * z) (by
      show z' 0 * z 0 * (z' 1 * z 1) = 1
      linear_combination (z' 0 * z' 1) * hz + hz') c r := by
  obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective c r
  rw [twist_mk, twist_mk, twist_mk, MvPowerSeries.rescale_rescale]

theorem twist_one (h : (1 : Fin 2 → W) 0 * (1 : Fin 2 → W) 1 = 1) (r : UVCrossingModel W c) :
    twist 1 h c r = r := by
  obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective c r
  rw [twist_mk, MvPowerSeries.rescale_one]; rfl

theorem rescale_expand (n : ℕ) (hn : n ≠ 0) (G : MvPowerSeries (Fin 2) W) :
    MvPowerSeries.rescale z (MvPowerSeries.expand n hn G) =
      MvPowerSeries.expand n hn (MvPowerSeries.rescale (z ^ n) G) := by
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_eq_subst, MvPowerSeries.expand,
    MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_pow hn) (MvPowerSeries.HasSubst.smul_X z),
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.smul_X (z ^ n)) (MvPowerSeries.HasSubst.X_pow hn)]
  congr 1
  funext s
  rw [MvPowerSeries.subst_pow (MvPowerSeries.HasSubst.smul_X z), MvPowerSeries.subst_X (MvPowerSeries.HasSubst.smul_X z)]
  show (z s • (MvPowerSeries.X s : MvPowerSeries (Fin 2) W)) ^ n =
    MvPowerSeries.subst (fun s => (MvPowerSeries.X s : MvPowerSeries (Fin 2) W) ^ n)
      ((z ^ n) s • (MvPowerSeries.X s : MvPowerSeries (Fin 2) W))
  rw [MvPowerSeries.subst_smul (MvPowerSeries.HasSubst.X_pow hn), MvPowerSeries.subst_X (MvPowerSeries.HasSubst.X_pow hn),
    smul_pow, Pi.pow_apply]

theorem twist_modelMap (n : ℕ) (hn : n ≠ 0) (hzn : z ^ n = 1) (π : W) (m : ℕ)
    (h1 : (1 : Fin 2 → W) 0 * (1 : Fin 2 → W) 1 = 1) (r : UVCrossingModel W (π ^ (m * n))) :
    twist z hz (π ^ m) (modelMap n hn 1 h1 π m r) = modelMap n hn 1 h1 π m r := by
  obtain ⟨G, rfl⟩ := UVCrossingModel.mk_surjective _ r
  rw [modelMap_mk, twist_mk]
  congr 1
  simp only [liftHom, RingHom.coe_comp, Function.comp_apply, MvPowerSeries.rescale_one, RingHom.id_apply]
  show MvPowerSeries.rescale z (MvPowerSeries.expand n hn G) = MvPowerSeries.expand n hn G
  rw [rescale_expand z n hn, hzn, MvPowerSeries.rescale_one]; rfl

end Twist

end KummerClass44

namespace KummerClass44

open KummerNorm44

section Invariants

variable {W : Type*} [CommRing W] [IsDomain W]

omit [IsDomain W] in
theorem const_pow (c a : W) (k : ℕ) : const c a ^ k = const c (a ^ k) := (map_pow (constHom c) a k).symm

omit [IsDomain W] in
theorem const_zero (c : W) : const c (0 : W) = 0 := map_zero (constHom c)

omit [IsDomain W] in
theorem const_sum (c : W) {ι : Type*} (s : Finset ι) (f : ι → W) :
    const c (∑ t ∈ s, f t) = ∑ t ∈ s, const c (f t) := map_sum (constHom c) f s

omit [IsDomain W] in
theorem twist_congr {z z' : Fin 2 → W} (hz : z 0 * z 1 = 1) (hz' : z' 0 * z' 1 = 1) (c : W) (h : z = z') :
    twist z hz c = twist z' hz' c := by subst h; rfl

theorem sum_pow_eq_of_pow_eq_one {η : W} (n : ℕ) (hη : η ^ n = 1) (hη1 : η ≠ 1) :
    ∑ t ∈ Finset.range n, η ^ t = 0 := by
  have := geom_sum_mul η n
  rw [hη, sub_self, mul_eq_zero] at this
  exact this.resolve_right (sub_ne_zero.mpr hη1)

theorem mem_range_modelMap_of_twist_eq
    (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W)) (ζ : W) (hζ : IsPrimitiveRoot ζ n)
    (π : W) (m : ℕ) (h1 : (1 : Fin 2 → W) 0 * (1 : Fin 2 → W) 1 = 1)
    (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (hz0 : z 0 = ζ)
    (r : UVCrossingModel W (π ^ m)) (hr : twist z hz (π ^ m) r = r) :
    r ∈ (modelMap n hn.ne' 1 h1 π m).range := by
  classical
  set φ := modelMap n hn.ne' 1 h1 π m with hφ
  have hz0n : z 0 ^ n = 1 := by rw [hz0]; exact hζ.pow_eq_one
  have hz1n : z 1 ^ n = 1 := by
    have h := congrArg (· ^ n) hz
    simp only [mul_pow, one_pow] at h
    rwa [hz0n, one_mul] at h
  have hzn : z ^ n = 1 := by
    funext i; fin_cases i
    · exact hz0n
    · exact hz1n

  let zp : ℕ → Fin 2 → W := fun t => z ^ t
  have hzp : ∀ t, zp t 0 * zp t 1 = 1 := by
    intro t; show z 0 ^ t * z 1 ^ t = 1; rw [← mul_pow, hz, one_pow]
  have hzpn : ∀ t, zp t ^ n = 1 := by
    intro t; show (z ^ t) ^ n = 1; rw [← pow_mul, mul_comm, pow_mul, hzn, one_pow]
  have hiter : ∀ t, twist (zp t) (hzp t) (π ^ m) r = r := by
    intro t
    induction t with
    | zero =>
      obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective _ r
      rw [twist_mk]
      simp only [zp, pow_zero, MvPowerSeries.rescale_one, RingHom.id_apply]
    | succ t ih =>
      have hcomp := twist_comp z hz (π ^ m) (zp t) (hzp t) r
      rw [ih, hr] at hcomp
      have hzeq : zp t * z = zp (t + 1) := by funext i; simp [zp, pow_succ]
      rw [twist_congr (hzp (t + 1)) (by rw [hzeq]; exact hzp (t + 1)) (π ^ m) hzeq.symm, ← hcomp]
  have htwφ : ∀ (t : ℕ) (a : UVCrossingModel W (π ^ (m * n))),
      twist (zp t) (hzp t) (π ^ m) (φ a) = φ a := fun t a =>
    twist_modelMap (zp t) (hzp t) n hn.ne' (hzpn t) π m h1 a

  obtain ⟨g, hg⟩ := exists_eq_sum_modelMap_mul n hn.ne' 1 h1 π m 1 (fun i => by simp) r
  let M : ℕ → ℕ → UVCrossingModel W (π ^ m) := fun i j => U (π ^ m) ^ i * V (π ^ m) ^ j
  let cc : ℕ → ℕ → W := fun i j => z 0 ^ i * z 1 ^ j
  have htwmon : ∀ (t i j : ℕ), twist (zp t) (hzp t) (π ^ m) (M i j) = const (π ^ m) (cc i j ^ t) * M i j := by
    intro t i j
    show twist (zp t) (hzp t) (π ^ m) (U (π ^ m) ^ i * V (π ^ m) ^ j) =
      const (π ^ m) ((z 0 ^ i * z 1 ^ j) ^ t) * (U (π ^ m) ^ i * V (π ^ m) ^ j)
    rw [map_mul, map_pow, map_pow, twist_U, twist_V, mul_pow, mul_pow, const_pow, const_pow]
    show const _ ((z 0 ^ t) ^ i) * _ * (const _ ((z 1 ^ t) ^ j) * _) = _
    rw [show ((z 0 ^ i * z 1 ^ j) ^ t) = (z 0 ^ t) ^ i * ((z 1 ^ t) ^ j) by ring, ← const_mul]
    ring
  have hroots : ∀ i j : ℕ, i < n → j < n →
      ∑ t ∈ Finset.range n, cc i j ^ t = if i = j then (n : W) else 0 := by
    intro i j hi hj
    show ∑ t ∈ Finset.range n, (z 0 ^ i * z 1 ^ j) ^ t = _
    split_ifs with hij
    · subst hij
      rw [← mul_pow, hz, one_pow]
      simp
    · apply sum_pow_eq_of_pow_eq_one n
      · rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i n, mul_comm j n, pow_mul, pow_mul,
          hz0n, hz1n, one_pow, one_pow, one_mul]
      · intro h
        apply hij
        have hz1 : z 1 * z 0 = 1 := by rw [mul_comm]; exact hz
        have : ζ ^ i = ζ ^ j := by
          have h' := congrArg (· * z 0 ^ j) h
          simp only [one_mul] at h'
          rw [mul_assoc, ← mul_pow, hz1, one_pow, mul_one, hz0] at h'
          exact h'
        exact hζ.pow_inj hi hj this

  have havg : ∑ t ∈ Finset.range n, twist (zp t) (hzp t) (π ^ m) r =
      const (π ^ m) n * φ (∑ i ∈ Finset.range n, g i i * const (π ^ (m * n)) ((π ^ m) ^ i)) := by
    calc ∑ t ∈ Finset.range n, twist (zp t) (hzp t) (π ^ m) r
        = ∑ t ∈ Finset.range n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            φ (g i j) * (const (π ^ m) (cc i j ^ t) * M i j) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hg, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, htwφ, htwmon]
      _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            φ (g i j) * (const (π ^ m) (∑ t ∈ Finset.range n, cc i j ^ t) * M i j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, const_sum, Finset.sum_mul]
      _ = ∑ i ∈ Finset.range n, φ (g i i) * (const (π ^ m) n * M i i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.sum_eq_single_of_mem i hi]
          · rw [hroots i i (Finset.mem_range.mp hi) (Finset.mem_range.mp hi), if_pos rfl]
          · intro j hj hji
            rw [hroots i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj), if_neg (Ne.symm hji),
              const_zero, zero_mul, mul_zero]
      _ = const (π ^ m) n * φ (∑ i ∈ Finset.range n, g i i * const (π ^ (m * n)) ((π ^ m) ^ i)) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, modelMap_const]
          show φ (g i i) * (const (π ^ m) n * (U (π ^ m) ^ i * V (π ^ m) ^ i)) = _
          rw [← mul_pow, U_mul_V_eq_const, const_pow]
          ring
  have hsum1 : ∑ t ∈ Finset.range n, twist (zp t) (hzp t) (π ^ m) r = const (π ^ m) n * r := by
    simp only [hiter, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← map_natCast (constHom (π ^ m)) n]; rfl
  rw [hsum1] at havg
  have hunit : IsUnit (const (π ^ m) (n : W)) := hnW.map (constHom (π ^ m))
  exact ⟨_, (hunit.mul_left_cancel havg).symm⟩

end Invariants

end KummerClass44

namespace KummerClass44

open KummerNorm44

section PrincipalUnits

variable {W : Type*} [CommRing W] [IsLocalRing W]

theorem constantCoeff_rescale (z : Fin 2 → W) (f : MvPowerSeries (Fin 2) W) :
    MvPowerSeries.constantCoeff (MvPowerSeries.rescale z f) = MvPowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_rescale,
    Finsupp.prod_zero_index, one_mul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem resHom_twist (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (z : Fin 2 → W) (hz : z 0 * z 1 = 1)
    (x : UVCrossingModel W c) : resHom c hc (twist z hz c x) = resHom c hc x := by
  obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective c x
  rw [twist_mk, resHom_mk, resHom_mk, constantCoeff_rescale]

variable (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) [IsLocalRing (UVCrossingModel W c)]

def PU (x : UVCrossingModel W c) : Prop := resHom c hc x = 1

omit [IsLocalRing (UVCrossingModel W c)] in
theorem PU.mul {x y : UVCrossingModel W c} (hx : PU c hc x) (hy : PU c hc y) : PU c hc (x * y) := by
  unfold PU at *; rw [map_mul, hx, hy, one_mul]

omit [IsLocalRing (UVCrossingModel W c)] in
theorem PU.one : PU c hc (1 : UVCrossingModel W c) := by unfold PU; rw [map_one]

omit [IsLocalRing (UVCrossingModel W c)] in
theorem PU.pow {x : UVCrossingModel W c} (hx : PU c hc x) (k : ℕ) : PU c hc (x ^ k) := by
  unfold PU at *; rw [map_pow, hx, one_pow]

omit [IsLocalRing (UVCrossingModel W c)] in
theorem PU.twist {x : UVCrossingModel W c} (hx : PU c hc x) (z : Fin 2 → W) (hz : z 0 * z 1 = 1) :
    PU c hc (KummerClass44.twist z hz c x) := by
  unfold PU at *; rw [resHom_twist, hx]

omit [IsLocalRing (UVCrossingModel W c)] in
theorem PU.prod {ι : Type*} (s : Finset ι) (f : ι → UVCrossingModel W c) (h : ∀ i ∈ s, PU c hc (f i)) :
    PU c hc (∏ i ∈ s, f i) := by
  unfold PU at *; rw [map_prod]; exact Finset.prod_eq_one h

theorem PU.isUnit {x : UVCrossingModel W c} (hx : PU c hc x) : IsUnit x := by
  rw [isUnit_iff_resHom c hc, hx]; exact one_ne_zero

theorem PU.val_inv {x : UVCrossingModel W c} (hx : PU c hc x) (u : (UVCrossingModel W c)ˣ) (hu : (u : UVCrossingModel W c) = x) :
    PU c hc (↑u⁻¹ : UVCrossingModel W c) := by
  unfold PU at *
  have := congrArg (resHom c hc) u.mul_inv
  rw [map_mul, map_one, hu, hx, one_mul] at this
  exact this

theorem PU.sub_one_mem {x : UVCrossingModel W c} (hx : PU c hc x) :
    x - 1 ∈ IsLocalRing.maximalIdeal (UVCrossingModel W c) := by
  rw [mem_maximalIdeal_iff_resHom c hc, map_sub, map_one, hx, sub_self]

theorem PU.of_sub_one_mem {x : UVCrossingModel W c}
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal (UVCrossingModel W c)) : PU c hc x := by
  rw [mem_maximalIdeal_iff_resHom c hc, map_sub, map_one, sub_eq_zero] at hx; exact hx

theorem PU.pow_injective (n : ℕ) (hnW : IsUnit (n : W)) {x y : UVCrossingModel W c}
    (hx : PU c hc x) (hy : PU c hc y) (h : x ^ n = y ^ n) : x = y := by
  obtain ⟨u, hu⟩ := PU.isUnit c hc hy

  have hηPU : PU c hc (x * ↑u⁻¹) := PU.mul c hc hx (PU.val_inv c hc hy u hu)
  have hηn : (x * ↑u⁻¹) ^ n = 1 := by
    rw [mul_pow, h, ← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      inv_pow, mul_inv_cancel, Units.val_one]
  have hgeom := geom_sum_mul (x * ↑u⁻¹) n
  rw [hηn, sub_self] at hgeom
  have hres1 : ∀ i, resHom c hc ((x * ↑u⁻¹) ^ i) = 1 := by
    intro i; rw [map_pow]; unfold PU at hηPU; rw [hηPU, one_pow]
  have hS : IsUnit (∑ i ∈ Finset.range n, (x * ↑u⁻¹) ^ i) := by
    rw [isUnit_iff_resHom c hc, map_sum]
    simp only [hres1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← map_natCast (IsLocalRing.residue W)]
    exact (hnW.map (IsLocalRing.residue W)).ne_zero
  have hη1 : x * ↑u⁻¹ = 1 := by
    have := hS.mul_right_eq_zero.mp hgeom
    rwa [sub_eq_zero] at this
  calc x = x * ↑u⁻¹ * ↑u := by rw [mul_assoc, Units.inv_mul, mul_one]
    _ = y := by rw [hη1, one_mul, hu]

theorem PU.exists_pow_eq [HenselianRing (UVCrossingModel W c) (IsLocalRing.maximalIdeal (UVCrossingModel W c))]
    (n : ℕ) (hnW : IsUnit (n : W)) {a : UVCrossingModel W c} (ha : PU c hc a) :
    ∃ w : UVCrossingModel W c, PU c hc w ∧ w ^ n = a := by
  have hn : IsUnit ((n : ℕ) : UVCrossingModel W c) := by
    have := hnW.map (constHom c); rwa [map_natCast] at this
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hnW
    exact not_isUnit_zero hnW
  obtain ⟨w, hw, hw1⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (UVCrossingModel W c))
    (Polynomial.X ^ n - Polynomial.C a) (Polynomial.monic_X_pow_sub_C a hn0) 1
    (by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, one_pow, Polynomial.eval_C]
      rw [← Ideal.neg_mem_iff, neg_sub]; exact PU.sub_one_mem c hc ha)
    (by
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        sub_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        one_pow, mul_one]
      exact hn.map _)
  refine ⟨w, PU.of_sub_one_mem c hc hw1, ?_⟩
  have := hw
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at this
  exact this

variable [HenselianRing (UVCrossingModel W c) (IsLocalRing.maximalIdeal (UVCrossingModel W c))]
variable (n : ℕ) (hnW : IsUnit (n : W))

open Classical in

noncomputable def rt (x : UVCrossingModel W c) : UVCrossingModel W c :=
  if h : PU c hc x then Classical.choose (PU.exists_pow_eq c hc n hnW h) else 1

theorem rt_spec {x : UVCrossingModel W c} (hx : PU c hc x) :
    PU c hc (rt c hc n hnW x) ∧ (rt c hc n hnW x) ^ n = x := by
  classical
  unfold rt; rw [dif_pos hx]; exact Classical.choose_spec (PU.exists_pow_eq c hc n hnW hx)

theorem rt_eq_of_pow_eq {x w : UVCrossingModel W c} (hx : PU c hc x) (hw : PU c hc w) (h : w ^ n = x) :
    rt c hc n hnW x = w :=
  PU.pow_injective c hc n hnW (rt_spec c hc n hnW hx).1 hw ((rt_spec c hc n hnW hx).2.trans h.symm)

theorem rt_mul {x y : UVCrossingModel W c} (hx : PU c hc x) (hy : PU c hc y) :
    rt c hc n hnW (x * y) = rt c hc n hnW x * rt c hc n hnW y :=
  rt_eq_of_pow_eq c hc n hnW (PU.mul c hc hx hy) (PU.mul c hc (rt_spec c hc n hnW hx).1 (rt_spec c hc n hnW hy).1)
    (by rw [mul_pow, (rt_spec c hc n hnW hx).2, (rt_spec c hc n hnW hy).2])

theorem rt_twist {x : UVCrossingModel W c} (hx : PU c hc x) (z : Fin 2 → W) (hz : z 0 * z 1 = 1) :
    rt c hc n hnW (KummerClass44.twist z hz c x) = KummerClass44.twist z hz c (rt c hc n hnW x) :=
  rt_eq_of_pow_eq c hc n hnW (PU.twist c hc hx z hz) (PU.twist c hc (rt_spec c hc n hnW hx).1 z hz)
    (by rw [← map_pow, (rt_spec c hc n hnW hx).2])

theorem rt_pow_self {x : UVCrossingModel W c} (hx : PU c hc x) : rt c hc n hnW (x ^ n) = x :=
  rt_eq_of_pow_eq c hc n hnW (PU.pow c hc hx n) hx rfl

end PrincipalUnits

end KummerClass44

namespace KummerClass44

open KummerNorm44

section Cochain

variable {W : Type*} [CommRing W]
variable (c : W) (z : Fin 2 → W)

theorem hzp_of (hz : z 0 * z 1 = 1) (t : ℕ) : (z ^ t) 0 * (z ^ t) 1 = 1 := by
  show z 0 ^ t * z 1 ^ t = 1; rw [← mul_pow, hz, one_pow]

noncomputable def orb (hz : z 0 * z 1 = 1) (x : UVCrossingModel W c) (t : ℕ) : UVCrossingModel W c :=
  twist (z ^ t) (hzp_of z hz t) c x

theorem orb_zero (hz : z 0 * z 1 = 1) (x : UVCrossingModel W c) : orb c z hz x 0 = x := by
  obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective c x
  unfold orb; rw [twist_mk]
  simp only [pow_zero, MvPowerSeries.rescale_one, RingHom.id_apply]

theorem twist_orb (hz : z 0 * z 1 = 1) (x : UVCrossingModel W c) (t : ℕ) :
    twist z hz c (orb c z hz x t) = orb c z hz x (t + 1) := by
  unfold orb
  rw [twist_comp z hz c (z ^ t) (hzp_of z hz t) x]
  exact congrFun (congrArg DFunLike.coe (twist_congr _ (hzp_of z hz (t + 1)) c (pow_succ z t).symm)) x

theorem exists_twist_eq_mul_of_prod_orb_eq_one [IsLocalRing W]
    (hc : c ∈ IsLocalRing.maximalIdeal W) [IsLocalRing (UVCrossingModel W c)]
    [HenselianRing (UVCrossingModel W c) (IsLocalRing.maximalIdeal (UVCrossingModel W c))]
    (n : ℕ) (hnW : IsUnit (n : W))
    (hz : z 0 * z 1 = 1) (hn : 0 < n) (c₁ : UVCrossingModel W c) (h₁ : PU c hc c₁)
    (hN : ∏ t ∈ Finset.range n, orb c z hz c₁ t = 1) :
    ∃ e : UVCrossingModel W c, PU c hc e ∧ twist z hz c e = c₁ * e := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  set a := orb c z hz c₁ with ha
  have haPU : ∀ t, PU c hc (a t) := fun t => PU.twist c hc h₁ _ _
  have ha0 : a 0 = c₁ := orb_zero c z hz c₁
  have hσa : ∀ t, twist z hz c (a t) = a (t + 1) := twist_orb c z hz c₁

  set Q := ∏ i ∈ Finset.range (k + 1), a i ^ (k - i) with hQ
  have hQPU : PU c hc Q := PU.prod c hc _ _ fun i _ => PU.pow c hc (haPU i) _

  have hprod1 : (∏ i ∈ Finset.range k, a (i + 1)) * a 0 = 1 := by
    rw [← Finset.prod_range_succ' (fun i => a i) k]; exact hN
  have hkey : twist z hz c Q * c₁ ^ (k + 1) = Q := by
    have hσQ : twist z hz c Q = ∏ i ∈ Finset.range (k + 1), a (i + 1) ^ (k - i) := by
      rw [hQ, map_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [map_pow, hσa]
    rw [hσQ, Finset.prod_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hsplit : ∏ i ∈ Finset.range k, a (i + 1) ^ (k - i) =
        (∏ i ∈ Finset.range k, a (i + 1) ^ (k - 1 - i)) * ∏ i ∈ Finset.range k, a (i + 1) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [← pow_succ]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [hsplit, hQ, Finset.prod_range_succ' (fun i => a i ^ (k - i)) k]
    simp only [Nat.sub_zero]
    have hrw : ∀ i ∈ Finset.range k, a (i + 1) ^ (k - (i + 1)) = a (i + 1) ^ (k - 1 - i) := by
      intro i hi; congr 1; omega
    rw [Finset.prod_congr rfl hrw, ← ha0, pow_succ]
    simp only [mul_assoc]
    congr 1
    rw [mul_left_comm, hprod1, mul_one]

  have hσQPU : PU c hc (twist z hz c Q) := PU.twist c hc hQPU z hz
  have hroot := congrArg (rt c hc (k + 1) hnW) hkey
  rw [rt_mul c hc (k + 1) hnW hσQPU (PU.pow c hc h₁ _), rt_pow_self c hc (k + 1) hnW h₁,
    rt_twist c hc (k + 1) hnW hQPU z hz] at hroot

  obtain ⟨hrPU, -⟩ := rt_spec c hc (k + 1) hnW hQPU
  obtain ⟨u, hu⟩ := PU.isUnit c hc hrPU
  refine ⟨↑u⁻¹, PU.val_inv c hc hrPU u hu, ?_⟩

  have htw : twist z hz c (u : UVCrossingModel W c) * c₁ = u := by rw [hu]; exact hroot
  have hinv : twist z hz c (↑u⁻¹ : UVCrossingModel W c) * twist z hz c (u : UVCrossingModel W c) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc twist z hz c (↑u⁻¹ : UVCrossingModel W c)
      = twist z hz c ↑u⁻¹ * (twist z hz c ↑u * c₁) * ↑u⁻¹ := by rw [htw, mul_assoc, Units.mul_inv, mul_one]
    _ = (twist z hz c ↑u⁻¹ * twist z hz c ↑u) * c₁ * ↑u⁻¹ := by simp only [mul_assoc]
    _ = c₁ * ↑u⁻¹ := by rw [hinv, one_mul]

theorem exists_mul_eq_const_pow_mul_twist [IsLocalRing W] [IsDomain W]
    (hc : c ∈ IsLocalRing.maximalIdeal W) [IsLocalRing (UVCrossingModel W c)]
    [HenselianRing (UVCrossingModel W c) (IsLocalRing.maximalIdeal (UVCrossingModel W c))]
    (n : ℕ) (hnW : IsUnit (n : W))
    (hz : z 0 * z 1 = 1) (hn : 0 < n) (hζ : IsPrimitiveRoot (z 0) n)
    (cu : UVCrossingModel W c) (hcu : IsUnit cu)
    (hN : ∏ t ∈ Finset.range n, orb c z hz cu t = 1) :
    ∃ (j : ℕ) (e : UVCrossingModel W c), IsUnit e ∧ cu * e = const c (z 0 ^ j) * twist z hz c e := by
  classical

  set ρ := resHom c hc with hρ
  have hζbar : IsPrimitiveRoot (IsLocalRing.residue W (z 0)) n := by
    rw [IsPrimitiveRoot.iff hn]
    refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl hln => ?_⟩
    rw [← map_pow, Ne, ← sub_eq_zero, ← map_one (IsLocalRing.residue W), ← map_sub,
      IsLocalRing.residue_eq_zero_iff]

    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
    have hprod := hζ.prod_one_sub_pow_eq_order
    have hdvd : (1 - z 0 ^ l) ∣ ((k + 1 : ℕ) : W) := by
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, (Nat.succ_pred_eq_of_pos hl).symm⟩
      rw [Nat.cast_succ, ← hprod]
      exact Finset.dvd_prod_of_mem (fun i => 1 - z 0 ^ (i + 1)) (Finset.mem_range.mpr (by omega))
    have hu : IsUnit (1 - z 0 ^ l) := isUnit_of_dvd_unit hdvd hnW
    have hu' : IsUnit (z 0 ^ l - 1) := by rw [← neg_sub]; exact hu.neg
    intro hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu'

  have hρtw : ∀ (t : ℕ) (x : UVCrossingModel W c), ρ (orb c z hz x t) = ρ x := fun t x =>
    resHom_twist c hc _ _ x
  have hρcu : ρ cu ^ n = 1 := by
    have := congrArg ρ hN
    rw [map_prod, map_one] at this
    rw [← this, Finset.prod_congr rfl (fun t _ => hρtw t cu), Finset.prod_const, Finset.card_range]
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, -, hj⟩ := hζbar.eq_pow_of_pow_eq_one hρcu

  have hz0n : z 0 ^ n = 1 := hζ.pow_eq_one
  have hz1n : z 1 ^ n = 1 := by
    have h := congrArg (· ^ n) hz
    simp only [mul_pow, one_pow] at h
    rwa [hz0n, one_mul] at h

  set c₁ := cu * const c (z 1) ^ j with hc₁
  have h₁ : PU c hc c₁ := by
    show ρ c₁ = 1
    rw [hc₁, map_mul, map_pow, ← hj, resHom_const, ← mul_pow, ← map_mul, hz, map_one, one_pow]
  have horb : ∀ t, orb c z hz c₁ t = orb c z hz cu t * const c (z 1) ^ j := by
    intro t
    show twist _ _ c (cu * const c (z 1) ^ j) = twist _ _ c cu * _
    rw [map_mul, map_pow, twist_const]
  have hN₁ : ∏ t ∈ Finset.range n, orb c z hz c₁ t = 1 := by
    rw [Finset.prod_congr rfl (fun t _ => horb t), Finset.prod_mul_distrib, hN, one_mul,
      Finset.prod_const, Finset.card_range, ← pow_mul, const_pow, mul_comm j n, pow_mul, hz1n, one_pow]
    exact map_one (constHom c)
  obtain ⟨e, hePU, he⟩ := exists_twist_eq_mul_of_prod_orb_eq_one c z hc n hnW hz hn c₁ h₁ hN₁
  refine ⟨j, e, PU.isUnit c hc hePU, ?_⟩
  rw [he, hc₁]
  have : const c (z 0 ^ j) * (const c (z 1) ^ j) = 1 := by
    rw [const_pow, const_mul, ← mul_pow, hz, one_pow]; exact map_one (constHom c)
  linear_combination (-(cu * e)) * this

end Cochain

end KummerClass44

namespace KummerClass44

open KummerNorm44

section SigmaK

variable {W : Type*} [CommRing W] [IsDomain W] [IsLocalRing W]

theorem twist_swap_comp (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (c : W) (x : UVCrossingModel W c) :
    twist (![z 1, z 0]) (by show z 1 * z 0 = 1; rw [mul_comm]; exact hz) c (twist z hz c x) = x := by
  rw [twist_comp]
  have h1 : z * ![z 1, z 0] = 1 := by
    funext i; fin_cases i
    · show z 0 * z 1 = 1; exact hz
    · show z 1 * z 0 = 1; rw [mul_comm]; exact hz
  rw [twist_congr _ (by show (1 : Fin 2 → W) 0 * (1 : Fin 2 → W) 1 = 1; simp) c h1]
  exact twist_one c _ x

theorem twist_comp_swap (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (c : W) (x : UVCrossingModel W c) :
    twist z hz c (twist (![z 1, z 0]) (by show z 1 * z 0 = 1; rw [mul_comm]; exact hz) c x) = x := by
  have := twist_swap_comp (![z 1, z 0]) (by show z 1 * z 0 = 1; rw [mul_comm]; exact hz) c x
  have hzz : (![(![z 1, z 0] : Fin 2 → W) 1, (![z 1, z 0] : Fin 2 → W) 0] : Fin 2 → W) = z := by
    funext i; fin_cases i <;> rfl
  rw [twist_congr _ hz c hzz] at this
  exact this

noncomputable def twistEquiv (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (c : W) :
    UVCrossingModel W c ≃+* UVCrossingModel W c :=
  RingEquiv.ofRingHom (twist z hz c) (twist (![z 1, z 0]) (by show z 1 * z 0 = 1; rw [mul_comm]; exact hz) c)
    (by ext x; exact twist_comp_swap z hz c x) (by ext x; exact twist_swap_comp z hz c x)

theorem twistEquiv_apply (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (c : W) (x : UVCrossingModel W c) :
    twistEquiv z hz c x = twist z hz c x := rfl

variable (c : W) (z : Fin 2 → W) (hz : z 0 * z 1 = 1)
variable [IsDomain (UVCrossingModel W c)]

noncomputable def sigmaK : FractionRing (UVCrossingModel W c) ≃+* FractionRing (UVCrossingModel W c) :=
  IsFractionRing.ringEquivOfRingEquiv (K := FractionRing (UVCrossingModel W c))
    (L := FractionRing (UVCrossingModel W c)) (twistEquiv z hz c)

theorem sigmaK_algebraMap (r : UVCrossingModel W c) :
    sigmaK c z hz (algebraMap _ (FractionRing (UVCrossingModel W c)) r) =
      algebraMap _ (FractionRing (UVCrossingModel W c)) (twist z hz c r) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (twistEquiv z hz c) r

theorem sigmaK_iterate_algebraMap (t : ℕ) (r : UVCrossingModel W c) :
    (sigmaK c z hz)^[t] (algebraMap _ (FractionRing (UVCrossingModel W c)) r) =
      algebraMap _ (FractionRing (UVCrossingModel W c)) (orb c z hz r t) := by
  induction t with
  | zero => rw [Function.iterate_zero, id, orb_zero]
  | succ t ih => rw [Function.iterate_succ_apply', ih, sigmaK_algebraMap, twist_orb]

theorem sigmaK_iterate_eq_self (n : ℕ) (hzn : z ^ n = 1) (k : FractionRing (UVCrossingModel W c)) :
    (sigmaK c z hz)^[n] k = k := by
  have horbn : ∀ r : UVCrossingModel W c, orb c z hz r n = r := by
    intro r
    obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective c r
    unfold orb; rw [twist_mk]
    congr 1
    rw [hzn, MvPowerSeries.rescale_one]; rfl
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := UVCrossingModel W c) k
  have hiter : ∀ (t : ℕ) (x y : FractionRing (UVCrossingModel W c)),
      (sigmaK c z hz)^[t] (x / y) = (sigmaK c z hz)^[t] x / (sigmaK c z hz)^[t] y := by
    intro t; induction t with
    | zero => intro x y; rfl
    | succ t ih => intro x y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_div₀]
  rw [hiter, sigmaK_iterate_algebraMap, sigmaK_iterate_algebraMap, horbn, horbn]

theorem sigmaK_iterate_mul (t : ℕ) (x y : FractionRing (UVCrossingModel W c)) :
    (sigmaK c z hz)^[t] (x * y) = (sigmaK c z hz)^[t] x * (sigmaK c z hz)^[t] y := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem sigmaK_iterate_div (t : ℕ) (x y : FractionRing (UVCrossingModel W c)) :
    (sigmaK c z hz)^[t] (x / y) = (sigmaK c z hz)^[t] x / (sigmaK c z hz)^[t] y := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_div₀]

omit [IsDomain W] [IsLocalRing W] [IsDomain (UVCrossingModel W c)] in
theorem prod_range_div_telescope {F : Type*} [Field F] (G : ℕ → F) (hG : ∀ t, G t ≠ 0) (N : ℕ) :
    ∏ t ∈ Finset.range N, G (t + 1) / G t = G N / G 0 := by
  induction N with
  | zero => rw [Finset.prod_range_zero, div_self (hG 0)]
  | succ N ih => rw [Finset.prod_range_succ, ih, div_mul_div_comm, mul_comm (G N) (G (N + 1)),
      mul_div_mul_right _ _ (hG N)]

theorem exists_div_eq_of_sigmaK_eq (n : ℕ) (hn : 0 < n) (hzn : z ^ n = 1)
    (k : FractionRing (UVCrossingModel W c)) (hk : sigmaK c z hz k = k) :
    ∃ (a b : UVCrossingModel W c), b ≠ 0 ∧ twist z hz c a = a ∧ twist z hz c b = b ∧
      k = algebraMap _ (FractionRing (UVCrossingModel W c)) a / algebraMap _ _ b := by
  classical
  obtain ⟨a₀, b₀, hb₀, rfl⟩ := IsFractionRing.div_surjective (A := UVCrossingModel W c) k
  have hb₀0 : b₀ ≠ 0 := nonZeroDivisors.ne_zero hb₀

  obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  let Nb : UVCrossingModel W c := ∏ t ∈ Finset.range (k' + 1), orb c z hz b₀ t
  let b' : UVCrossingModel W c := ∏ t ∈ Finset.range k', orb c z hz b₀ (t + 1)
  have hNb : Nb = b' * b₀ := by
    show ∏ t ∈ Finset.range (k' + 1), orb c z hz b₀ t = _
    rw [Finset.prod_range_succ' (fun t => orb c z hz b₀ t), orb_zero]
  have horbn : ∀ r : UVCrossingModel W c, orb c z hz r (k' + 1) = r := by
    intro r
    obtain ⟨f, rfl⟩ := UVCrossingModel.mk_surjective c r
    unfold orb; rw [twist_mk]
    congr 1
    rw [hzn, MvPowerSeries.rescale_one]; rfl
  have hNbfix : twist z hz c Nb = Nb := by
    show twist z hz c (∏ t ∈ Finset.range (k' + 1), orb c z hz b₀ t) = _
    rw [map_prod, Finset.prod_congr rfl (fun t _ => twist_orb c z hz b₀ t),
      Finset.prod_range_succ (fun t => orb c z hz b₀ (t + 1)), horbn]
    exact hNb.symm
  have hNb0 : Nb ≠ 0 := by
    show ∏ t ∈ Finset.range (k' + 1), orb c z hz b₀ t ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro t _ h0
    apply hb₀0
    have := twist_swap_comp (z ^ t) (hzp_of z hz t) c b₀
    unfold orb at h0
    rw [h0, map_zero] at this
    exact this.symm
  have hb'0 : algebraMap _ (FractionRing (UVCrossingModel W c)) b₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb₀0
  have hNbK0 : algebraMap _ (FractionRing (UVCrossingModel W c)) Nb ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hNb0
  have hk' : algebraMap _ (FractionRing (UVCrossingModel W c)) a₀ / algebraMap _ _ b₀ =
      algebraMap _ _ (a₀ * b') / algebraMap _ _ Nb := by
    rw [div_eq_div_iff hb'0 hNbK0, hNb, map_mul, map_mul]; ring
  refine ⟨a₀ * b', Nb, hNb0, ?_, hNbfix, hk'⟩

  rw [hk'] at hk
  rw [map_div₀, sigmaK_algebraMap, sigmaK_algebraMap, hNbfix, div_left_inj' hNbK0] at hk
  exact IsFractionRing.injective _ _ hk

end SigmaK

end KummerClass44

namespace KummerClass44

open KummerNorm44

section Descent

variable {W : Type*} [CommRing W] [IsDomain W] [IsLocalRing W]

theorem descent_cocycle (π : W) (m n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (h1 : (1 : Fin 2 → W) 0 * (1 : Fin 2 → W) 1 = 1)
    (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (hζ : IsPrimitiveRoot (z 0) n)
    (hπm : π ^ m ∈ IsLocalRing.maximalIdeal W) (hπm0 : π ^ m ≠ 0) (hπmn0 : π ^ (m * n) ≠ 0)
    [IsDomain (UVCrossingModel W (π ^ m))] [IsLocalRing (UVCrossingModel W (π ^ m))]
    [IsIntegrallyClosed (UVCrossingModel W (π ^ m))]
    [HenselianRing (UVCrossingModel W (π ^ m)) (IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ m)))]
    [IsDomain (UVCrossingModel W (π ^ (m * n)))]
    (hφ : Function.Injective (modelMap n hn.ne' 1 h1 π m))
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (ι : K₀ →+* FractionRing (UVCrossingModel W (π ^ m)))
    (hιalg : ∀ r₀, ι (algebraMap _ K₀ r₀) =
      algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (modelMap n hn.ne' 1 h1 π m r₀))
    (f₀ : K₀) (hf₀ : f₀ ≠ 0)
    (u₁ : (UVCrossingModel W (π ^ m))ˣ) (g₁ : FractionRing (UVCrossingModel W (π ^ m)))
    (hfg : ι f₀ = algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (u₁ : UVCrossingModel W (π ^ m)) * g₁ ^ n) :
    ∃ cR : UVCrossingModel W (π ^ m), IsUnit cR ∧ g₁ ≠ 0 ∧
      algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) cR = sigmaK (π ^ m) z hz g₁ / g₁ ∧
      ∏ t ∈ Finset.range n, orb (π ^ m) z hz cR t = 1 := by
  classical

  have hz0n : z 0 ^ n = 1 := hζ.pow_eq_one
  have hz1n : z 1 ^ n = 1 := by
    have h := congrArg (· ^ n) hz
    simp only [mul_pow, one_pow] at h
    rwa [hz0n, one_mul] at h
  have hzn : z ^ n = 1 := by
    funext i; fin_cases i
    · exact hz0n
    · exact hz1n

  set φ := modelMap n hn.ne' 1 h1 π m with hφdef
  have hιinj : Function.Injective ι := ι.injective
  set σ := sigmaK (π ^ m) z hz with hσdef
  have hRK := IsFractionRing.injective (UVCrossingModel W (π ^ m)) (FractionRing (UVCrossingModel W (π ^ m)))
  have hσalg : ∀ r, σ (algebraMap _ _ r) = algebraMap _ (FractionRing (UVCrossingModel W (π ^ m)))
      (twist z hz (π ^ m) r) := sigmaK_algebraMap (π ^ m) z hz
  have hσι : ∀ k₀, σ (ι k₀) = ι k₀ := by
    have hext : σ.toRingHom.comp ι = ι := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (UVCrossingModel W (π ^ (m * n))))
      ext r₀
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hιalg, hσalg, twist_modelMap z hz n hn.ne' hzn π m h1]
    intro k₀; exact RingHom.congr_fun hext k₀

  have hu₁K : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (u₁ : UVCrossingModel W (π ^ m)) ≠ 0 :=
    (map_ne_zero_iff _ hRK).mpr u₁.ne_zero
  have hg₁ : g₁ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', mul_zero, map_eq_zero_iff _ hιinj] at hfg
    exact hf₀ hfg
  let tu : (UVCrossingModel W (π ^ m))ˣ := Units.map (twist z hz (π ^ m)).toMonoidHom u₁
  have htu : (tu : UVCrossingModel W (π ^ m)) = twist z hz (π ^ m) u₁ := rfl
  have hσfg : ι f₀ = algebraMap _ _ (tu : UVCrossingModel W (π ^ m)) * σ g₁ ^ n := by
    rw [← hσι f₀]
    show σ (ι f₀) = _
    rw [hfg, map_mul, map_pow, hσalg, htu]
  have hcn : (σ g₁ / g₁) ^ n = algebraMap _ (FractionRing (UVCrossingModel W (π ^ m)))
      ((u₁ * tu⁻¹ : (UVCrossingModel W (π ^ m))ˣ) : UVCrossingModel W (π ^ m)) := by
    have htuK : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (tu : UVCrossingModel W (π ^ m)) ≠ 0 :=
      (map_ne_zero_iff _ hRK).mpr tu.ne_zero
    rw [div_pow, div_eq_iff (pow_ne_zero _ hg₁), Units.val_mul, map_mul]
    have hinv : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) ((tu⁻¹ : (UVCrossingModel W (π ^ m))ˣ) : UVCrossingModel W (π ^ m)) =
        (algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (tu : UVCrossingModel W (π ^ m)))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [hinv]
    field_simp

    linear_combination hfg - hσfg

  have hint : IsIntegral (UVCrossingModel W (π ^ m)) (σ g₁ / g₁) := by
    refine ⟨Polynomial.X ^ n - Polynomial.C ((u₁ * tu⁻¹ : (UVCrossingModel W (π ^ m))ˣ) : UVCrossingModel W (π ^ m)),
      Polynomial.monic_X_pow_sub_C _ hn.ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hcn, sub_self]
  obtain ⟨cR, hcR⟩ := (IsIntegrallyClosed.isIntegral_iff (K := FractionRing (UVCrossingModel W (π ^ m)))).mp hint
  have hcRn : cR ^ n = ((u₁ * tu⁻¹ : (UVCrossingModel W (π ^ m))ˣ) : UVCrossingModel W (π ^ m)) := by
    apply hRK; rw [map_pow, hcR, hcn]
  have hcRu : IsUnit cR := by
    have : IsUnit (cR ^ n) := by rw [hcRn]; exact Units.isUnit _
    exact (isUnit_pow_iff hn.ne').mp this
  have hcR0 : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) cR ≠ 0 := (map_ne_zero_iff _ hRK).mpr hcRu.ne_zero

  have hGne : ∀ t, σ^[t] g₁ ≠ 0 := by
    intro t; induction t with
    | zero => exact hg₁
    | succ t ih => rw [Function.iterate_succ_apply']; exact (map_ne_zero_iff _ σ.injective).mpr ih
  have hN : ∏ t ∈ Finset.range n, orb (π ^ m) z hz cR t = 1 := by
    apply hRK
    rw [map_prod, map_one]
    have hterm : ∀ t ∈ Finset.range n, algebraMap _ (FractionRing (UVCrossingModel W (π ^ m)))
        (orb (π ^ m) z hz cR t) = σ^[t + 1] g₁ / σ^[t] g₁ := by
      intro t _
      rw [← sigmaK_iterate_algebraMap (π ^ m) z hz t cR]
      erw [hcR]
      rw [sigmaK_iterate_div, Function.iterate_succ_apply]
    rw [Finset.prod_congr rfl hterm, prod_range_div_telescope (fun t => σ^[t] g₁) hGne n,
      sigmaK_iterate_eq_self (π ^ m) z hz n hzn, Function.iterate_zero, id, div_self hg₁]
  exact ⟨cR, hcRu, hg₁, hcR, hN⟩

theorem descent (π : W) (m n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (h1 : (1 : Fin 2 → W) 0 * (1 : Fin 2 → W) 1 = 1)
    (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (hζ : IsPrimitiveRoot (z 0) n)
    (hπm : π ^ m ∈ IsLocalRing.maximalIdeal W) (hπm0 : π ^ m ≠ 0) (hπmn0 : π ^ (m * n) ≠ 0)
    [IsDomain (UVCrossingModel W (π ^ m))] [IsLocalRing (UVCrossingModel W (π ^ m))]
    [IsIntegrallyClosed (UVCrossingModel W (π ^ m))]
    [HenselianRing (UVCrossingModel W (π ^ m)) (IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ m)))]
    [IsDomain (UVCrossingModel W (π ^ (m * n)))]
    (hφ : Function.Injective (modelMap n hn.ne' 1 h1 π m))
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (ι : K₀ →+* FractionRing (UVCrossingModel W (π ^ m)))
    (hιalg : ∀ r₀, ι (algebraMap _ K₀ r₀) =
      algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (modelMap n hn.ne' 1 h1 π m r₀))
    (f₀ : K₀) (hf₀ : f₀ ≠ 0)
    (u₁ : (UVCrossingModel W (π ^ m))ˣ) (g₁ : FractionRing (UVCrossingModel W (π ^ m)))
    (hfg : ι f₀ = algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (u₁ : UVCrossingModel W (π ^ m)) * g₁ ^ n) :
    ∃ (u₀ : (UVCrossingModel W (π ^ (m * n)))ˣ) (j : ℕ) (h : K₀),
      f₀ = algebraMap _ K₀ (u₀ : UVCrossingModel W (π ^ (m * n))) *
        algebraMap _ K₀ (U (π ^ (m * n))) ^ j * h ^ n := by
  classical

  have hz0n : z 0 ^ n = 1 := hζ.pow_eq_one
  have hz1n : z 1 ^ n = 1 := by
    have h := congrArg (· ^ n) hz
    simp only [mul_pow, one_pow] at h
    rwa [hz0n, one_mul] at h
  have hzn : z ^ n = 1 := by
    funext i; fin_cases i
    · exact hz0n
    · exact hz1n

  set φ := modelMap n hn.ne' 1 h1 π m with hφdef
  have hιinj : Function.Injective ι := ι.injective
  set σ := sigmaK (π ^ m) z hz with hσdef
  have hRK := IsFractionRing.injective (UVCrossingModel W (π ^ m)) (FractionRing (UVCrossingModel W (π ^ m)))
  have hσalg : ∀ r, σ (algebraMap _ _ r) = algebraMap _ (FractionRing (UVCrossingModel W (π ^ m)))
      (twist z hz (π ^ m) r) := sigmaK_algebraMap (π ^ m) z hz
  have hσι : ∀ k₀, σ (ι k₀) = ι k₀ := by
    have hext : σ.toRingHom.comp ι = ι := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (UVCrossingModel W (π ^ (m * n))))
      ext r₀
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hιalg, hσalg, twist_modelMap z hz n hn.ne' hzn π m h1]
    intro k₀; exact RingHom.congr_fun hext k₀
  obtain ⟨cR, hcRu, hg₁, hcR, hN⟩ := descent_cocycle π m n hn hnW h1 z hz hζ hπm hπm0 hπmn0 hφ K₀ ι hιalg f₀ hf₀ u₁ g₁ hfg
  have hcR0 : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) cR ≠ 0 := (map_ne_zero_iff _ hRK).mpr hcRu.ne_zero

  obtain ⟨j, e, heu, hce⟩ := exists_mul_eq_const_pow_mul_twist (π ^ m) z hπm n hnW hz hn hζ cR hcRu hN

  have he0 : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) e ≠ 0 := (map_ne_zero_iff _ hRK).mpr heu.ne_zero
  have hU0 : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (U (π ^ m)) ≠ 0 :=
    (map_ne_zero_iff _ hRK).mpr (nonZeroDivisors.ne_zero
      (ModularCurve.UVCrossingModel.U_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπm0)))
  set UK := algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (U (π ^ m)) with hUK
  set eK := algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) e with heK
  set hK := g₁ / (eK * UK ^ j) with hhK
  have hσU : σ UK = algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (const (π ^ m) (z 0)) * UK := by
    rw [hUK, hσalg, twist_U, map_mul]
  have hceK : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) cR * eK =
      algebraMap _ _ (const (π ^ m) (z 0)) ^ j * algebraMap _ _ (twist z hz (π ^ m) e) := by
    rw [heK, ← map_mul, hce, map_mul, ← const_pow, map_pow]
  have hσg : σ g₁ = algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) cR * g₁ := by
    rw [hcR, div_mul_cancel₀ _ hg₁]
  have hte0 : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (twist z hz (π ^ m) e) ≠ 0 := by
    rw [← hσalg]; exact (map_ne_zero_iff _ σ.injective).mpr he0
  have hcz0 : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (const (π ^ m) (z 0)) ≠ 0 := by
    apply (map_ne_zero_iff _ hRK).mpr
    intro h0
    have := congrArg (fun w => w ^ n) h0
    simp only [const_pow, hz0n, zero_pow hn.ne'] at this
    exact one_ne_zero ((map_one (constHom (π ^ m))).symm.trans this)
  have hfix : σ hK = hK := by
    rw [hhK, map_div₀, map_mul, map_pow, hσg, hσU,
      show σ eK = algebraMap _ _ (twist z hz (π ^ m) e) by rw [heK]; exact hσalg e, mul_pow,
      div_eq_div_iff (mul_ne_zero hte0 (mul_ne_zero (pow_ne_zero _ hcz0) (pow_ne_zero _ hU0)))
        (mul_ne_zero he0 (pow_ne_zero _ hU0))]
    linear_combination (g₁ * UK ^ j) * hceK
  obtain ⟨a, b, hb0, hafix, hbfix, hab⟩ := exists_div_eq_of_sigmaK_eq (π ^ m) z hz n hn hzn hK hfix
  obtain ⟨a₀, ha₀⟩ := mem_range_modelMap_of_twist_eq n hn hnW (z 0) hζ π m h1 z hz rfl a hafix
  obtain ⟨b₀, hb₀⟩ := mem_range_modelMap_of_twist_eq n hn hnW (z 0) hζ π m h1 z hz rfl b hbfix
  have hb₀0 : b₀ ≠ 0 := by rintro rfl; rw [map_zero] at hb₀; exact hb0 hb₀.symm
  set h : K₀ := algebraMap _ K₀ a₀ / algebraMap _ K₀ b₀ with hhdef
  have hιh : ι h = hK := by
    rw [hhdef, map_div₀, hιalg, hιalg]
    show algebraMap _ _ (φ a₀) / algebraMap _ _ (φ b₀) = hK
    rw [ha₀, hb₀, ← hab]
  have hg₁eq : g₁ = hK * (eK * UK ^ j) := by
    rw [hhK, div_mul_cancel₀ _ (mul_ne_zero he0 (pow_ne_zero _ hU0))]
  have hUn : UK ^ n = ι (algebraMap _ K₀ (U (π ^ (m * n)))) := by
    rw [hιalg]
    show UK ^ n = algebraMap _ _ (φ (U (π ^ (m * n))))
    rw [modelMap_U, Pi.one_apply, show const (π ^ m) (1 : W) = 1 from map_one (constHom (π ^ m)), one_mul,
      map_pow]

  obtain ⟨uR, huR⟩ : ∃ uR : (UVCrossingModel W (π ^ m))ˣ, (uR : UVCrossingModel W (π ^ m)) = u₁ * e ^ n :=
    ⟨u₁ * heu.unit ^ n, by rw [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]⟩
  have hmain : ι f₀ = algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (uR : UVCrossingModel W (π ^ m)) *
      ι (algebraMap _ K₀ (U (π ^ (m * n))) ^ j * h ^ n) := by
    rw [hfg, hg₁eq, huR, map_mul ι, map_pow, map_pow, ← hUn, hιh, map_mul, map_pow, ← heK]
    ring

  have hU₀0 : algebraMap _ K₀ (U (π ^ (m * n))) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero
      (ModularCurve.UVCrossingModel.U_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπmn0)))
  have hh0 : h ≠ 0 := by
    intro h0
    apply hg₁
    rw [hg₁eq, ← hιh, h0, map_zero, zero_mul]
  have hq0 : algebraMap _ K₀ (U (π ^ (m * n))) ^ j * h ^ n ≠ 0 := mul_ne_zero (pow_ne_zero _ hU₀0) (pow_ne_zero _ hh0)
  have huRK : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (uR : UVCrossingModel W (π ^ m)) =
      ι (f₀ / (algebraMap _ K₀ (U (π ^ (m * n))) ^ j * h ^ n)) := by
    rw [map_div₀, hmain, mul_div_assoc, div_self ((map_ne_zero_iff _ hιinj).mpr hq0), mul_one]
  have huRfix : twist z hz (π ^ m) (uR : UVCrossingModel W (π ^ m)) = uR := by
    apply hRK
    have := hσalg (uR : UVCrossingModel W (π ^ m))
    rw [huRK, hσι] at this
    rw [← this, huRK]
  have huRinvfix : twist z hz (π ^ m) ((uR⁻¹ : (UVCrossingModel W (π ^ m))ˣ) : UVCrossingModel W (π ^ m)) = ↑uR⁻¹ := by
    have hmul : twist z hz (π ^ m) ((uR⁻¹ : (UVCrossingModel W (π ^ m))ˣ) : UVCrossingModel W (π ^ m)) *
        (uR : UVCrossingModel W (π ^ m)) = 1 := by
      rw [← huRfix, ← map_mul, Units.inv_mul, map_one]
    calc twist z hz (π ^ m) ((uR⁻¹ : (UVCrossingModel W (π ^ m))ˣ) : UVCrossingModel W (π ^ m))
        = twist z hz (π ^ m) ↑uR⁻¹ * ((uR : UVCrossingModel W (π ^ m)) * ↑uR⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = ↑uR⁻¹ := by rw [← mul_assoc, hmul, one_mul]
  obtain ⟨u₀', hu₀'⟩ := mem_range_modelMap_of_twist_eq n hn hnW (z 0) hζ π m h1 z hz rfl _ huRfix
  obtain ⟨v₀, hv₀⟩ := mem_range_modelMap_of_twist_eq n hn hnW (z 0) hζ π m h1 z hz rfl _ huRinvfix
  have hunit : u₀' * v₀ = 1 := by
    apply hφ
    show φ (u₀' * v₀) = φ 1
    rw [map_mul, map_one]
    show modelMap n hn.ne' 1 h1 π m u₀' * modelMap n hn.ne' 1 h1 π m v₀ = 1
    rw [hu₀', hv₀, Units.mul_inv]
  refine ⟨Units.mkOfMulEqOne u₀' v₀ hunit, j, h, hιinj ?_⟩
  have hφu : algebraMap _ (FractionRing (UVCrossingModel W (π ^ m))) (φ u₀') =
      algebraMap _ _ (uR : UVCrossingModel W (π ^ m)) := congrArg _ hu₀'
  rw [Units.val_mkOfMulEqOne, hmain]
  simp only [map_mul ι, map_pow ι, hιalg]
  erw [hφu]
  ring

end Descent

end KummerClass44

namespace KummerClass44

section K1

variable {W : Type*} [CommRing W]

theorem dd_sub (d : ℕ) :
    (Finsupp.single (0 : Fin 2) (d + 1) + Finsupp.single 1 (d + 1) : Fin 2 →₀ ℕ) -
      (Finsupp.single 0 1 + Finsupp.single 1 1) = Finsupp.single 0 d + Finsupp.single 1 d := by
  ext k
  rw [Finsupp.tsub_apply]
  fin_cases k <;> simp

theorem dd_le (d : ℕ) :
    (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≤
      Finsupp.single 0 (d + 1) + Finsupp.single 1 (d + 1) := by
  rw [Finsupp.le_def]; intro k; fin_cases k <;> simp

theorem not_dd_le_zero :
    ¬ ((Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≤ 0) := by
  rw [Finsupp.le_def]; intro h; have := h 0; simp at this

theorem eq_zero_of_const_eq_zero [IsNoetherianRing W] [IsLocalRing W] (c : W)
    (hc : c ∈ IsLocalRing.maximalIdeal W) (w : W) (h' : const c w = 0) : w = 0 := by
  classical
  change UVCrossingModel.mk c (MvPowerSeries.C w) = 0 at h'
  have h : MvPowerSeries.C w ∈ uvCrossingIdeal W c := Ideal.Quotient.eq_zero_iff_mem.mp h'
  change _ ∈ Ideal.span _ at h
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨Q, hQ⟩ := h

  let e : ℕ → (Fin 2 →₀ ℕ) := fun d => Finsupp.single 0 d + Finsupp.single 1 d
  have hX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 =
      MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]
  have h0 : w = -(c * MvPowerSeries.coeff (e 0) Q) := by
    have := congrArg (MvPowerSeries.coeff (e 0)) hQ
    rw [sub_mul, map_sub, MvPowerSeries.coeff_C_mul, hX, MvPowerSeries.coeff_monomial_mul] at this
    simp only [e, Finsupp.single_zero, add_zero] at this
    rw [if_neg not_dd_le_zero, MvPowerSeries.coeff_C, if_pos rfl, zero_sub] at this
    simpa [e] using this
  have hstep : ∀ d, MvPowerSeries.coeff (e d) Q = c * MvPowerSeries.coeff (e (d + 1)) Q := by
    intro d
    have := congrArg (MvPowerSeries.coeff (e (d + 1))) hQ
    rw [sub_mul, map_sub, MvPowerSeries.coeff_C_mul, hX, MvPowerSeries.coeff_monomial_mul,
      if_pos (dd_le d), one_mul, dd_sub, MvPowerSeries.coeff_C, if_neg] at this
    · exact (sub_eq_zero.mp this.symm)
    · intro h; have := congrArg (fun f => f 0) h; simp [e] at this
  have hpow : ∀ d, MvPowerSeries.coeff (e 0) Q ∈ (Ideal.span {c}) ^ d := by
    intro d
    suffices ∀ d k, MvPowerSeries.coeff (e k) Q ∈ (Ideal.span {c}) ^ d • (⊤ : Ideal W) →
        MvPowerSeries.coeff (e 0) Q ∈ (Ideal.span {c}) ^ (d + k) by
      have := this 0 d (by simp)
      simpa using this
    intro d k
    induction k generalizing d with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro h
      have h' : MvPowerSeries.coeff (e k) Q ∈ (Ideal.span {c}) ^ (d + 1) • (⊤ : Ideal W) := by
        rw [hstep k, smul_eq_mul, Ideal.mul_top, pow_succ']
        rw [smul_eq_mul, Ideal.mul_top] at h
        exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self c) h
      have := ih (d + 1) h'
      rwa [show d + 1 + k = d + (k + 1) by omega] at this
  have hq0 : MvPowerSeries.coeff (e 0) Q = 0 := by
    have hmem : MvPowerSeries.coeff (e 0) Q ∈ ⨅ d : ℕ, (Ideal.span {c}) ^ d := Ideal.mem_iInf.mpr hpow
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ ?_, Ideal.mem_bot] at hmem
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal _).mp hc
  rw [h0, hq0, mul_zero, neg_zero]

theorem const_injective [IsNoetherianRing W] [IsLocalRing W] (c : W)
    (hc : c ∈ IsLocalRing.maximalIdeal W) : Function.Injective (const c : W → UVCrossingModel W c) := by
  intro w₁ w₂ h
  rw [← sub_eq_zero]
  apply eq_zero_of_const_eq_zero c hc
  rw [← constHom_apply, map_sub, constHom_apply, constHom_apply, sub_eq_zero]
  exact h

theorem exists_kummer_generator
    [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F))
    (hdeg : Module.finrank K₀ F = n)
    [IsDomain (UVCrossingModel W (π ^ (m * n)))] :
    ∃ (α : F) (f : K₀), f ≠ 0 ∧ α ^ n = algebraMap K₀ F f ∧ IntermediateField.adjoin K₀ {α} = ⊤ := by
  haveI := hcyc
  obtain ⟨ζ, hζ⟩ := hμ
  have hπmn : π ^ (m * n) ∈ IsLocalRing.maximalIdeal W :=
    Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit) _
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm.ne' hn.ne'))
  have hinj : Function.Injective
      ((algebraMap (UVCrossingModel W (π ^ (m * n))) K₀).comp (constHom (π ^ (m * n)))) :=
    (IsFractionRing.injective (UVCrossingModel W (π ^ (m * n))) K₀).comp
      (const_injective (π ^ (m * n)) hπmn)
  have hζK : IsPrimitiveRoot
      ((algebraMap (UVCrossingModel W (π ^ (m * n))) K₀) (const (π ^ (m * n)) ζ)) n :=
    hζ.map_of_injective hinj
  have hK : (primitiveRoots (Module.finrank K₀ F) K₀).Nonempty := by
    rw [hdeg]; exact ⟨_, (mem_primitiveRoots hn).mpr hζK⟩
  obtain ⟨α, ⟨f, hf⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic K₀ F hK
  rw [hdeg] at hf
  by_cases hf0 : f = 0
  · refine ⟨1, 1, one_ne_zero, by rw [one_pow, map_one], ?_⟩
    have hα0 : α = 0 := by
      have : α ^ n = 0 := by rw [← hf, hf0, map_zero]
      exact pow_eq_zero_iff (hn.ne') |>.mp this
    rw [hα0] at hα
    rw [eq_top_iff, ← hα]
    exact IntermediateField.adjoin_le_iff.mpr (by simp)
  · exact ⟨α, f, hf0, hf.symm, hα⟩

end K1

end KummerClass44

namespace KummerClass44

section K2

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

theorem exists_mul_eq_mul_pow_of_irreducible (q : Ideal A) [q.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    (π₀ : A) (hirr : Irreducible (algebraMap A (Localization.AtPrime q) π₀))
    (r : A) (hr : r ≠ 0) :
    ∃ (a : ℕ) (r' s' : A), r' ∉ q ∧ s' ∉ q ∧ r * s' = r' * π₀ ^ a := by
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have hr' : algebraMap A (Localization.AtPrime q) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr' hirr
  obtain ⟨⟨r', s'⟩, hrs⟩ := IsLocalization.mk'_surjective q.primeCompl (u : Localization.AtPrime q)
  dsimp only at hrs
  have hr'q : r' ∉ q := by
    have : IsUnit (IsLocalization.mk' (Localization.AtPrime q) r' s') := by rw [hrs]; exact u.isUnit
    exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime q) q r' s').mp this
  refine ⟨a, r', s', hr'q, s'.2, hinj ?_⟩
  rw [map_mul, map_mul, map_pow, hu, ← hrs]
  rw [← IsLocalization.mk'_spec (Localization.AtPrime q) r' s']
  ring

theorem exists_pow_mul_of_isUnramifiedAt_of_height_eq_one
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hunr : ∀ (Q : Ideal ↥(integralClosure A L)) [Q.IsPrime],
      (Q.comap (algebraMap A ↥(integralClosure A L))).height = 1 → Algebra.IsUnramifiedAt A Q)
    (n : ℕ) (α : L) (f : K) (hf : f ≠ 0) (hα : α ^ n = algebraMap K L f)
    (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    ∃ (g : K) (r s : A), r ∉ q ∧ s ∉ q ∧ f * algebraMap A K s = g ^ n * algebraMap A K r := by
  classical

  haveI : Module.Finite A ↥(integralClosure A L) := IsIntegralClosure.finite A K L _
  haveI : IsFractionRing ↥(integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L _
  haveI : Algebra.IsIntegral A ↥(integralClosure A L) := Algebra.IsIntegral.of_finite A _
  have hAB : Function.Injective (algebraMap A ↥(integralClosure A L)) := by
    intro x y h
    have := congrArg (fun b : ↥(integralClosure A L) => (b : L)) h
    have h2 : algebraMap A L x = algebraMap A L y := this
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K L] at h2
    exact IsFractionRing.injective A K ((algebraMap K L).injective h2)

  haveI hdvr : IsDiscreteValuationRing (Localization.AtPrime q) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one q hq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨π₀, sπ⟩, hπ₀⟩ := IsLocalization.mk'_surjective q.primeCompl ϖ
  dsimp only at hπ₀
  have hϖ' : Irreducible (algebraMap A (Localization.AtPrime q) π₀) := by
    have hassoc : Associated ϖ (algebraMap A (Localization.AtPrime q) π₀) := by
      refine ⟨((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q (sπ : A)).mpr sπ.2).unit, ?_⟩
      rw [IsUnit.unit_spec, ← hπ₀, IsLocalization.mk'_spec]
    exact hassoc.irreducible hϖ
  have hπ₀q : π₀ ∈ q := by
    by_contra h
    have : IsUnit (algebraMap A (Localization.AtPrime q) π₀) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q π₀).mpr h
    exact hϖ'.not_isUnit this
  have hπ₀0 : π₀ ≠ 0 := by
    rintro rfl; rw [map_zero] at hϖ'; exact hϖ'.ne_zero rfl
  have hmaxq : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap A (Localization.AtPrime q) π₀} := hϖ'.maximalIdeal_eq

  obtain ⟨Q, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := ↥(integralClosure A L)) q (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hAB]; exact bot_le)
  haveI := hQp
  haveI : Q.LiesOver q := ⟨hQ.symm⟩
  have hU : Algebra.IsUnramifiedAt A Q := hunr Q (by rw [hQ]; exact hq)
  letI := Localization.AtPrime.algebraOfLiesOver q Q
  obtain ⟨-, hmap⟩ := (Algebra.isUnramifiedAt_iff_map_eq A q Q).mp hU

  set BQ := Localization.AtPrime Q with hBQ
  have hmaxB : IsLocalRing.maximalIdeal BQ = Ideal.span {algebraMap A BQ π₀} := by
    rw [← hmap, IsScalarTower.algebraMap_eq A (Localization.AtPrime q) BQ, ← Ideal.map_map,
      Localization.AtPrime.map_eq_maximalIdeal, hmaxq, Ideal.map_span, Set.image_singleton,
      RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  have hABQ : Function.Injective (algebraMap A BQ) := by
    rw [IsScalarTower.algebraMap_eq A ↥(integralClosure A L) BQ]
    exact (IsLocalization.injective BQ Q.primeCompl_le_nonZeroDivisors).comp hAB
  have hϖB0 : algebraMap A BQ π₀ ≠ 0 := (map_ne_zero_iff _ hABQ).mpr hπ₀0
  have hirrB : Irreducible (algebraMap A BQ π₀) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hϖB0 hmaxB
  haveI : IsNoetherianRing ↥(integralClosure A L) := IsIntegralClosure.isNoetherianRing A K L _
  haveI : IsNoetherianRing BQ := IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : IsPrincipalIdealRing BQ :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain BQ).out 4 0).mp
      (⟨⟨algebraMap A BQ π₀, hmaxB⟩⟩ : (IsLocalRing.maximalIdeal BQ).IsPrincipal)
  haveI : IsDiscreteValuationRing BQ :=
    { not_a_field' := by
        rw [hmaxB, Ne, Ideal.span_singleton_eq_bot]; exact hϖB0 }

  obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := ↥(integralClosure A L)) α
  obtain ⟨r₁, r₂, hr₂, rfl⟩ := IsFractionRing.div_surjective (A := A) f
  have hr₂0 : r₂ ≠ 0 := nonZeroDivisors.ne_zero hr₂
  have hb₂0 : b₂ ≠ 0 := nonZeroDivisors.ne_zero hb₂
  have hr₁0 : r₁ ≠ 0 := by
    rintro rfl; apply hf; rw [map_zero, zero_div]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    subst hn0
    refine ⟨1, 1, 1, ?_, ?_, ?_⟩
    · exact fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).mpr h)
    · exact fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).mpr h)
    · rw [pow_zero] at hα ⊢
      have : algebraMap K L (algebraMap A K r₁ / algebraMap A K r₂) = 1 := hα.symm
      rw [map_eq_one_iff _ (algebraMap K L).injective] at this
      rw [this]
  have hb₁0 : b₁ ≠ 0 := by
    rintro rfl
    apply hf
    rw [map_zero, zero_div, zero_pow hnpos.ne'] at hα
    exact (map_eq_zero_iff _ (algebraMap K L).injective).mp hα.symm

  have hAL : ∀ r : A, algebraMap K L (algebraMap A K r) =
      algebraMap ↥(integralClosure A L) L (algebraMap A ↥(integralClosure A L) r) := by
    intro r; rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hb₂L : algebraMap ↥(integralClosure A L) L b₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ↥(integralClosure A L) L)).mpr hb₂0
  have hr₂L : algebraMap K L (algebraMap A K r₂) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap K L).injective, map_ne_zero_iff _ (IsFractionRing.injective A K)]
    exact hr₂0
  have hB : b₁ ^ n * algebraMap A ↥(integralClosure A L) r₂ = b₂ ^ n * algebraMap A _ r₁ := by
    apply IsFractionRing.injective ↥(integralClosure A L) L
    rw [map_mul, map_mul, map_pow, map_pow, ← hAL, ← hAL]
    rw [div_pow, map_div₀, div_eq_div_iff (pow_ne_zero _ hb₂L) hr₂L] at hα
    rw [hα, mul_comm]

  have hBBQ : Function.Injective (algebraMap ↥(integralClosure A L) BQ) :=
    IsLocalization.injective BQ Q.primeCompl_le_nonZeroDivisors
  have hc₁ : algebraMap ↥(integralClosure A L) BQ b₁ ≠ 0 := (map_ne_zero_iff _ hBBQ).mpr hb₁0
  have hc₂ : algebraMap ↥(integralClosure A L) BQ b₂ ≠ 0 := (map_ne_zero_iff _ hBBQ).mpr hb₂0
  obtain ⟨k₁, v₁, hv₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc₁ hirrB
  obtain ⟨k₂, v₂, hv₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc₂ hirrB
  obtain ⟨a₁, r₁', s₁', hr₁', hs₁', h₁⟩ := exists_mul_eq_mul_pow_of_irreducible q π₀ hϖ' r₁ hr₁0
  obtain ⟨a₂, r₂', s₂', hr₂', hs₂', h₂⟩ := exists_mul_eq_mul_pow_of_irreducible q π₀ hϖ' r₂ hr₂0

  have hunit : ∀ t : A, t ∉ q → IsUnit (algebraMap A BQ t) := by
    intro t ht
    rw [IsScalarTower.algebraMap_apply A ↥(integralClosure A L) BQ]
    apply (IsLocalization.AtPrime.isUnit_to_map_iff BQ Q _).mpr
    show algebraMap A ↥(integralClosure A L) t ∉ Q
    rw [← Ideal.mem_comap, hQ]; exact ht
  have hexp : n * k₁ + a₂ = n * k₂ + a₁ := by
    have hBQ' := congrArg (algebraMap ↥(integralClosure A L) BQ) hB
    rw [map_mul, map_mul, map_pow, map_pow, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, hv₁, hv₂] at hBQ'

    have h₁' := congrArg (algebraMap A BQ) h₁
    have h₂' := congrArg (algebraMap A BQ) h₂
    rw [map_mul, map_mul, map_pow] at h₁' h₂'
    have key : ((v₁ ^ n * (hunit r₂' hr₂').unit * (hunit s₁' hs₁').unit : BQˣ) : BQ) *
        algebraMap A BQ π₀ ^ (n * k₁ + a₂) =
        ((v₂ ^ n * (hunit r₁' hr₁').unit * (hunit s₂' hs₂').unit : BQˣ) : BQ) *
        algebraMap A BQ π₀ ^ (n * k₂ + a₁) := by
      push_cast
      simp only [IsUnit.unit_spec]
      have e1 : (↑v₁ * algebraMap A BQ π₀ ^ k₁) ^ n * algebraMap A BQ r₂ * (algebraMap A BQ s₁' *
          algebraMap A BQ s₂') = (↑v₂ * algebraMap A BQ π₀ ^ k₂) ^ n * algebraMap A BQ r₁ *
          (algebraMap A BQ s₁' * algebraMap A BQ s₂') := by rw [hBQ']
      calc (↑(v₁ ^ n) : BQ) * algebraMap A BQ r₂' * algebraMap A BQ s₁' *
            algebraMap A BQ π₀ ^ (n * k₁ + a₂)
          = (↑v₁ * algebraMap A BQ π₀ ^ k₁) ^ n * (algebraMap A BQ r₂ * algebraMap A BQ s₂') *
              algebraMap A BQ s₁' := by rw [h₂']; push_cast; ring
        _ = (↑v₂ * algebraMap A BQ π₀ ^ k₂) ^ n * (algebraMap A BQ r₁ * algebraMap A BQ s₁') *
              algebraMap A BQ s₂' := by linear_combination e1
        _ = (↑(v₂ ^ n) : BQ) * algebraMap A BQ r₁' * algebraMap A BQ s₂' *
            algebraMap A BQ π₀ ^ (n * k₂ + a₁) := by rw [h₁']; push_cast; ring
    exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hirrB hirrB _ _ _ _ key

  have hP : algebraMap A K π₀ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hπ₀0
  have hR₂ : algebraMap A K r₂ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hr₂0
  refine ⟨algebraMap A K π₀ ^ k₁ / algebraMap A K π₀ ^ k₂, r₁' * s₂', s₁' * r₂', ?_, ?_, ?_⟩
  · exact fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hr₁' hs₂'
  · exact fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hs₁' hr₂'
  · have h₁K := congrArg (algebraMap A K) h₁
    have h₂K := congrArg (algebraMap A K) h₂
    rw [map_mul, map_mul, map_pow] at h₁K h₂K
    have hPe : algebraMap A K π₀ ^ a₁ * algebraMap A K π₀ ^ (k₂ * n) =
        algebraMap A K π₀ ^ (k₁ * n) * algebraMap A K π₀ ^ a₂ := by
      rw [← pow_add, ← pow_add]; congr 1; linarith
    rw [div_pow, map_mul, map_mul, ← pow_mul, ← pow_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_div_iff hR₂ (pow_ne_zero _ hP)]
    linear_combination (algebraMap A K r₂' * algebraMap A K π₀ ^ (k₂ * n)) * h₁K -
      (algebraMap A K π₀ ^ (k₁ * n) * algebraMap A K r₁') * h₂K +
      algebraMap A K r₁' * algebraMap A K r₂' * hPe

end K2

end KummerClass44

namespace KummerClass44

section K2prime

theorem height_comap_eq_one_of_ringKrullDim_eq_two
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Algebra.IsIntegral A B]
    [FaithfulSMul A B]
    (hA : ringKrullDim A ≤ 2) (hB : ringKrullDim B = 2)
    (P : Ideal B) [P.IsPrime] (hP : P.height = 1) :
    (P.comap (algebraMap A B)).height = 1 := by
  set q := P.comap (algebraMap A B) with hq
  haveI : q.IsPrime := Ideal.IsPrime.comap _
  haveI : FiniteRingKrullDim A := finiteRingKrullDim_iff_ne_bot_and_top.mpr
    ⟨by
      intro h
      have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
      rw [h] at h0; exact absurd h0 (by decide),
     ne_top_of_le_ne_top (by decide) hA⟩
  haveI : FiniteRingKrullDim B := finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by rw [hB]; decide, by rw [hB]; decide⟩

  have hP0 : P ≠ ⊥ := by
    rintro rfl; rw [Ideal.height_bot] at hP; exact zero_ne_one hP
  have hq0 : q ≠ ⊥ := fun h => hP0 (Ideal.eq_bot_of_comap_eq_bot h)

  have hqm : q ≠ IsLocalRing.maximalIdeal A := by
    intro h
    have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P
      (by rw [← hq, h]; exact IsLocalRing.maximalIdeal.isMaximal A)
    have : P = IsLocalRing.maximalIdeal B := IsLocalRing.eq_maximalIdeal hPm
    have h2 : P.height = 2 := by
      rw [this]
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B)
      rw [hB] at this
      exact WithBot.coe_eq_coe.mp this
    rw [hP] at h2; exact absurd h2 (by decide)

  apply le_antisymm
  · have hlt : q < IsLocalRing.maximalIdeal A := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hqm
    have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    have hm : (IsLocalRing.maximalIdeal A).height ≤ 2 := by
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
      rw [← this] at hA
      exact WithBot.coe_le_coe.mp hA
    have h1 : q.height < 2 := lt_of_lt_of_le h1 hm
    have : q.height ≠ ⊤ := by intro h; rw [h] at h1; exact absurd h1 (by decide)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp this
    rw [← hk] at h1 ⊢
    have : k < 2 := by exact_mod_cast h1
    exact_mod_cast (show k ≤ 1 by omega)
  · rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    exact hq0

end K2prime

end KummerClass44

namespace KummerClass44

section K3b

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

def UnitAt (K : Type*) [Field K] [Algebra R K] (P : Ideal R) (x : K) : Prop :=
  ∃ r s : R, r ∉ P ∧ s ∉ P ∧ x * algebraMap R K s = algebraMap R K r

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
theorem UnitAt.mul {P : Ideal R} [P.IsPrime] {x y : K} (hx : UnitAt K P x) (hy : UnitAt K P y) :
    UnitAt K P (x * y) := by
  obtain ⟨r, s, hr, hs, h⟩ := hx
  obtain ⟨r', s', hr', hs', h'⟩ := hy
  refine ⟨r * r', s * s', fun hh => (Ideal.IsPrime.mem_or_mem inferInstance hh).elim hr hr',
    fun hh => (Ideal.IsPrime.mem_or_mem inferInstance hh).elim hs hs', ?_⟩
  rw [map_mul, map_mul]
  linear_combination (y * algebraMap R K s') * h + algebraMap R K r * h'

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
theorem UnitAt.one (P : Ideal R) [P.IsPrime] : UnitAt K P (1 : K) :=
  ⟨1, 1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one P).mpr h),
    fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one P).mpr h), by simp⟩

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
theorem UnitAt.of_not_mem {P : Ideal R} [P.IsPrime] {t : R} (ht : t ∉ P) : UnitAt K P (algebraMap R K t) :=
  ⟨t, 1, ht, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one P).mpr h), by simp⟩

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
theorem UnitAt.ne_zero {P : Ideal R} {x : K} (hx : UnitAt K P x) : x ≠ 0 := by
  obtain ⟨r, s, hr, hs, h⟩ := hx
  rintro rfl
  rw [zero_mul, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective R K)] at h
  exact hr (h ▸ P.zero_mem)

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
theorem UnitAt.inv {P : Ideal R} [P.IsPrime] {x : K} (hx : UnitAt K P x) : UnitAt K P x⁻¹ := by
  have hx0 := hx.ne_zero
  obtain ⟨r, s, hr, hs, h⟩ := hx
  refine ⟨s, r, hs, hr, ?_⟩
  rw [← h, inv_mul_cancel_left₀ hx0]

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
theorem UnitAt.div {P : Ideal R} [P.IsPrime] {x y : K} (hx : UnitAt K P x) (hy : UnitAt K P y) :
    UnitAt K P (x / y) := by
  rw [div_eq_mul_inv]; exact hx.mul hy.inv

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
theorem UnitAt.pow {P : Ideal R} [P.IsPrime] {x : K} (hx : UnitAt K P x) (k : ℕ) : UnitAt K P (x ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact UnitAt.one P
  | succ k ih => rw [pow_succ]; exact ih.mul hx

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
theorem UnitAt.zpow {P : Ideal R} [P.IsPrime] {x : K} (hx : UnitAt K P x) (k : ℤ) : UnitAt K P (x ^ k) := by
  cases k with
  | ofNat k => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hx.pow k
  | negSucc k => rw [zpow_negSucc]; exact (hx.pow _).inv

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] in
theorem UnitAt.prod {ι : Type*} {P : Ideal R} [P.IsPrime] (T : Finset ι) (x : ι → K)
    (hx : ∀ i ∈ T, UnitAt K P (x i)) : UnitAt K P (∏ i ∈ T, x i) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact UnitAt.one P
  | insert a T ha ih =>
    rw [Finset.prod_insert ha]
    exact (hx a (Finset.mem_insert_self a T)).mul (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

theorem UnitAt.generator_of_ne {P Q : Ideal R} [P.IsPrime] [Q.IsPrime]
    (hP : P.height = 1) (hQ : Q.height = 1) {p : R} (hp : P = Ideal.span {p}) (hne : P ≠ Q) :
    UnitAt K Q (algebraMap R K p) := by
  apply UnitAt.of_not_mem
  intro hpQ
  have hle : P ≤ Q := by rw [hp, Ideal.span_le, Set.singleton_subset_iff]; exact hpQ
  rcases hle.lt_or_eq with hlt | heq
  · have := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    rw [hP, hQ] at this; exact lt_irrefl _ this
  · exact hne heq

theorem exists_mul_eq_mul_pow_of_height_eq_one {P : Ideal R} [P.IsPrime] (hP : P.height = 1)
    {p : R} (hp : P = Ideal.span {p}) (r : R) (hr : r ≠ 0) :
    ∃ (a : ℕ) (r' s' : R), r' ∉ P ∧ s' ∉ P ∧ r * s' = r' * p ^ a := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one P hP
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hp
    rw [hp, Ideal.height_bot] at hP; exact zero_ne_one hP
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap R (Localization.AtPrime P) p} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact (congrArg (fun I : Ideal R => Ideal.map (algebraMap R (Localization.AtPrime P)) I) hp).trans
      (by rw [Ideal.map_span, Set.image_singleton])
  have hirr : Irreducible (algebraMap R (Localization.AtPrime P) p) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ((map_ne_zero_iff _ hinj).mpr hp0) hmax
  have hr' : algebraMap R (Localization.AtPrime P) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr' hirr
  obtain ⟨⟨r', s'⟩, hrs⟩ := IsLocalization.mk'_surjective P.primeCompl (u : Localization.AtPrime P)
  dsimp only at hrs
  have hr'P : r' ∉ P := by
    have : IsUnit (IsLocalization.mk' (Localization.AtPrime P) r' s') := by rw [hrs]; exact u.isUnit
    exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P r' s').mp this
  refine ⟨a, r', s', hr'P, s'.2, hinj ?_⟩
  rw [map_mul, map_mul, map_pow, hu, ← hrs, ← IsLocalization.mk'_spec (Localization.AtPrime P) r' s']
  ring

theorem exists_unitAt_mul_zpow {P : Ideal R} [P.IsPrime] (hP : P.height = 1)
    {p : R} (hp : P = Ideal.span {p}) (x : K) (hx : x ≠ 0) :
    ∃ (k : ℤ) (w : K), UnitAt K P w ∧ x = w * algebraMap R K p ^ k := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; apply hx; rw [map_zero, zero_div]
  obtain ⟨ka, a', sa, ha', hsa, ha⟩ := exists_mul_eq_mul_pow_of_height_eq_one hP hp a ha0
  obtain ⟨kb, b', sb, hb', hsb, hbb⟩ := exists_mul_eq_mul_pow_of_height_eq_one hP hp b hb0
  have hpne : p ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hp
    rw [hp, Ideal.height_bot] at hP; exact zero_ne_one hP
  have hp0 : algebraMap R K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hpne
  refine ⟨(ka : ℤ) - (kb : ℤ), (algebraMap R K a' * algebraMap R K sb) / (algebraMap R K b' * algebraMap R K sa),
    ?_, ?_⟩
  · exact ((UnitAt.of_not_mem ha').mul (UnitAt.of_not_mem hsb)).div
      ((UnitAt.of_not_mem hb').mul (UnitAt.of_not_mem hsa))
  · have haK := congrArg (algebraMap R K) ha
    have hbK := congrArg (algebraMap R K) hbb
    rw [map_mul, map_mul, map_pow] at haK hbK
    have hsa0 : algebraMap R K sa ≠ 0 := fun h => hsa ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h ▸ P.zero_mem)
    have hsb0 : algebraMap R K sb ≠ 0 := fun h => hsb ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h ▸ P.zero_mem)
    have hb'0 : algebraMap R K b' ≠ 0 := fun h => hb' ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h ▸ P.zero_mem)
    have hbK0 : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
    rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
    field_simp
    linear_combination (algebraMap R K b' * algebraMap R K p ^ kb) * haK -
      (algebraMap R K a' * algebraMap R K p ^ ka) * hbK

theorem exists_unit_mul_pow_of_forall_height_eq_one
    (hprin : ∀ P : Ideal R, P.IsPrime → P.height = 1 → Submodule.IsPrincipal P)
    (n : ℕ) (f : K) (hf : f ≠ 0)
    (hloc : ∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      ∃ (g : K) (r s : R), r ∉ P ∧ s ∉ P ∧ f * algebraMap R K s = g ^ n * algebraMap R K r) :
    ∃ (u : Rˣ) (g : K), f = algebraMap R K u * g ^ n := by
  classical

  let ι := {P : Ideal R // P.IsPrime ∧ P.height = 1}
  have hgen' : ∀ i : ι, ∃ p : R, i.1 = Ideal.span {p} := fun i =>
    haveI := i.2.1; (hprin i.1 i.2.1 i.2.2).principal
  choose gen hgen using hgen'
  have hgen0 : ∀ i : ι, algebraMap R K (gen i) ≠ 0 := by
    intro i h0
    rw [map_eq_zero_iff _ (IsFractionRing.injective R K)] at h0
    have := hgen i
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at this
    have h1 := i.2.2; rw [this, Ideal.height_bot] at h1; exact zero_ne_one h1

  have hdec : ∀ i : ι, ∃ (k : ℤ) (w : K), UnitAt K i.1 w ∧
      f = w * algebraMap R K (gen i) ^ ((n : ℤ) * k) := by
    intro i
    haveI := i.2.1
    obtain ⟨g, r, s, hr, hs, hfg⟩ := hloc i.1 i.2.2
    have hs0 : algebraMap R K s ≠ 0 := fun h =>
      hs ((map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h ▸ i.1.zero_mem)
    have hg0 : g ≠ 0 ∨ n = 0 := by
      by_cases hn : n = 0
      · exact Or.inr hn
      · left; rintro rfl; rw [zero_pow hn, zero_mul, mul_eq_zero] at hfg
        exact hfg.elim hf hs0
    rcases hg0 with hg0 | hn0
    · obtain ⟨k, w, hw, hgw⟩ := exists_unitAt_mul_zpow i.2.2 (hgen i) g hg0
      refine ⟨k, w ^ n * (algebraMap R K r / algebraMap R K s), (hw.pow n).mul
        ((UnitAt.of_not_mem hr).div (UnitAt.of_not_mem hs)), ?_⟩
      have : f = g ^ n * algebraMap R K r / algebraMap R K s := by rw [eq_div_iff hs0]; exact hfg
      rw [this, hgw, mul_pow, ← zpow_natCast (algebraMap R K (gen i) ^ k), ← zpow_mul, mul_comm k]
      ring
    · subst hn0
      refine ⟨0, f, ?_, by simp⟩
      refine ⟨r, s, hr, hs, ?_⟩
      rw [hfg, pow_zero, one_mul]
  choose j w hw hfw using hdec

  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; apply hf; rw [map_zero, zero_div]
  have hfin : {i : ι | a * b ∈ i.1}.Finite := by
    have hS := Ideal.finite_setOf_height_eq_one_and_mem (R := R) (mul_ne_zero ha0 hb0)
    refine (hS.preimage (f := (Subtype.val : ι → Ideal R)) Subtype.val_injective.injOn).subset ?_
    intro i hi; exact ⟨i.2.1, i.2.2, hi⟩
  let T : Finset ι := hfin.toFinset
  have hT : ∀ i : ι, i ∈ T ↔ a * b ∈ i.1 := fun i => by simp [T]

  let g₀ : K := ∏ i ∈ T, algebraMap R K (gen i) ^ (j i)
  have hg₀0 : g₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hgen0 i)
  let u : K := algebraMap R K a / algebraMap R K b / g₀ ^ n
  have hrest : ∀ (Q : Ideal R) [Q.IsPrime] (hQ : Q.height = 1) (S : Finset ι),
      (⟨Q, ‹_›, hQ⟩ : ι) ∉ S → UnitAt K Q (∏ i ∈ S, algebraMap R K (gen i) ^ (j i)) := by
    intro Q _ hQ S hS
    apply UnitAt.prod
    intro i hi
    haveI := i.2.1
    have hne : i.1 ≠ Q := by
      intro h; apply hS
      have : (⟨Q, ‹_›, hQ⟩ : ι) = i := Subtype.ext h.symm
      rw [this]; exact hi
    exact (UnitAt.generator_of_ne (K := K) i.2.2 hQ (hgen i) hne).zpow _
  have hU : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → UnitAt K Q u := by
    intro Q _ hQ
    let iQ : ι := ⟨Q, ‹_›, hQ⟩
    by_cases hmem : iQ ∈ T
    · have hsplit : g₀ = algebraMap R K (gen iQ) ^ (j iQ) *
          ∏ i ∈ T.erase iQ, algebraMap R K (gen i) ^ (j i) := (Finset.mul_prod_erase T _ hmem).symm
      have hX : algebraMap R K (gen iQ) ^ ((n : ℤ) * j iQ) ≠ 0 := zpow_ne_zero _ (hgen0 iQ)
      have : u = w iQ / (∏ i ∈ T.erase iQ, algebraMap R K (gen i) ^ (j i)) ^ n := by
        show algebraMap R K a / algebraMap R K b / g₀ ^ n = _
        rw [hfw iQ, hsplit, mul_pow, ← zpow_natCast (algebraMap R K (gen iQ) ^ j iQ), ← zpow_mul,
          mul_comm (j iQ) (n : ℤ), mul_comm (algebraMap R K (gen iQ) ^ ((n : ℤ) * j iQ)) (_ ^ n),
          mul_div_mul_right _ _ hX]
      rw [this]
      exact (hw iQ).div ((hrest Q hQ _ (T.notMem_erase iQ)).pow n)
    · have hab : a * b ∉ Q := (hT iQ).not.mp hmem
      have haQ : a ∉ Q := fun h => hab (Q.mul_mem_right b h)
      have hbQ : b ∉ Q := fun h => hab (Q.mul_mem_left a h)
      exact ((UnitAt.of_not_mem haQ).div (UnitAt.of_not_mem hbQ)).div ((hrest Q hQ T hmem).pow n)

  have hmemR : ∀ x : K, (∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → UnitAt K Q x) →
      x ∈ Set.range (algebraMap R K) := by
    intro x hx
    apply IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one
    intro P hP hP1
    haveI := hP
    obtain ⟨r, s, -, hs, h⟩ := hx P hP1
    exact ⟨r, s, hs, h⟩
  obtain ⟨u₀, hu₀⟩ := hmemR u hU
  obtain ⟨u₁, hu₁⟩ := hmemR u⁻¹ fun Q _ hQ => (hU Q hQ).inv
  have hu0 : u ≠ 0 := div_ne_zero (div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha0)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0)) (pow_ne_zero _ hg₀0)
  have hunit : u₀ * u₁ = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, hu₀, hu₁, mul_inv_cancel₀ hu0, map_one]
  refine ⟨Units.mkOfMulEqOne u₀ u₁ hunit, g₀, ?_⟩
  rw [Units.val_mkOfMulEqOne, hu₀]
  show _ = algebraMap R K a / algebraMap R K b / g₀ ^ n * g₀ ^ n
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hg₀0)]

end K3b

end KummerClass44

namespace KummerClass44

open KummerNorm44

section StageA

theorem radicand_eq_unit_mul_U_pow_mul_pow
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (ζ : W) (hζ : IsPrimitiveRoot ζ n)
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (1 * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (1 * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (1 * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (1 * n))) K₀ F]
    [FiniteDimensional K₀ F] [Algebra.IsSeparable K₀ F]
    (hunr : ∀ (Q : Ideal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) [Q.IsPrime],
      (Q.comap (algebraMap (UVCrossingModel W (π ^ (1 * n)))
        ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).height = 1 →
      Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) Q)
    (α : F) (f : K₀) (hf0 : f ≠ 0) (hαf : α ^ n = algebraMap K₀ F f) :
    ∃ (u₀ : (UVCrossingModel W (π ^ (1 * n)))ˣ) (j : ℕ) (h : K₀),
      f = algebraMap _ K₀ (u₀ : UVCrossingModel W (π ^ (1 * n))) *
        algebraMap _ K₀ (U (π ^ (1 * n))) ^ j * h ^ n := by
  classical

  have hn0 : n ≠ 0 := hn.ne'
  have h1n : 1 ≤ 1 * n := by omega
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπmem : π ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
  have hW : IsLocalRing.maximalIdeal W = Ideal.span {π ^ 1} := by rw [pow_one]; exact hπ.maximalIdeal_eq
  have hπ1 : π ^ 1 ∈ IsLocalRing.maximalIdeal W := by rw [pow_one]; exact hπmem
  have hπ10 : π ^ 1 ≠ 0 := pow_ne_zero _ hπ0
  have hπ1n0 : π ^ (1 * n) ≠ 0 := pow_ne_zero _ hπ0

  obtain ⟨iD0, iL0, iIC0⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (1 * n) h1n
  obtain ⟨iD1, iL1, iIC1⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ 1 le_rfl
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ (1 * n))) := ModularCurve.UVCrossingModel.isNoetherianRing _
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ 1)) := ModularCurve.UVCrossingModel.isNoetherianRing _
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ 1))) (UVCrossingModel W (π ^ 1)) :=
    ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal _
  haveI : IsRegularLocalRing (UVCrossingModel W (π ^ 1)) :=
    ModularCurve.UVCrossingModel.isRegularLocalRing hW hπ10
  have hdimR : ringKrullDim (UVCrossingModel W (π ^ 1)) = 2 :=
    ModularCurve.UVCrossingModel.ringKrullDim_eq_two hW hπ10
  have hdimR0 : ringKrullDim (UVCrossingModel W (π ^ (1 * n))) ≤ 2 :=
    ModularCurve.UVCrossingModel.ringKrullDim_le_two π hπ (1 * n) h1n
  have hprin : ∀ P : Ideal (UVCrossingModel W (π ^ 1)), P.IsPrime → P.height = 1 → Submodule.IsPrincipal P :=
    fun P hP hP1 => IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
      (le_of_eq hdimR) P hP hP1

  have h1 : (1 : Fin 2 → W) 0 * (1 : Fin 2 → W) 1 = 1 := by simp
  set φ := modelMap n hn0 1 h1 π 1 with hφdef
  have hφinj : Function.Injective φ :=
    modelMap_injective n hn0 1 h1 (by simp) (by simp) π hπmem (mem_nonZeroDivisors_of_ne_zero hπ0) 1 one_ne_zero
  letI algR : Algebra (UVCrossingModel W (π ^ (1 * n))) (UVCrossingModel W (π ^ 1)) := φ.toAlgebra
  haveI : Module.Finite (UVCrossingModel W (π ^ (1 * n))) (UVCrossingModel W (π ^ 1)) :=
    moduleFinite_modelMap n hn0 1 h1 π 1 1 (fun i => by simp)
  haveI : Algebra.IsIntegral (UVCrossingModel W (π ^ (1 * n))) (UVCrossingModel W (π ^ 1)) :=
    Algebra.IsIntegral.of_finite _ _
  haveI : FaithfulSMul (UVCrossingModel W (π ^ (1 * n))) (UVCrossingModel W (π ^ 1)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hφinj

  have hg : Function.Injective ((algebraMap (UVCrossingModel W (π ^ 1))
      (FractionRing (UVCrossingModel W (π ^ 1)))).comp φ) :=
    by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective (UVCrossingModel W (π ^ 1))
      (FractionRing (UVCrossingModel W (π ^ 1)))).comp hφinj
  obtain ⟨ι, hιalg⟩ : ∃ ι : K₀ →+* FractionRing (UVCrossingModel W (π ^ 1)),
      ∀ r₀, ι (algebraMap _ K₀ r₀) = algebraMap _ _ (φ r₀) :=
    ⟨IsFractionRing.lift hg, IsFractionRing.lift_algebraMap hg⟩
  have hιinj : Function.Injective ι := ι.injective

  have hloc : ∀ (P : Ideal (UVCrossingModel W (π ^ 1))) [P.IsPrime], P.height = 1 →
      ∃ (g : FractionRing (UVCrossingModel W (π ^ 1))) (r s : UVCrossingModel W (π ^ 1)), r ∉ P ∧ s ∉ P ∧
        ι f * algebraMap _ _ s = g ^ n * algebraMap _ _ r := by
    intro P _ hP
    have hq : (P.comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) (UVCrossingModel W (π ^ 1)))).height = 1 :=
      height_comap_eq_one_of_ringKrullDim_eq_two hdimR0 hdimR P hP
    obtain ⟨g₀, r₀, s₀, hr₀, hs₀, hfs⟩ := exists_pow_mul_of_isUnramifiedAt_of_height_eq_one K₀ F hunr n α f hf0 hαf
      (P.comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) (UVCrossingModel W (π ^ 1)))) hq
    refine ⟨ι g₀, φ r₀, φ s₀, fun h => hr₀ (Ideal.mem_comap.mpr h), fun h => hs₀ (Ideal.mem_comap.mpr h), ?_⟩
    have := congrArg ι hfs
    rw [map_mul, map_mul, map_pow, hιalg, hιalg] at this
    exact this

  have hιf0 : ι f ≠ 0 := (map_ne_zero_iff _ hιinj).mpr hf0
  obtain ⟨u₁, g₁, hug⟩ := exists_unit_mul_pow_of_forall_height_eq_one
    (K := FractionRing (UVCrossingModel W (π ^ 1))) hprin n (ι f) hιf0 hloc

  let ζu : Wˣ := (hζ.isUnit hn0).unit
  have hζu : (ζu : W) = ζ := rfl
  let z : Fin 2 → W := ![ζ, ((ζu⁻¹ : Wˣ) : W)]
  have hz : z 0 * z 1 = 1 := by
    show ζ * ((ζu⁻¹ : Wˣ) : W) = 1
    rw [← hζu, Units.mul_inv]
  have hζ' : IsPrimitiveRoot (z 0) n := hζ
  exact descent π 1 n hn hnW h1 z hz hζ' hπ1 hπ10 hπ1n0 hφinj K₀ ι hιalg f hf0 u₁ g₁ hug

end StageA

end KummerClass44

namespace KummerClass44

open KummerNorm44

section K4Field

theorem exists_eq_pow_of_pow_eq_one' {W F : Type*} [CommRing W] [IsDomain W] [Field F]
    (f : W →+* F) (hf : Function.Injective f) (ζ : W) (n : ℕ) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (d : ℕ) (hd : d ∣ n) (η : F) (hη : η ^ d = 1) : ∃ i : ℕ, η = f (ζ ^ (n / d * i)) := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  haveI : NeZero d := ⟨hd0.ne'⟩
  have hnd0 : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hd) hd0).ne'
  have hξ : IsPrimitiveRoot (f ζ ^ (n / d)) d := by
    have := (hζ.map_of_injective hf).pow_of_dvd hnd0 (Nat.div_dvd_of_dvd hd)
    rwa [Nat.div_div_self hd hn.ne'] at this
  obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one hη
  exact ⟨i, by rw [← hi, map_pow, pow_mul]⟩

theorem eq_one_of_pow_div_mem_range {K F : Type*} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] (β : F) (hβ : IntermediateField.adjoin K {β} = ⊤)
    (n d : ℕ) (hn : 0 < n) (hdeg : Module.finrank K F = n) (hd : d ∣ n)
    (hmem : β ^ (n / d) ∈ (algebraMap K F).range) : d = 1 := by
  obtain ⟨c, hc⟩ := hmem
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hd) hd0
  have hint : IsIntegral K β := .of_finite K β
  have hdvd : minpoly K β ∣ Polynomial.X ^ (n / d) - Polynomial.C c := by
    apply minpoly.dvd
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hc, sub_self]
  have hle : (minpoly K β).natDegree ≤ n / d := by
    have h := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.X_pow_sub_C_ne_zero hnd c)
    rwa [Polynomial.natDegree_X_pow_sub_C] at h
  have hfr : Module.finrank K (IntermediateField.adjoin K {β}) = (minpoly K β).natDegree :=
    IntermediateField.adjoin.finrank hint
  rw [hβ, IntermediateField.finrank_top', hdeg] at hfr
  rw [← hfr] at hle
  by_contra hne
  have h1 : 1 < d := lt_of_le_of_ne hd0 (Ne.symm hne)
  exact absurd (Nat.div_lt_self hn h1) (not_lt.mpr hle)

theorem exists_pow_eq_mul_of_coprime {K F : Type*} [Field K] [Field F] [Algebra K F]
    (β : F) (hβ : IntermediateField.adjoin K {β} = ⊤) (n j : ℕ) (hn : 0 < n)
    (hcop : Nat.Coprime j n) (c x : K) (hc : c ≠ 0) (hx : x ≠ 0)
    (hβn : β ^ n = algebraMap K F c * algebraMap K F x ^ j) :
    ∃ (b : ℕ) (θ : F), θ ^ n = algebraMap K F (c ^ b * x) ∧
      IntermediateField.adjoin K {θ} = ⊤ := by
  have hcF : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hxF : algebraMap K F x ≠ 0 := (map_ne_zero _).mpr hx
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hβn
    exact (mul_ne_zero hcF (pow_ne_zero _ hxF)) hβn.symm
  have key : ∀ θ : F, β ∈ IntermediateField.adjoin K {θ} →
      IntermediateField.adjoin K {θ} = ⊤ := by
    intro θ hmem
    rw [eq_top_iff, ← hβ]
    exact IntermediateField.adjoin_simple_le_iff.mpr hmem
  rcases Nat.lt_or_ge 1 n with h1n | hn1
  · obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1n
    obtain ⟨k, hk⟩ : ∃ k, j * b = n * k + 1 := ⟨j * b / n, by
      have := Nat.div_add_mod (j * b) n
      rw [hb] at this
      exact this.symm⟩
    refine ⟨b, β ^ b / algebraMap K F x ^ k, ?_, ?_⟩
    · rw [map_mul, map_pow, div_pow, ← pow_mul β b n, ← pow_mul (algebraMap K F x) k n,
        mul_comm b n, pow_mul β n b, hβn, mul_pow, ← pow_mul (algebraMap K F x) j b, hk,
        div_eq_iff (pow_ne_zero _ hxF)]
      ring
    · set θ := β ^ b / algebraMap K F x ^ k with hθdef
      apply key
      have hθ : β ^ b = θ * algebraMap K F x ^ k := by
        rw [hθdef, div_mul_cancel₀ _ (pow_ne_zero _ hxF)]
      have hmem : (θ * algebraMap K F x ^ k) ^ j / (algebraMap K F c * algebraMap K F x ^ j) ^ k ∈
          IntermediateField.adjoin K {θ} :=
        div_mem (pow_mem (mul_mem (IntermediateField.mem_adjoin_simple_self K θ)
          (pow_mem (algebraMap_mem _ x) _)) _)
          (pow_mem (mul_mem (algebraMap_mem _ c) (pow_mem (algebraMap_mem _ x) _)) _)
      convert hmem using 1
      rw [← hθ, ← hβn, ← pow_mul β b j, ← pow_mul β n k, mul_comm b j, hk, pow_succ,
        mul_div_cancel_left₀ _ (pow_ne_zero _ hβ0)]
  · obtain rfl : n = 1 := le_antisymm hn1 hn
    refine ⟨0, algebraMap K F x, by rw [pow_one, pow_zero, one_mul], key _ ?_⟩
    rw [← pow_one β, hβn]
    exact mul_mem (algebraMap_mem _ c) (pow_mem (algebraMap_mem _ x) _)

end K4Field

section K4Residue

variable {W : Type*} [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W]
  [HenselianRing W (IsLocalRing.maximalIdeal W)]

theorem exists_eq_const_of_pow_eq_const (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W)
    [IsLocalRing (UVCrossingModel W c)]
    (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W)) (ζ : W) (hζ : IsPrimitiveRoot ζ n)
    (d : ℕ) (hd : d ∣ n)
    (F : Type*) [Field F] [Algebra (UVCrossingModel W c) F]
    (hinj : Function.Injective (algebraMap (UVCrossingModel W c) F))
    [IsLocalRing ↥(integralClosure (UVCrossingModel W c) F)]
    (hres : ∀ b : ↥(integralClosure (UVCrossingModel W c) F), ∃ w : W,
      b - algebraMap (UVCrossingModel W c) _ (const c w) ∈
        IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W c) F))
    (w : W) (hw : IsUnit w) (ε : F) (hε : ε ^ d = algebraMap (UVCrossingModel W c) F (const c w)) :
    ∃ w₁ : W, ε = algebraMap (UVCrossingModel W c) F (const c w₁) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn

  have hdW : IsUnit (d : W) := by
    obtain ⟨e, he⟩ := hd
    have : (n : W) = (d : W) * (e : W) := by rw [he, Nat.cast_mul]
    rw [this] at hnW
    exact isUnit_of_mul_isUnit_left hnW

  have hεint : IsIntegral (UVCrossingModel W c) ε := by
    refine ⟨Polynomial.X ^ d - Polynomial.C (const c w), Polynomial.monic_X_pow_sub_C _ hd0.ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hε, sub_self]
  have hεmem : ε ∈ integralClosure (UVCrossingModel W c) F := hεint
  obtain ⟨w', hw'⟩ := hres ⟨ε, hεmem⟩

  have h1 : (⟨ε, hεmem⟩ : ↥(integralClosure (UVCrossingModel W c) F)) ^ d =
      algebraMap (UVCrossingModel W c) _ (const c w) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap]
    exact hε
  have hmemB : algebraMap (UVCrossingModel W c) ↥(integralClosure (UVCrossingModel W c) F)
      (const c (w - w' ^ d)) ∈
        IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W c) F) := by
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow
      (⟨ε, hεmem⟩ : ↥(integralClosure (UVCrossingModel W c) F))
      (algebraMap (UVCrossingModel W c) _ (const c w')) d
    have h2 : algebraMap (UVCrossingModel W c) ↥(integralClosure (UVCrossingModel W c) F)
        (const c (w - w' ^ d)) =
        (⟨ε, hεmem⟩ : ↥(integralClosure (UVCrossingModel W c) F)) ^ d -
          (algebraMap (UVCrossingModel W c) _ (const c w')) ^ d := by
      rw [← constHom_apply, map_sub, map_pow, map_sub, map_pow, constHom_apply, constHom_apply, h1]
    rw [h2, hq]
    exact Ideal.mul_mem_right _ _ hw'

  have hmW : w - w' ^ d ∈ IsLocalRing.maximalIdeal W := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_const_iff c hc]
    intro hu
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmemB (hu.map _))

  have hw'u : IsUnit w' := by
    by_contra h
    have h' : w' ^ d ∈ IsLocalRing.maximalIdeal W :=
      Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr h) _ hd0
    have hwm : w ∈ IsLocalRing.maximalIdeal W := by
      have := Ideal.add_mem _ hmW h'
      rwa [sub_add_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp hwm hw

  obtain ⟨v, hv⟩ := hw'u.exists_right_inv
  have ha : w * v ^ d - 1 ∈ IsLocalRing.maximalIdeal W := by
    have : w * v ^ d - 1 = (w - w' ^ d) * v ^ d := by
      rw [sub_mul, ← mul_pow, hv, one_pow]
    rw [this]
    exact Ideal.mul_mem_right _ _ hmW
  obtain ⟨ω, hωu, hω⟩ := exists_isUnit_pow_eq d hdW _ ha
  have hw1 : (w' * ω) ^ d = w := by
    calc (w' * ω) ^ d = w * (w' * v) ^ d := by rw [mul_pow, hω, mul_pow]; ring
      _ = w := by rw [hv, one_pow, mul_one]

  set f : W →+* F := (algebraMap (UVCrossingModel W c) F).comp (constHom c) with hfdef
  have hfinj : Function.Injective f := hinj.comp (const_injective c hc)
  have hfw : f (w' * ω) ≠ 0 := (map_ne_zero_iff f hfinj).mpr (hw'u.mul hωu).ne_zero
  have hfw' : f w ≠ 0 := (map_ne_zero_iff f hfinj).mpr hw.ne_zero
  have hε' : ε ^ d = f w := hε
  have hη : (ε / f (w' * ω)) ^ d = 1 := by
    rw [div_pow, ← map_pow, hw1, hε', div_self hfw']
  obtain ⟨i, hi⟩ := exists_eq_pow_of_pow_eq_one' f hfinj ζ n hn hζ d hd _ hη
  refine ⟨ζ ^ (n / d * i) * (w' * ω), ?_⟩
  rw [div_eq_iff hfw] at hi
  rw [hi, ← map_mul]
  rfl

end K4Residue

end KummerClass44

namespace KummerClass44

open KummerNorm44

section Final

theorem kummer_class_thicknessOne
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (1 * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (1 * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (1 * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (1 * n))) K₀ F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F))
    (hdeg : Module.finrank K₀ F = n)
    [IsLocalRing ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)]
    (hunr : ∀ (Q : Ideal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) [Q.IsPrime],
      (Q.comap (algebraMap (UVCrossingModel W (π ^ (1 * n)))
        ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).height = 1 →
      Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) Q)
    (hres : ∀ b : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F), ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (1 * n))) _ (const (π ^ (1 * n)) w) ∈
        IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) :
    ∃ (u : (UVCrossingModel W (π ^ (1 * n)))ˣ) (θ : F),
      θ ^ n = algebraMap (UVCrossingModel W (π ^ (1 * n))) F (↑u * U (π ^ (1 * n))) ∧
      IntermediateField.adjoin K₀ {θ} = ⊤ := by
  classical
  obtain ⟨ζ, hζ⟩ := hμ
  have hn0 : n ≠ 0 := hn.ne'
  have h1n : 1 ≤ 1 * n := by omega
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπmem : π ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
  have hπ1n : π ^ (1 * n) ∈ IsLocalRing.maximalIdeal W := Ideal.pow_mem_of_mem _ hπmem _ h1n
  have hπ1n0 : π ^ (1 * n) ≠ 0 := pow_ne_zero _ hπ0
  obtain ⟨iD0, iL0, iIC0⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (1 * n) h1n
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ (1 * n))) :=
    ModularCurve.UVCrossingModel.isNoetherianRing _
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ (1 * n))))
      (UVCrossingModel W (π ^ (1 * n))) :=
    ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal _

  have hRK : Function.Injective (algebraMap (UVCrossingModel W (π ^ (1 * n))) K₀) :=
    IsFractionRing.injective _ _
  have hRF : Function.Injective (algebraMap (UVCrossingModel W (π ^ (1 * n))) F) := by
    rw [IsScalarTower.algebraMap_eq (UVCrossingModel W (π ^ (1 * n))) K₀ F, RingHom.coe_comp]
    exact (algebraMap K₀ F).injective.comp hRK

  obtain ⟨α, f, hf0, hαf, hαtop⟩ :=
    exists_kummer_generator π hπ 1 n one_pos hn hnW ⟨ζ, hζ⟩ K₀ F hcyc hdeg

  obtain ⟨u₀, j, h, hfeq⟩ :=
    radicand_eq_unit_mul_U_pow_mul_pow π hπ n hn hnW ζ hζ K₀ F hunr α f hf0 hαf

  obtain ⟨wu, hwu⟩ := exists_const_mul_sub_one_mem (π ^ (1 * n)) hπ1n u₀
  have hnR0 : IsUnit ((n : ℕ) : UVCrossingModel W (π ^ (1 * n))) := by
    have := hnW.map (constHom (π ^ (1 * n)))
    rwa [map_natCast] at this
  obtain ⟨w₀, -, hw₀⟩ := exists_isUnit_pow_eq n hnR0 _ hwu
  have hu₀ : (u₀ : UVCrossingModel W (π ^ (1 * n))) = const (π ^ (1 * n)) (wu : W) * w₀ ^ n := by
    rw [hw₀, mul_left_comm, const_mul, Units.mul_inv, ← constHom_apply, map_one, mul_one]

  obtain ⟨cK, hcK⟩ : ∃ cK : K₀,
      cK = algebraMap (UVCrossingModel W (π ^ (1 * n))) K₀ (const (π ^ (1 * n)) (wu : W)) := ⟨_, rfl⟩
  obtain ⟨xK, hxK⟩ : ∃ xK : K₀,
      xK = algebraMap (UVCrossingModel W (π ^ (1 * n))) K₀ (U (π ^ (1 * n))) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : K₀,
      g = algebraMap (UVCrossingModel W (π ^ (1 * n))) K₀ w₀ * h := ⟨_, rfl⟩
  have hfeq' : f = cK * xK ^ j * g ^ n := by
    rw [hfeq, hu₀, map_mul, map_pow, hcK, hxK, hg, mul_pow]; ring
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hf0
    rw [hfeq', hg0, zero_pow hn0, mul_zero]
  have hcK0 : cK ≠ 0 := by
    rw [hcK]
    exact (map_ne_zero_iff _ hRK).mpr ((isUnit_const_iff _ hπ1n _).mpr wu.isUnit).ne_zero
  have hxK0 : xK ≠ 0 := by
    rw [hxK]
    exact (map_ne_zero_iff _ hRK).mpr (nonZeroDivisors.ne_zero
      (ModularCurve.UVCrossingModel.U_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ1n0)))

  have hgF0 : algebraMap K₀ F g ≠ 0 := (map_ne_zero _).mpr hg0
  obtain ⟨β, hβ⟩ : ∃ β : F, β = α / algebraMap K₀ F g := ⟨_, rfl⟩
  have hβn : β ^ n = algebraMap K₀ F cK * algebraMap K₀ F xK ^ j := by
    rw [hβ, div_pow, hαf, hfeq', map_mul, map_mul, map_pow, map_pow,
      mul_div_cancel_right₀ _ (pow_ne_zero _ hgF0)]
  have hβtop : IntermediateField.adjoin K₀ {β} = ⊤ := by
    rw [eq_top_iff, ← hαtop, IntermediateField.adjoin_simple_le_iff]
    have hαβ : α = β * algebraMap K₀ F g := by rw [hβ, div_mul_cancel₀ _ hgF0]
    rw [hαβ]
    exact mul_mem (IntermediateField.mem_adjoin_simple_self K₀ β) (algebraMap_mem _ g)

  obtain ⟨d, hd⟩ : ∃ d, Nat.gcd j n = d := ⟨_, rfl⟩
  have hdn : d ∣ n := hd ▸ Nat.gcd_dvd_right j n
  have hdj : d ∣ j := hd ▸ Nat.gcd_dvd_left j n
  have hxF0 : algebraMap K₀ F xK ≠ 0 := (map_ne_zero _).mpr hxK0
  obtain ⟨ε, hε⟩ : ∃ ε : F, ε = β ^ (n / d) / algebraMap K₀ F xK ^ (j / d) := ⟨_, rfl⟩
  have hεd : ε ^ d = algebraMap (UVCrossingModel W (π ^ (1 * n))) F (const (π ^ (1 * n)) (wu : W)) := by
    rw [hε, div_pow, ← pow_mul, ← pow_mul, Nat.div_mul_cancel hdn, Nat.div_mul_cancel hdj, hβn,
      mul_div_cancel_right₀ _ (pow_ne_zero _ hxF0), hcK, ← IsScalarTower.algebraMap_apply]
  obtain ⟨w₁, hw₁⟩ := exists_eq_const_of_pow_eq_const (π ^ (1 * n)) hπ1n n hn hnW ζ hζ d hdn F hRF
    hres (wu : W) wu.isUnit ε hεd
  have hd1 : d = 1 := by
    refine eq_one_of_pow_div_mem_range β hβtop n d hn hdeg hdn (RingHom.mem_range.mpr
      ⟨algebraMap _ K₀ (const (π ^ (1 * n)) w₁) * xK ^ (j / d), ?_⟩)
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, ← hw₁, hε,
      div_mul_cancel₀ _ (pow_ne_zero _ hxF0)]
  have hcop : Nat.Coprime j n := hd.trans hd1

  obtain ⟨b, θ, hθn, hθtop⟩ :=
    exists_pow_eq_mul_of_coprime β hβtop n j hn hcop cK xK hcK0 hxK0 hβn
  have hcu : IsUnit (const (π ^ (1 * n)) (wu : W) ^ b) :=
    ((isUnit_const_iff _ hπ1n _).mpr wu.isUnit).pow b
  refine ⟨hcu.unit, θ, ?_, hθtop⟩
  rw [hθn, hcu.unit_spec, IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (1 * n))) K₀ F
      (const (π ^ (1 * n)) (wu : W) ^ b * U (π ^ (1 * n))),
    map_mul (algebraMap (UVCrossingModel W (π ^ (1 * n))) K₀),
    map_pow (algebraMap (UVCrossingModel W (π ^ (1 * n))) K₀), ← hcK, ← hxK]

end Final

end KummerClass44

theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (1 * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (1 * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (1 * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (1 * n))) K₀ F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F))
    (hdeg : Module.finrank K₀ F = n)
    [IsLocalRing ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)]
    (hunr : ∀ (Q : Ideal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) [Q.IsPrime],
      (Q.comap (algebraMap (UVCrossingModel W (π ^ (1 * n)))
        ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).height = 1 →
      Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) Q)
    (hres : ∀ b : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F), ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (1 * n))) _ (const (π ^ (1 * n)) w) ∈
        IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) :
    ∃ (u : (UVCrossingModel W (π ^ (1 * n)))ˣ) (θ : F),
      θ ^ n = algebraMap (UVCrossingModel W (π ^ (1 * n))) F (↑u * U (π ^ (1 * n))) ∧
      IntermediateField.adjoin K₀ {θ} = ⊤ :=
  KummerClass44.kummer_class_thicknessOne π hπ n hn hnW hμ K₀ F hcyc hdeg hunr hres

end S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne (solution)
