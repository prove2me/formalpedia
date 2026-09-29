-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e950c3b0-c6d2-55d6-a758-16765cd7ab72

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U

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

namespace KummerNorm44

section Main

theorem main
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnW : IsUnit (n : W))
    (u : (UVCrossingModel W (π ^ (m * n)))ˣ)
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (m * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (m * n))) K₀ F]
    (θ : F) (hθ : θ ^ n = algebraMap (UVCrossingModel W (π ^ (m * n))) F (↑u * U (π ^ (m * n))))
    (hF : IntermediateField.adjoin K₀ {θ} = ⊤) :
    Module.Finite (UVCrossingModel W (π ^ (m * n)))
        ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ∧
    IsLocalRing ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ∧
    ∃ e : ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ≃+* UVCrossingModel W (π ^ m),
      (∀ w : W, e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (const (π ^ (m * n)) w)) =
        const (π ^ m) w) ∧
      (∃ v : (UVCrossingModel W (π ^ m))ˣ,
        ((e.symm (↑v * U (π ^ m)) : ↥(integralClosure _ F)) : F) = θ) ∧
      (∃ v₁ : (UVCrossingModel W (π ^ m))ˣ,
        e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (U (π ^ (m * n)))) = ↑v₁ * U (π ^ m) ^ n) ∧
      (∃ v₂ : (UVCrossingModel W (π ^ m))ˣ,
        e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (V (π ^ (m * n)))) = ↑v₂ * V (π ^ m) ^ n) := by
  classical

  have hn0 : n ≠ 0 := hn.ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hm0 hn0)
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπmem : π ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
  have hπmn : π ^ (m * n) ∈ IsLocalRing.maximalIdeal W := Ideal.pow_mem_of_mem _ hπmem _ hmn

  obtain ⟨instD0, instL0, instIC0⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ (m * n) hmn
  obtain ⟨instD1, instL1, instIC1⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ m hm
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ (m * n))) :=
    ModularCurve.UVCrossingModel.isNoetherianRing _
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ m)) :=
    ModularCurve.UVCrossingModel.isNoetherianRing _
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel W (π ^ (m * n))))
      (UVCrossingModel W (π ^ (m * n))) :=
    ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal _

  obtain ⟨u₀, hu₀⟩ := exists_const_mul_sub_one_mem (π ^ (m * n)) hπmn u

  have hnR : IsUnit ((n : ℕ) : UVCrossingModel W (π ^ (m * n))) := by
    have := hnW.map (constHom (π ^ (m * n))); rwa [map_natCast] at this
  obtain ⟨w₀, hw₀u, hw₀⟩ := exists_isUnit_pow_eq n hnR _ hu₀

  let c : Fin 2 → W := ![(↑u₀⁻¹ : W), (u₀ : W)]
  have hc0' : c 0 = (↑u₀⁻¹ : W) := rfl
  have hc1' : c 1 = (u₀ : W) := rfl
  have hc : c 0 * c 1 = 1 := by rw [hc0', hc1', Units.inv_mul]
  have hc0 : IsUnit (c 0) := by rw [hc0']; exact Units.isUnit _
  have hc1 : IsUnit (c 1) := by rw [hc1']; exact Units.isUnit _
  let c' : Fin 2 → W := ![(u₀ : W), (↑u₀⁻¹ : W)]
  have hc' : ∀ i, c' i * c i = 1 := by
    intro i; fin_cases i
    · exact Units.mul_inv _
    · exact Units.inv_mul _
  let φ : UVCrossingModel W (π ^ (m * n)) →+* UVCrossingModel W (π ^ m) := modelMap n hn0 c hc π m
  have hφinj : Function.Injective φ :=
    modelMap_injective n hn0 c hc hc0 hc1 π hπmem (mem_nonZeroDivisors_of_ne_zero hπ0) m hm0
  letI algR : Algebra (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ m)) := φ.toAlgebra
  haveI finR : Module.Finite (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ m)) :=
    moduleFinite_modelMap n hn0 c hc π m c' hc'

  let K := FractionRing (UVCrossingModel W (π ^ m))
  let g : UVCrossingModel W (π ^ (m * n)) →+* K := (algebraMap (UVCrossingModel W (π ^ m)) K).comp φ
  have hg : Function.Injective g := (IsFractionRing.injective (UVCrossingModel W (π ^ m)) K).comp hφinj
  letI algK₀K : Algebra K₀ K := (IsFractionRing.lift hg).toAlgebra

  haveI st2 : IsScalarTower (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ m)) K :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI st1 : IsScalarTower (UVCrossingModel W (π ^ (m * n))) K₀ K := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ m)) K r]
    show _ = IsFractionRing.lift hg (algebraMap (UVCrossingModel W (π ^ (m * n))) K₀ r)
    rw [IsFractionRing.lift_algebraMap]
    rfl

  set a := (u : UVCrossingModel W (π ^ (m * n))) * U (π ^ (m * n)) with ha
  let f : Polynomial (UVCrossingModel W (π ^ (m * n))) := Polynomial.X ^ n - Polynomial.C a
  have hfmonic : f.Monic := Polynomial.monic_X_pow_sub_C a hn0
  have hfirr : Irreducible f := irreducible_X_pow_sub_C_unit_mul_U (π ^ (m * n)) hπmn n hn0 u
  have hfirrK : Irreducible (f.map (algebraMap (UVCrossingModel W (π ^ (m * n))) K₀)) :=
    (hfmonic.irreducible_iff_irreducible_map_fraction_map).mp hfirr
  have hθB : IsIntegral (UVCrossingModel W (π ^ (m * n))) θ := by
    refine ⟨f, hfmonic, ?_⟩
    simp only [f, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hθ, sub_self]
  have hθint : IsIntegral K₀ θ := hθB.tower_top
  have hminpoly : minpoly K₀ θ = f.map (algebraMap (UVCrossingModel W (π ^ (m * n))) K₀) := by
    refine (minpoly.eq_of_irreducible_of_monic hfirrK ?_ (hfmonic.map _)).symm
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, Polynomial.eval₂_sub,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hθ, sub_self]
  let v : UVCrossingModel W (π ^ m) := φ w₀
  have hv : IsUnit v := hw₀u.map φ
  let y : K := algebraMap (UVCrossingModel W (π ^ m)) K (v * U (π ^ m))
  have hφa : φ a = (v * U (π ^ m)) ^ n := by
    simp only [ha, v, map_mul, mul_pow, ← map_pow, hw₀]
    rw [modelMap_const n hn0 c hc π m, modelMap_U n hn0 c hc π m, hc0', mul_assoc]
  have hyroot : Polynomial.aeval y (minpoly K₀ θ) = 0 := by
    rw [hminpoly, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, Polynomial.eval₂_sub,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ m)) K,
      sub_eq_zero]
    change algebraMap _ K (v * U (π ^ m)) ^ n = algebraMap (UVCrossingModel W (π ^ m)) K (φ a)
    rw [← map_pow, hφa]
  let pb := IntermediateField.adjoin.powerBasis hθint
  have hpb : Polynomial.aeval y (minpoly K₀ pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]; exact hyroot
  let ψ₁ : ↥(IntermediateField.adjoin K₀ {θ}) →ₐ[K₀] K := pb.lift y hpb
  let ι : F →ₐ[K₀] ↥(IntermediateField.adjoin K₀ {θ}) :=
    ((IntermediateField.equivOfEq hF).symm.toAlgHom).comp
      (IntermediateField.topEquiv (F := K₀) (E := F)).symm.toAlgHom
  let ψ : F →ₐ[K₀] K := ψ₁.comp ι
  have hψθ : ψ θ = y := by
    have h1 : ι θ = pb.gen := by
      rw [IntermediateField.adjoin.powerBasis_gen]
      apply Subtype.ext
      rfl
    show ψ₁ (ι θ) = y
    rw [h1]; exact pb.lift_gen y hpb

  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  have hRinj := IsFractionRing.injective (UVCrossingModel W (π ^ m)) K
  have halgφ : ∀ r : UVCrossingModel W (π ^ (m * n)),
      algebraMap (UVCrossingModel W (π ^ m)) K (φ r) =
        algebraMap K₀ K (algebraMap (UVCrossingModel W (π ^ (m * n))) K₀ r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply (UVCrossingModel W (π ^ (m * n))) K₀ K]; rfl
  have hUK : algebraMap (UVCrossingModel W (π ^ m)) K (U (π ^ m)) ∈ ψ.fieldRange := by
    have hy : y ∈ ψ.fieldRange := AlgHom.mem_fieldRange.mpr ⟨θ, hψθ⟩
    have hvK : algebraMap (UVCrossingModel W (π ^ m)) K v ∈ ψ.fieldRange := by
      show algebraMap (UVCrossingModel W (π ^ m)) K (φ w₀) ∈ ψ.fieldRange
      rw [halgφ]; exact IntermediateField.algebraMap_mem _ _
    have hv0 : algebraMap (UVCrossingModel W (π ^ m)) K v ≠ 0 :=
      (map_ne_zero_iff _ hRinj).mpr hv.ne_zero
    have : algebraMap (UVCrossingModel W (π ^ m)) K (U (π ^ m)) =
        y / algebraMap (UVCrossingModel W (π ^ m)) K v := by
      rw [eq_div_iff hv0, ← map_mul, mul_comm]
    rw [this]; exact div_mem hy hvK
  have hU0 : algebraMap (UVCrossingModel W (π ^ m)) K (U (π ^ m)) ≠ 0 :=
    (map_ne_zero_iff _ hRinj).mpr (nonZeroDivisors.ne_zero
      (ModularCurve.UVCrossingModel.U_mem_nonZeroDivisors
        (pow_mem (mem_nonZeroDivisors_of_ne_zero hπ0) m)))
  have hVK : algebraMap (UVCrossingModel W (π ^ m)) K (V (π ^ m)) ∈ ψ.fieldRange := by
    have hcK : algebraMap (UVCrossingModel W (π ^ m)) K (const (π ^ m) (π ^ m)) ∈ ψ.fieldRange := by
      rw [← modelMap_const n hn0 c hc π m (π ^ m)]
      show algebraMap (UVCrossingModel W (π ^ m)) K (φ _) ∈ ψ.fieldRange
      rw [halgφ]; exact IntermediateField.algebraMap_mem _ _
    have : algebraMap (UVCrossingModel W (π ^ m)) K (V (π ^ m)) =
        algebraMap (UVCrossingModel W (π ^ m)) K (const (π ^ m) (π ^ m)) /
          algebraMap (UVCrossingModel W (π ^ m)) K (U (π ^ m)) := by
      rw [eq_div_iff hU0, ← map_mul, mul_comm, U_mul_V_eq_const]
    rw [this]; exact div_mem hcK hUK
  have hRK : ∀ r : UVCrossingModel W (π ^ m),
      algebraMap (UVCrossingModel W (π ^ m)) K r ∈ ψ.fieldRange := by
    intro r
    obtain ⟨gij, hr⟩ := exists_eq_sum_modelMap_mul n hn0 c hc π m c' hc' r
    rw [hr, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    refine mul_mem ?_ (mul_mem (pow_mem hUK _) (pow_mem hVK _))
    show algebraMap (UVCrossingModel W (π ^ m)) K (φ _) ∈ ψ.fieldRange
    rw [halgφ]; exact IntermediateField.algebraMap_mem _ _
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := UVCrossingModel W (π ^ m)) z
    exact AlgHom.mem_fieldRange.mp (div_mem (hRK p) (hRK q))
  let e₁ : F ≃ₐ[K₀] K := AlgEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  let e₁' : F ≃ₐ[UVCrossingModel W (π ^ (m * n))] K := e₁.restrictScalars (UVCrossingModel W (π ^ (m * n)))

  haveI stl1 : IsScalarTower (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ (m * n)))
      (UVCrossingModel W (π ^ m)) :=
    IsScalarTower.left (M := UVCrossingModel W (π ^ (m * n))) (α := UVCrossingModel W (π ^ m))
  haveI stl2 : IsScalarTower (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ (m * n))) F :=
    IsScalarTower.left (M := UVCrossingModel W (π ^ (m * n))) (α := F)
  haveI stl3 : IsScalarTower (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ (m * n))) K :=
    IsScalarTower.left (M := UVCrossingModel W (π ^ (m * n))) (α := K)
  let ιR : UVCrossingModel W (π ^ m) →ₐ[UVCrossingModel W (π ^ (m * n))] K :=
    IsScalarTower.toAlgHom (UVCrossingModel W (π ^ (m * n))) (UVCrossingModel W (π ^ m)) K
  have hιR : Function.Injective ιR := hRinj
  let κ₀ : UVCrossingModel W (π ^ m) →ₐ[UVCrossingModel W (π ^ (m * n))] F := e₁'.symm.toAlgHom.comp ιR
  have hκ₀ : ∀ r, κ₀ r ∈ integralClosure (UVCrossingModel W (π ^ (m * n))) F := fun r =>
    (Algebra.IsIntegral.isIntegral (R := UVCrossingModel W (π ^ (m * n))) r).map κ₀
  let κ : UVCrossingModel W (π ^ m) →ₐ[UVCrossingModel W (π ^ (m * n))]
      ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) := κ₀.codRestrict _ hκ₀
  have hκinj : Function.Injective κ := by
    intro r s hrs
    have := congrArg Subtype.val hrs
    exact hιR (e₁'.symm.injective this)
  have hκsurj : Function.Surjective κ := by
    rintro ⟨b, hb⟩
    have hbK : IsIntegral (UVCrossingModel W (π ^ (m * n))) (e₁' b) := IsIntegral.map e₁'.toAlgHom hb
    have hbK' : IsIntegral (UVCrossingModel W (π ^ m)) (e₁' b) := hbK.tower_top
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hbK'
    refine ⟨r, Subtype.ext ?_⟩
    show e₁'.symm (ιR r) = b
    rw [show ιR r = e₁' b from hr, AlgEquiv.symm_apply_apply]
  let e := (AlgEquiv.ofBijective κ ⟨hκinj, hκsurj⟩).symm
  have he : ∀ b : ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F), ιR (e b) = ψ (b : F) := by
    intro b
    have h1 : κ (e b) = b := AlgEquiv.apply_symm_apply (AlgEquiv.ofBijective κ ⟨hκinj, hκsurj⟩) b
    have h2 := congrArg Subtype.val h1
    have h3 : e₁' (e₁'.symm (ιR (e b))) = e₁' b := congrArg e₁' h2
    rw [AlgEquiv.apply_symm_apply] at h3
    exact h3

  refine ⟨Module.Finite.equiv e.symm.toLinearEquiv, ?_, e.toRingEquiv, ?_, ?_, ?_, ?_⟩
  · exact IsLocalRing.of_surjective' e.symm.toAlgHom.toRingHom fun b => ⟨e b, e.symm_apply_apply b⟩
  · intro w
    show e (algebraMap _ _ (const _ w)) = const _ w
    rw [AlgEquiv.commutes]; exact modelMap_const n hn0 c hc π m w
  · refine ⟨hv.unit, ?_⟩
    have hθe : e ⟨θ, hθB⟩ = v * U (π ^ m) := by
      apply hιR
      rw [he]
      exact hψθ
    show ((e.symm (hv.unit * U (π ^ m)) : ↥(integralClosure _ F)) : F) = θ
    rw [IsUnit.unit_spec, ← hθe, AlgEquiv.symm_apply_apply]
  · refine ⟨Units.map (constHom (π ^ m)).toMonoidHom u₀⁻¹, ?_⟩
    show e (algebraMap _ _ (U _)) = const (π ^ m) (↑u₀⁻¹ : W) * U (π ^ m) ^ n
    rw [AlgEquiv.commutes]; exact modelMap_U n hn0 c hc π m
  · refine ⟨Units.map (constHom (π ^ m)).toMonoidHom u₀, ?_⟩
    show e (algebraMap _ _ (V _)) = const (π ^ m) (u₀ : W) * V (π ^ m) ^ n
    rw [AlgEquiv.commutes]; exact modelMap_V n hn0 c hc π m

end Main

end KummerNorm44

theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnW : IsUnit (n : W))
    (u : (UVCrossingModel W (π ^ (m * n)))ˣ)
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (m * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (m * n))) K₀ F]
    (θ : F) (hθ : θ ^ n = algebraMap (UVCrossingModel W (π ^ (m * n))) F (↑u * U (π ^ (m * n))))
    (hF : IntermediateField.adjoin K₀ {θ} = ⊤) :
    Module.Finite (UVCrossingModel W (π ^ (m * n)))
        ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ∧
    IsLocalRing ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ∧
    ∃ e : ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ≃+* UVCrossingModel W (π ^ m),
      (∀ w : W, e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (const (π ^ (m * n)) w)) =
        const (π ^ m) w) ∧
      (∃ v : (UVCrossingModel W (π ^ m))ˣ,
        ((e.symm (↑v * U (π ^ m)) : ↥(integralClosure _ F)) : F) = θ) ∧
      (∃ v₁ : (UVCrossingModel W (π ^ m))ˣ,
        e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (U (π ^ (m * n)))) = ↑v₁ * U (π ^ m) ^ n) ∧
      (∃ v₂ : (UVCrossingModel W (π ^ m))ˣ,
        e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (V (π ^ (m * n)))) = ↑v₂ * V (π ^ m) ^ n) :=
  KummerNorm44.main π hπ m n hm hn hnW u K₀ F θ hθ hF

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U (solution)
