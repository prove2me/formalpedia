-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3d6941c3-82f2-5a94-969c-5d4e528d490d

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

universe u

p2m_open "ModularCurve ModularCurve.UVCrossingModel IsLocalRing P2MW.S_ModularCurve_UVCrossingModel_residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank.IsLocalRing"
open scoped TensorProduct

namespace IsLocalRing p2m_export "IsLocalRing" "ResidueField maximalIdeal residue_eq_zero_iff maximalIdeal.isMaximal mem_maximalIdeal ResidueField.algebraMap_eq residue" end IsLocalRing
p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.residue_norm_eq_residue_pow_finrank_of_pow_sub_mem
    {W : Type u} [CommRing W] [IsLocalRing W] {B : Type u} [CommRing B] [Algebra W B]
    [Module.Free W B] [Module.Finite W B] (b : B) (β₀ : W) (n : ℕ)
    (hn : (b - algebraMap W B β₀) ^ n ∈ (maximalIdeal W).map (algebraMap W B)) :
    residue W (Algebra.norm W b) = residue W β₀ ^ Module.finrank W B := by
  classical

  have h1 : residue W (Algebra.norm W b) = Algebra.norm (ResidueField W) ((1 : ResidueField W) ⊗ₜ[W] b) := by
    rw [Algebra.norm_apply (ResidueField W), ← Algebra.baseChange_lmul, LinearMap.det_baseChange, ← Algebra.norm_apply]
    rfl
  rw [h1, ← Module.finrank_baseChange (R := ResidueField W)]

  apply Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap
  have h3 : (1 : ResidueField W) ⊗ₜ[W] b - algebraMap (ResidueField W) (ResidueField W ⊗[W] B) (residue W β₀) =
      (1 : ResidueField W) ⊗ₜ[W] (b - algebraMap W B β₀) := by
    rw [TensorProduct.tmul_sub]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      ← IsLocalRing.ResidueField.algebraMap_eq, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  rw [h3]
  refine ⟨n, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow]
  have key : ∀ m ∈ (maximalIdeal W).map (algebraMap W B), (1 : ResidueField W) ⊗ₜ[W] m = 0 := by
    intro m hm
    have hm' : m ∈ maximalIdeal W • (⊤ : Submodule W B) := by
      rw [Ideal.smul_top_eq_map]; exact hm
    refine Submodule.smul_induction_on hm' (fun a ha y _ => ?_)
      (fun y z hy hz => by rw [TensorProduct.tmul_add, hy, hz, add_zero])
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff a).mpr ha, TensorProduct.zero_tmul]
  exact key _ hn

p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.exists_pow_mem_map_maximalIdeal_of_mem_maximalIdeal
    {W : Type u} [CommRing W] [IsLocalRing W] {R : Type u} [CommRing R] [IsLocalRing R] [Algebra W R]
    {B : Type u} [CommRing B] [Algebra W B] [Module.Finite W B]
    (φ : R →+* B) (hφ : Function.Surjective φ) (hcomp : ∀ c : W, φ (algebraMap W R c) = algebraMap W B c)
    (Y : R) (hY : Y ∈ maximalIdeal R) :
    ∃ n : ℕ, φ Y ^ n ∈ (maximalIdeal W).map (algebraMap W B) := by
  classical

  haveI : Algebra.IsIntegral W B := Algebra.IsIntegral.of_finite W B
  obtain ⟨f, hfmon, hfY⟩ : IsIntegral W (φ Y) := Algebra.IsIntegral.isIntegral _

  have htop : f.coeff f.natDegree ∉ maximalIdeal W := by
    rw [hfmon.coeff_natDegree]
    exact fun h => (maximalIdeal.isMaximal W).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  have hex : ∃ r, f.coeff r ∉ maximalIdeal W := ⟨f.natDegree, htop⟩
  let r := Nat.find hex
  have hr : f.coeff r ∉ maximalIdeal W := Nat.find_spec hex
  have hlt : ∀ i < r, f.coeff i ∈ maximalIdeal W := fun i hi => by
    have := Nat.find_min hex hi
    simpa using this
  have hrle : r ≤ f.natDegree := Nat.find_min' hex htop
  refine ⟨r, ?_⟩
  set y := φ Y with hy
  have hsum : ∑ i ∈ Finset.range (f.natDegree + 1), algebraMap W B (f.coeff i) * y ^ i = 0 := by
    rw [Polynomial.eval₂_eq_sum_range] at hfY
    simpa [Algebra.smul_def] using hfY

  have hlow : ∑ i ∈ Finset.range r, algebraMap W B (f.coeff i) * y ^ i ∈ (maximalIdeal W).map (algebraMap W B) := by
    refine Ideal.sum_mem _ (fun i hi => ?_)
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hlt i (Finset.mem_range.mp hi)))

  have hsplit : ∑ i ∈ Finset.range (f.natDegree + 1), algebraMap W B (f.coeff i) * y ^ i =
      ∑ i ∈ Finset.range r, algebraMap W B (f.coeff i) * y ^ i +
        y ^ r * ∑ j ∈ Finset.range (f.natDegree + 1 - r), algebraMap W B (f.coeff (r + j)) * y ^ j := by
    conv_lhs => rw [show f.natDegree + 1 = r + (f.natDegree + 1 - r) by omega, Finset.sum_range_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_add]; ring
  set w := ∑ j ∈ Finset.range (f.natDegree + 1 - r), algebraMap W B (f.coeff (r + j)) * y ^ j with hw
  have hwunit : IsUnit w := by
    have hS : ∑ j ∈ Finset.range (f.natDegree - r), algebraMap W B (f.coeff (r + (j + 1))) * y ^ (j + 1) =
        y * ∑ j ∈ Finset.range (f.natDegree - r), algebraMap W B (f.coeff (r + (j + 1))) * y ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hw' : w = algebraMap W B (f.coeff r) +
        y * ∑ j ∈ Finset.range (f.natDegree - r), algebraMap W B (f.coeff (r + (j + 1))) * y ^ j := by
      rw [hw, show f.natDegree + 1 - r = (f.natDegree - r) + 1 by omega, Finset.sum_range_succ', hS, pow_zero, mul_one,
        add_zero, add_comm]
    rw [hw']
    obtain ⟨Z, hZ⟩ := hφ (∑ j ∈ Finset.range (f.natDegree - r), algebraMap W B (f.coeff (r + (j + 1))) * y ^ j)
    have hunitW : IsUnit (f.coeff r) := by
      by_contra h
      exact hr ((mem_maximalIdeal _).mpr h)
    have hunitR : IsUnit (algebraMap W R (f.coeff r) + Y * Z) := by
      have hmem : Y * Z ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hY
      have hcu : IsUnit (algebraMap W R (f.coeff r)) := hunitW.map _
      by_contra hnu
      have h2 : algebraMap W R (f.coeff r) + Y * Z ∈ maximalIdeal R := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      have h3 := sub_mem h2 hmem
      rw [add_sub_cancel_right] at h3
      exact (mem_maximalIdeal _).mp h3 hcu
    have := hunitR.map φ
    rwa [map_add, map_mul, hcomp, hZ] at this

  have hyr : y ^ r * w ∈ (maximalIdeal W).map (algebraMap W B) := by
    have : y ^ r * w = -(∑ i ∈ Finset.range r, algebraMap W B (f.coeff i) * y ^ i) := by
      rw [hsplit] at hsum
      linear_combination hsum
    rw [this]
    exact Submodule.neg_mem _ hlow
  have := Ideal.mul_mem_right (↑hwunit.unit⁻¹ : B) _ hyr
  rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at this

namespace Ideal p2m_export "Ideal" "Quotient.eq_zero_iff_mem mul_mem_right sum_mem span eq_top_of_isUnit_mem smul_top_eq_map Quotient.mk map span_singleton_eq_top Quotient.lift_mk ext mem_span_singleton' mem_map_of_mem Quotient.lift ResidueField Quotient.nontrivial_iff Quotient.mk_surjective mem_span_singleton_self" end Ideal
p2m_open_scoped "Ideal" in

theorem Ideal.exists_pow_mem_of_pow_mem_of_pow_mem {B : Type u} [CommRing B] (I : Ideal B)
    (u v a b : B) {n₁ n₂ : ℕ} (hu : u ^ n₁ ∈ I) (hv : v ^ n₂ ∈ I) :
    ∃ n : ℕ, (u * a + v * b) ^ n ∈ I := by
  have hnil : IsNilpotent (Ideal.Quotient.mk I (u * a + v * b)) := by
    rw [map_add, map_mul, map_mul]
    refine Commute.isNilpotent_add (Commute.all _ _) ?_ ?_
    · exact Commute.isNilpotent_mul_right (Commute.all _ _) ⟨n₁, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hu⟩
    · exact Commute.isNilpotent_mul_right (Commute.all _ _) ⟨n₂, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hv⟩
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn; exact hn⟩

set_option maxHeartbeats 1600000 in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (Q : Ideal (UVCrossingModel W (π ^ E)))
    [Module.Free W (UVCrossingModel W (π ^ E) ⧸ Q)] [Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q)]
    (G : MvPowerSeries (Fin 2) W) :
    residue W (Algebra.norm W (Ideal.Quotient.mk Q (mk (π ^ E) G))) =
      residue W (MvPowerSeries.constantCoeff G) ^ Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q) := by
  classical
  haveI hlocR : IsLocalRing (UVCrossingModel W (π ^ E)) :=
    UVCrossingModel.isLocalRing_of_not_isUnit (fun h => hπ.not_isUnit (isUnit_of_dvd_unit (dvd_pow_self π (by omega)) h))

  haveI : Nontrivial (W ⧸ Ideal.span {π ^ E}) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun h => hπ.not_isUnit
      (isUnit_of_dvd_unit (dvd_pow_self π (by omega)) (Ideal.span_singleton_eq_top.mp h)))
  obtain ⟨χ, hχU, hχV⟩ : ∃ χ : UVCrossingModel W (π ^ E) →+* W ⧸ Ideal.span {π ^ E},
      χ (U (π ^ E)) = 0 ∧ χ (V (π ^ E)) = 0 := by
    refine ⟨Ideal.Quotient.lift (uvCrossingIdeal W (π ^ E))
      ((Ideal.Quotient.mk (Ideal.span {π ^ E})).comp MvPowerSeries.constantCoeff) ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp only [RingHom.comp_apply, map_mul, map_sub, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C,
        zero_mul, zero_sub, map_neg, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (π ^ E)),
        neg_zero, mul_zero, map_zero, sub_zero]
    · show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = 0
      rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPowerSeries.constantCoeff_X, map_zero]
    · show Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = 0
      rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, MvPowerSeries.constantCoeff_X, map_zero]
  have hUm : U (π ^ E) ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map χ
    rw [hχU] at this
    exact not_isUnit_zero this
  have hVm : V (π ^ E) ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map χ
    rw [hχV] at this
    exact not_isUnit_zero this

  obtain ⟨n₁, hn₁⟩ := IsLocalRing.exists_pow_mem_map_maximalIdeal_of_mem_maximalIdeal
    (W := W) (R := UVCrossingModel W (π ^ E)) (B := UVCrossingModel W (π ^ E) ⧸ Q) (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective (fun c => rfl) _ hUm
  obtain ⟨n₂, hn₂⟩ := IsLocalRing.exists_pow_mem_map_maximalIdeal_of_mem_maximalIdeal
    (W := W) (R := UVCrossingModel W (π ^ E)) (B := UVCrossingModel W (π ^ E) ⧸ Q) (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective (fun c => rfl) _ hVm

  have hGsplit : ∃ K₁ K₂ : MvPowerSeries (Fin 2) W,
      G - MvPowerSeries.C (MvPowerSeries.constantCoeff G) = MvPowerSeries.X 0 * K₁ + MvPowerSeries.X 1 * K₂ := by
    set H : MvPowerSeries (Fin 2) W := G - MvPowerSeries.C (MvPowerSeries.constantCoeff G) with hH
    have hH0 : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) H = 0 := by
      rw [hH, map_sub, MvPowerSeries.coeff_C, if_pos rfl, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]
    let H₁ : MvPowerSeries (Fin 2) W := fun m => if 1 ≤ m 0 then MvPowerSeries.coeff m H else 0
    have hH₁ : ∀ m, MvPowerSeries.coeff m H₁ = if 1 ≤ m 0 then MvPowerSeries.coeff m H else 0 := fun m => rfl
    obtain ⟨K₁, hK₁⟩ : MvPowerSeries.X (0 : Fin 2) ^ 1 ∣ H₁ := by
      rw [MvPowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [hH₁, if_neg (by omega)]
    obtain ⟨K₂, hK₂⟩ : MvPowerSeries.X (1 : Fin 2) ^ 1 ∣ H - H₁ := by
      rw [MvPowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hH₁]
      split_ifs with h0
      · rw [sub_self]
      · rw [sub_zero]
        have hm0 : m = 0 := by
          ext i; fin_cases i <;> simp <;> omega
        rw [hm0]; exact hH0
    refine ⟨K₁, K₂, ?_⟩
    rw [pow_one] at hK₁ hK₂
    rw [← hK₁, ← hK₂]
    ring
  obtain ⟨K₁, K₂, hK⟩ := hGsplit
  have hx : Ideal.Quotient.mk Q (mk (π ^ E) G) -
        (algebraMap W (UVCrossingModel W (π ^ E) ⧸ Q) : W →+* UVCrossingModel W (π ^ E) ⧸ Q) (MvPowerSeries.constantCoeff G) =
      Ideal.Quotient.mk Q (U (π ^ E)) * Ideal.Quotient.mk Q (mk (π ^ E) K₁) +
        Ideal.Quotient.mk Q (V (π ^ E)) * Ideal.Quotient.mk Q (mk (π ^ E) K₂) := by
    have halg : (algebraMap W (UVCrossingModel W (π ^ E) ⧸ Q) : W →+* UVCrossingModel W (π ^ E) ⧸ Q) (MvPowerSeries.constantCoeff G) =
        Ideal.Quotient.mk Q (mk (π ^ E) (MvPowerSeries.C (MvPowerSeries.constantCoeff G))) := rfl
    rw [halg, ← map_sub, ← map_sub, hK]
    simp only [map_add, map_mul]
    rfl
  obtain ⟨n, hn⟩ := Ideal.exists_pow_mem_of_pow_mem_of_pow_mem _ _ _
    (Ideal.Quotient.mk Q (mk (π ^ E) K₁)) (Ideal.Quotient.mk Q (mk (π ^ E) K₂)) hn₁ hn₂
  rw [← hx] at hn
  exact IsLocalRing.residue_norm_eq_residue_pow_finrank_of_pow_sub_mem (W := W) (B := UVCrossingModel W (π ^ E) ⧸ Q)
    (Ideal.Quotient.mk Q (mk (π ^ E) G)) (MvPowerSeries.constantCoeff G) n hn

end S_ModularCurve_UVCrossingModel_residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_residue_norm_quotient_mk_eq_residue_constantCoeff_pow_finrank (solution)
