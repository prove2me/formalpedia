-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/0c333ee4-04cf-57fe-b617-d6583ffb5764

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
p2m_open "ModularCurve Polynomial AlgebraicGeometry.Polynomial"

open scoped MatrixGroups

noncomputable section

namespace P2MKcG0RatKPow

section CoeffMap

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem coeffMap_ofPowerSeries (φ : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R φ) = HahnSeries.ofPowerSeries ℤ S (φ.map f) := by
  ext m
  rw [coeffMap_coeff]
  change f (((φ : PowerSeries R) : LaurentSeries R).coeff m) =
    ((PowerSeries.map f φ : PowerSeries S) : LaurentSeries S).coeff m
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · exact (PowerSeries.coeff_map _ _ _).symm

theorem coeffMap_injective (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y hxy
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, hxy]

end CoeffMap

section Toric

variable {F F' : Type*} [Field F] [Field F'] (f : F →+* F')

theorem coeffMap_toricPoint_fst (p : ℕ) (c : F) :
    coeffMap f (toricPoint F p c).1 = (toricPoint F' p (f c)).1 := by
  rw [toricPoint_fst, toricPoint_fst, coeffMap_ofPowerSeries]
  congr 1
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm, map_div₀, map_pow, map_sub, map_one]
  · rw [if_neg hm, if_neg hm]
    simp only [map_sub, map_sum, map_mul, map_add, map_pow, map_natCast, apply_ite f, map_zero,
      map_ofNat, map_inv₀]

theorem toricPoint_fst_coeff_zero (p : ℕ) (c : F) :
    ((toricPoint F p c).1).coeff 0 = c / (1 - c) ^ 2 := by
  rw [toricPoint_fst]
  have : ((HahnSeries.ofPowerSeries ℤ F) (PowerSeries.mk fun m =>
      if m = 0 then c / (1 - c) ^ 2
      else (∑ d ∈ m.divisors, if p ∣ d then ((m / d : ℕ) : F) * (c ^ (m / d) + c⁻¹ ^ (m / d)) else 0)
        - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : F) else 0))).coeff ((0 : ℕ) : ℤ) =
      c / (1 - c) ^ 2 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_pos rfl]
  simpa using this

theorem toricPoint_fst_ne_of_isPrimitiveRoot (p N : ℕ) (hN : 3 < N) (ξ : F) (hξ : IsPrimitiveRoot ξ N) :
    (toricPoint F p ξ).1 ≠ (toricPoint F p (ξ ^ 2)).1 := by
  intro h
  have h0 := congrArg (fun x : LaurentSeries F => x.coeff 0) h
  simp only [toricPoint_fst_coeff_zero] at h0
  have hN1 : 1 < N := by omega
  have hξ1 : ξ ≠ 1 := hξ.ne_one hN1
  have hξ2 : ξ ^ 2 ≠ 1 := by
    intro h2
    have := (hξ.pow_eq_one_iff_dvd 2).mp h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hξ3 : ξ ^ 3 ≠ 1 := by
    intro h3
    have := (hξ.pow_eq_one_iff_dvd 3).mp h3
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hd1 : (1 - ξ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ1)
  have hd2 : (1 - ξ ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ2)
  rw [div_eq_div_iff (pow_ne_zero 2 hd1) (pow_ne_zero 2 hd2)] at h0

  have hξ0 : ξ ≠ 0 := hξ.ne_zero (by omega)
  have key : ξ * (1 - ξ) ^ 2 * (ξ ^ 2 + ξ + 1) = 0 := by linear_combination h0
  rcases mul_eq_zero.mp key with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hξ0 h2
    · exact hd1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
  · apply hξ3
    linear_combination (ξ - 1) * h1

end Toric

section GammaH

theorem T_mem_GammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH N H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]
    simp
  refine ⟨hT, ?_⟩
  have : CohCarrier.gamma0Units N ⟨ModularGroup.T, hT⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    change (((ModularGroup.T : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = ((1 : (ZMod N)ˣ) : ZMod N)
    rw [ModularGroup.coe_T]
    simp
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods_GammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    (1 : ℝ) ∈ (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_GammaH N H)]
  exact AddSubgroup.mem_zmultiples _

end GammaH

section Lifts

variable {A B : Type*} [Field A] [Field B] (g : A →+* B)

theorem coeff_mem_range_of_eval_natCast_mem_range [CharZero B] (P : B[X]) (n : ℕ)
    (hdeg : P.degree < (n + 1 : ℕ))
    (hval : ∀ c : ℕ, c < n + 1 → P.eval (c : B) ∈ Set.range g) (m : ℕ) :
    P.coeff m ∈ Set.range g := by
  classical
  have hinj : Set.InjOn (fun c : ℕ => (c : B)) ↑(Finset.range (n + 1)) :=
    fun a _ b _ h => Nat.cast_injective h
  have hcard : P.degree < (Finset.range (n + 1)).card := by rwa [Finset.card_range]
  have hP := Lagrange.eq_interpolate (v := fun c : ℕ => (c : B)) hinj hcard
  suffices hl : P ∈ Polynomial.lifts g from (Polynomial.lifts_iff_coeff_lifts P).mp hl m
  rw [hP, Lagrange.interpolate_apply]
  refine Subsemiring.sum_mem _ fun c hc => Subsemiring.mul_mem _ ?_ ?_
  · obtain ⟨y, hy⟩ := hval c (Finset.mem_range.mp hc)
    simpa only [hy] using Polynomial.C_mem_lifts g y
  · unfold Lagrange.basis
    refine Subsemiring.prod_mem _ fun j hj => ?_
    unfold Lagrange.basisDivisor
    rw [Polynomial.lifts_iff_liftsRing]
    refine Subring.mul_mem _ ?_ (Subring.sub_mem _ ?_ ?_)
    · rw [← Polynomial.lifts_iff_liftsRing]
      have : ((c : B) - (j : B))⁻¹ = g (((c : A) - (j : A))⁻¹) := by simp
      rw [this]; exact Polynomial.C_mem_lifts g _
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.X_mem_lifts g
    · rw [← Polynomial.lifts_iff_liftsRing]
      have : ((j : B)) = g (j : A) := by simp
      show Polynomial.C ((j : B)) ∈ _
      rw [this]; exact Polynomial.C_mem_lifts g _

end Lifts

section Comp

variable {R : Type*} [CommRing R]

theorem finset_sum_comp {ι : Type*} (s : Finset ι) (p : ι → R[X]) (r : R[X]) :
    (∑ i ∈ s, p i).comp r = ∑ i ∈ s, (p i).comp r :=
  map_sum (Polynomial.compRingHom r) p s

theorem finset_prod_comp {ι : Type*} (s : Finset ι) (p : ι → R[X]) (r : R[X]) :
    (∏ i ∈ s, p i).comp r = ∏ i ∈ s, (p i).comp r :=
  map_prod (Polynomial.compRingHom r) p s

end Comp

section Count

theorem card_filter_not_dvd (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) (hpk2 : p ^ k ≠ 2) :
    ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)).card = Nat.totient (p ^ k) / 2 := by
  have hp : p.Prime := Fact.out
  have h1 : ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => p ∣ a)).card +
      ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)).card = p ^ k / 2 := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have h2 : ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => p ∣ a)).card = p ^ k / 2 / p := by
    have : Finset.Icc 1 (p ^ k / 2) = Finset.Ioc 0 (p ^ k / 2) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [this]
    exact Nat.Ioc_filter_dvd_card_eq_div _ p
  have hpow : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hk]
  have h3 : p ^ k / 2 / p = p ^ (k - 1) / 2 := by
    rw [Nat.div_div_eq_div_mul, mul_comm 2 p, ← Nat.div_div_eq_div_mul, hpow, Nat.mul_div_cancel _ hp.pos]
  have h4 : Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) := Nat.totient_prime_pow hp hk
  rw [h2, h3] at h1
  rw [h4]
  have hAle : p ^ (k - 1) ≤ p ^ k := Nat.pow_le_pow_right hp.pos (Nat.sub_le k 1)
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have hk1 : k ≠ 1 := fun h => hpk2 (by rw [h, pow_one])
    have hA : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [hA] at h1 hpow ⊢
    omega
  · have hAodd : (p ^ (k - 1)) % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    have hNodd : (p ^ k) % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    have hmul : p ^ (k - 1) * (p - 1) = p ^ k - p ^ (k - 1) := by
      rw [Nat.mul_sub_one, ← hpow]
    rw [hmul]
    omega

theorem card_filter_not_dvd_eq_gamma0PowDeg (p k : ℕ) [Fact p.Prime] :
    ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)).card = ModularCurve.gamma0PowDeg p k := by
  unfold ModularCurve.gamma0PowDeg
  split_ifs with h2
  · obtain ⟨rfl, rfl⟩ := Nat.prime_two.pow_eq_iff.mp h2
    decide
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact P2MKcG0RatKPow.card_filter_not_dvd p k hk h2

end Count

end P2MKcG0RatKPow

open P2MKcG0RatKPow

set_option maxHeartbeats 3200000 in

theorem solution
    (M' : ℕ) [NeZero M']
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓg)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓg))
    (K'' : IntermediateField L (LaurentSeries L))
    (hK'' : K'' = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker))
    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M')
    (h : Polynomial (LaurentSeries L))
    (hh : ∀ (F' : Type) [Field F'] (f : L →+* F') (ζ : F'), IsPrimitiveRoot ζ (p ^ k) →
      h.map (ModularCurve.coeffMap f) =
        ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
          (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' 1 (ζ ^ a)).1))
    (C : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hx₁ : ((⟨(ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1, (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).2, (ModularCurve.tateToricPoint L 1 ((hζ.isUnit hℓg.ne_zero).unit ^ 2)).1, (ModularCurve.tateToricPoint L 1 ((hζ.isUnit hℓg.ne_zero).unit ^ 2)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xP ∈ Set.range ((↑) : ↥K'' → LaurentSeries L))
    (hx₂ : ((⟨(ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1, (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).2, (ModularCurve.tateToricPoint L 1 ((hζ.isUnit hℓg.ne_zero).unit ^ 2)).1, (ModularCurve.tateToricPoint L 1 ((hζ.isUnit hℓg.ne_zero).unit ^ 2)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xQ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L)) :
    ∀ i : ℕ, (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h).coeff i ∈
      Set.range ((↑) : ↥K'' → LaurentSeries L) := by
  classical

  have hpP : p.Prime := Fact.out
  have hℓg3 : 3 < ℓg := by omega
  have hℓg3' : 3 ≤ ℓg := by omega
  have hξq : IsPrimitiveRoot ζ ℓg := hζ
  have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hpP.ne_zero
  have hcard : ((Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)).card = ModularCurve.gamma0PowDeg p k :=
    card_filter_not_dvd_eq_gamma0PowDeg p k
  set d : ℕ := ModularCurve.gamma0PowDeg p k with hd
  set ξu : Lˣ := (hζ.isUnit hℓg.ne_zero).unit with hξu
  have hξu_val : (ξu : L) = ζ := (hζ.isUnit hℓg.ne_zero).unit_spec

  set X₁ : LaurentSeries L := (toricPoint L 1 ζ).1 with hX₁
  set X₂ : LaurentSeries L := (toricPoint L 1 (ζ ^ 2)).1 with hX₂
  set U : LaurentSeries L := ((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) with hU
  set Ui : LaurentSeries L := ((C.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) with hUi
  have hUUi : U * Ui = 1 := by rw [hU, hUi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcusp1 : ((⟨(ModularCurve.tateToricPoint L 1 ξu).1, (ModularCurve.tateToricPoint L 1 ξu).2,
        (ModularCurve.tateToricPoint L 1 (ξu ^ 2)).1, (ModularCurve.tateToricPoint L 1 (ξu ^ 2)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xP = Ui ^ 2 * (X₁ - C.r) := by
    rw [LevelPData.variableChange_xP]
    dsimp only
    rw [tateToricPoint_eq_toricPoint, hξu_val]
  have hcusp2 : ((⟨(ModularCurve.tateToricPoint L 1 ξu).1, (ModularCurve.tateToricPoint L 1 ξu).2,
        (ModularCurve.tateToricPoint L 1 (ξu ^ 2)).1, (ModularCurve.tateToricPoint L 1 (ξu ^ 2)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xQ = Ui ^ 2 * (X₂ - C.r) := by
    rw [LevelPData.variableChange_xQ]
    dsimp only
    rw [tateToricPoint_eq_toricPoint, Units.val_pow_eq_pow_val, hξu_val]
  rw [hcusp1] at hx₁
  rw [hcusp2] at hx₂
  obtain ⟨k₁, hk₁⟩ := hx₁
  obtain ⟨k₂, hk₂⟩ := hx₂

  set D : LaurentSeries L := X₁ - X₂ with hD
  have hD0 : D ≠ 0 := sub_ne_zero.mpr (toricPoint_fst_ne_of_isPrimitiveRoot 1 ℓg hℓg3 ζ hξq)
  set κ : ↥K'' := k₁ - k₂ with hκ
  have hκval : (κ : LaurentSeries L) = Ui ^ 2 * D := by
    rw [hκ]
    change (k₁ : LaurentSeries L) - k₂ = Ui ^ 2 * D
    rw [hk₁, hk₂, hD]; ring
  have hUi0 : Ui ≠ 0 := Units.ne_zero _
  have hκ0 : (κ : LaurentSeries L) ≠ 0 := by
    rw [hκval]; exact mul_ne_zero (pow_ne_zero 2 hUi0) hD0
  have hκ0' : κ ≠ 0 := fun h0 => hκ0 (by rw [h0]; rfl)
  have hUi2 : Ui ^ 2 = (κ : LaurentSeries L) * D⁻¹ := by
    rw [hκval, mul_assoc, mul_inv_cancel₀ hD0, mul_one]
  have hU2 : U ^ 2 = D * (κ : LaurentSeries L)⁻¹ := by
    have h1 : U ^ 2 * Ui ^ 2 = 1 := by rw [← mul_pow, hUUi, one_pow]
    rw [hUi2] at h1
    rw [eq_inv_of_mul_eq_one_left h1, mul_inv, inv_inv, mul_comm]
  have hr : C.r = X₁ - U ^ 2 * (k₁ : LaurentSeries L) := by
    have h1 : U ^ 2 * (k₁ : LaurentSeries L) = X₁ - C.r := by
      rw [hk₁, ← mul_assoc, ← mul_pow, hUUi, one_pow, one_mul]
    linear_combination h1

  set ht : (LaurentSeries L)[X] := h.comp (X + Polynomial.C X₁) with hht
  have hh_ht : h = ht.comp (X - Polynomial.C X₁) := by
    rw [hht, Polynomial.comp_assoc]
    simp
  set n : ℕ := ht.natDegree with hn
  set b : ℕ → LaurentSeries L := fun m => ht.coeff m with hb
  set G : ℕ → LaurentSeries L := fun m => b m * D ^ m * D⁻¹ ^ d with hG

  have hexp : kernelVariableChangeDeg C d h =
      ∑ m ∈ Finset.range (n + 1), Polynomial.C (Ui ^ (2 * d) * b m * U ^ (2 * m)) *
        (X - Polynomial.C (k₁ : LaurentSeries L)) ^ m := by
    unfold kernelVariableChangeDeg
    rw [← hUi, ← hU]
    conv_lhs => rw [hh_ht, Polynomial.comp_assoc]
    have hlin : (X - Polynomial.C X₁).comp (Polynomial.C U ^ 2 * X + Polynomial.C C.r) =
        Polynomial.C (U ^ 2) * (X - Polynomial.C (k₁ : LaurentSeries L)) := by
      rw [sub_comp, X_comp, C_comp, hr]
      simp only [map_sub, map_mul, map_pow]
      ring
    rw [hlin]
    conv_lhs => rw [ht.as_sum_range_C_mul_X_pow]
    rw [← hn]
    rw [finset_sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comp, C_comp, X_pow_comp, mul_pow, ← Polynomial.C_pow]
    simp only [← mul_assoc, ← Polynomial.C_mul]
    congr 2
    rw [hb]
    ring

  have hGmem : ∀ m : ℕ, G m ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) := by

    obtain ⟨ι, hιξ'⟩ := hιζ
    have hιinj : Function.Injective ι := ι.injective

    set ε : ℂ := Complex.exp (2 * Real.pi * Complex.I / ℓg) with hε
    have htε : ε ^ 1 = ι ζ := by rw [pow_one, hιξ']
    have htcop : (1 : ℕ).Coprime ℓg := Nat.coprime_one_left _

    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p ^ k : ℕ)) with hζ
    have hζprim : IsPrimitiveRoot ζ (p ^ k) := Complex.isPrimitiveRoot_exp (p ^ k) hpk0
    set Xc : ℂ → LaurentSeries ℂ := fun u => (toricPoint ℂ 1 u).1 with hXc
    have hX₁c : coeffMap ι X₁ = Xc (ε ^ 1) := by rw [hX₁, coeffMap_toricPoint_fst, htε]
    have hX₂c : coeffMap ι X₂ = Xc (ε ^ (2 * 1)) := by
      rw [hX₂, coeffMap_toricPoint_fst, map_pow, ← htε, ← pow_mul, Nat.mul_comm 1 2]
    have hDc : coeffMap ι D = Xc (ε ^ 1) - Xc (ε ^ (2 * 1)) := by rw [hD, map_sub, hX₁c, hX₂c]
    have hht_map : ht.map (coeffMap ι) =
        ∏ k ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
          (X - Polynomial.C (Xc (ζ ^ k) - Xc (ε ^ 1))) := by
      rw [hht, Polynomial.map_comp, hh ℂ ι ζ hζprim, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
        hX₁c, finset_prod_comp]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [sub_comp, X_comp, C_comp, map_sub]
      ring

    have hEc : ∀ c : ℕ, ht.eval ((c : LaurentSeries L) * D) * D⁻¹ ^ d ∈
        Set.range ((↑) : ↥K'' → LaurentSeries L) := by
      intro c
      obtain ⟨Φ, Ψ, a, ha0, hΨq, hΦq⟩ :=
        ModularCurve.FullLevel.Diamond.exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker
          M' ℓg hℓg3' hℓgM' (ZMod.unitsMap hℓgM').ker rfl p k hpk 1 htcop (c : ℚ)

      have hΨq' : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Ψ) =
          HahnSeries.C (a : ℂ) * coeffMap ι (D ^ d) := by
        rw [hΨq, map_pow, hDc, HahnSeries.C_mul_eq_smul, hcard]
      have hprod : (∏ k ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
            (((c : ℚ) : ℂ) • (Xc (ε ^ 1) - Xc (ε ^ (2 * 1))) - (Xc (ζ ^ k) - Xc (ε ^ 1)))) =
          coeffMap ι (ht.eval ((c : LaurentSeries L) * D)) := by
        rw [← Polynomial.eval_map_apply, hht_map, Polynomial.eval_prod]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, map_mul, map_natCast, hDc,
          Rat.cast_natCast, ← HahnSeries.C_mul_eq_smul, map_natCast]
      have hΦq' : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Φ) =
          HahnSeries.C (a : ℂ) * coeffMap ι (ht.eval ((c : LaurentSeries L) * D)) := by
        rw [hΦq, ← hprod, HahnSeries.C_mul_eq_smul]

      have hcoefΨ : ∀ n' : ℕ, (PowerSeries.coeff n') (UpperHalfPlane.qExpansion 1 ⇑Ψ) ∈ Set.range ⇑ι := by
        intro n'
        have := congrArg (fun x : LaurentSeries ℂ => x.coeff (n' : ℤ)) hΨq'
        simp only [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
          coeffMap_coeff, smul_eq_mul] at this
        rw [this]
        exact ⟨(a : L) * (D ^ d).coeff n', by rw [map_mul, map_ratCast]⟩
      have hcoefΦ : ∀ n' : ℕ, (PowerSeries.coeff n') (UpperHalfPlane.qExpansion 1 ⇑Φ) ∈ Set.range ⇑ι := by
        intro n'
        have := congrArg (fun x : LaurentSeries ℂ => x.coeff (n' : ℤ)) hΦq'
        simp only [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
          coeffMap_coeff, smul_eq_mul] at this
        rw [this]
        exact ⟨(a : L) * (ht.eval ((c : LaurentSeries L) * D)).coeff n', by rw [map_mul, map_ratCast]⟩

      have hΨ0 : Ψ ≠ 0 := by
        intro hΨ
        have hq0 : UpperHalfPlane.qExpansion 1 ⇑Ψ = 0 :=
          (ModularForm.qExpansion_eq_zero_iff one_pos
            (one_mem_strictPeriods_GammaH M' (ZMod.unitsMap hℓgM').ker) Ψ).mpr hΨ
        rw [hq0, map_zero] at hΨq'
        have : HahnSeries.C (a : ℂ) * coeffMap ι (D ^ d) ≠ 0 := by
          refine mul_ne_zero (HahnSeries.C_ne_zero (by exact_mod_cast ha0)) ?_
          rw [Ne, ← map_zero (coeffMap ι), (coeffMap_injective ι hιinj).eq_iff]
          exact pow_ne_zero d hD0
        exact this hΨq'.symm

      obtain ⟨y, hyK, hy⟩ :=
        ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
          M' (ZMod.unitsMap hℓgM').ker Φ Ψ hΨ0 L ι hcoefΦ hcoefΨ
      rw [hΨq', hΦq', mul_left_comm, ← map_mul] at hy
      have hy' : coeffMap ι (y * D ^ d) = coeffMap ι (ht.eval ((c : LaurentSeries L) * D)) :=
        mul_left_cancel₀ (HahnSeries.C_ne_zero (by exact_mod_cast ha0 : (a : ℂ) ≠ 0)) hy
      have hy'' : y * D ^ d = ht.eval ((c : LaurentSeries L) * D) := coeffMap_injective ι hιinj hy'
      subst hK''
      refine ⟨⟨y, hyK⟩, ?_⟩
      show y = ht.eval ((c : LaurentSeries L) * D) * D⁻¹ ^ d
      rw [← hy'', inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hD0), mul_one]

    intro m
    set P : (LaurentSeries L)[X] := ∑ m ∈ Finset.range (n + 1), Polynomial.C (G m) * X ^ m with hP
    have hPcoeff : ∀ m, P.coeff m = if m < n + 1 then G m else 0 := by
      intro m
      rw [hP, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq (Finset.range (n + 1)) m]
      simp [Finset.mem_range]
    have hPdeg : P.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [hPcoeff, if_neg (by omega)]
    have hPeval : ∀ c : ℕ, P.eval (c : LaurentSeries L) = ht.eval ((c : LaurentSeries L) * D) * D⁻¹ ^ d := by
      intro c
      rw [hP, Polynomial.eval_finsetSum]
      conv_rhs => rw [ht.as_sum_range_C_mul_X_pow, ← hn, Polynomial.eval_finsetSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, hG, hb]
      ring_nf
    haveI : CharZero (LaurentSeries L) :=
      charZero_of_injective_algebraMap (algebraMap L (LaurentSeries L)).injective
    by_cases hm : m < n + 1
    · have := coeff_mem_range_of_eval_natCast_mem_range (algebraMap (↥K'') (LaurentSeries L)) P n hPdeg
        (fun c _ => by rw [hPeval]; exact hEc c) m
      rwa [hPcoeff, if_pos hm] at this
    ·
      have hbm : b m = 0 := by
        rw [hb]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      refine ⟨0, ?_⟩
      rw [hG]
      simp [hbm]

  intro i
  rw [hexp, Polynomial.finsetSum_coeff]

  have hterm : ∀ m ∈ Finset.range (n + 1),
      (Polynomial.C (Ui ^ (2 * d) * b m * U ^ (2 * m)) *
        (X - Polynomial.C (k₁ : LaurentSeries L)) ^ m) ∈ Polynomial.lifts (algebraMap (↥K'') (LaurentSeries L)) := by
    intro m hm
    obtain ⟨g, hg⟩ := hGmem m
    have hscal : Ui ^ (2 * d) * b m * U ^ (2 * m) =
        ((κ ^ d * κ⁻¹ ^ m * g : ↥K'') : LaurentSeries L) := by
      rw [pow_mul, pow_mul, hUi2, hU2]
      push_cast
      rw [hg, hG]
      simp only
      ring_nf
    rw [Polynomial.lifts_iff_liftsRing]
    refine Subring.mul_mem _ ?_ (Subring.pow_mem _ (Subring.sub_mem _ ?_ ?_) _)
    · rw [← Polynomial.lifts_iff_liftsRing, hscal]
      exact Polynomial.C_mem_lifts (algebraMap (↥K'') (LaurentSeries L)) (κ ^ d * κ⁻¹ ^ m * g)
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.X_mem_lifts _
    · rw [← Polynomial.lifts_iff_liftsRing]
      exact Polynomial.C_mem_lifts (algebraMap (↥K'') (LaurentSeries L)) k₁
  have hsum := Subsemiring.sum_mem (Polynomial.lifts (algebraMap (↥K'') (LaurentSeries L))) hterm
  obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts _).mp hsum i
  refine ⟨y, ?_⟩
  rw [← Polynomial.finsetSum_coeff]
  exact hy

end
end S_ModularCurve_FullLevel_Diamond_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker (solution)
