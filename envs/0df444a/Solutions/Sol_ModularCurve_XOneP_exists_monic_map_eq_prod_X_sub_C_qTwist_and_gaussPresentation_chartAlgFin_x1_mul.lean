-- Prove2me | solution 1 for ModularCurve.XOneP.exists_monic_map_eq_prod_X_sub_C_qTwist_and_gaussPresentation_chartAlgFin_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/caed6c78-6884-5abe-9ddb-ab03e24e96d4

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_and_gaussPresentation_chartAlgFin_x1_mul
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open AlgebraicCurve Polynomial

namespace K1C

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_injective HahnSeries"

variable {A B : Type*} [CommRing A] [CommRing B]

theorem coeffMap_qExpand (f : A →+* B) (N : ℕ) [NeZero N] (x : LaurentSeries A) :
    coeffMap f (qExpand A N x) = qExpand B N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ hk, qExpand_coeff_of_not_dvd _ _ hk, map_zero]

theorem coeffMap_qTwist (f : A →+* B) (u : Aˣ) (x : LaurentSeries A) :
    coeffMap f (qTwist u x) = qTwist (Units.map (f : A →* B) u) (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul, ← map_zpow, Units.coe_map,
    MonoidHom.coe_coe]

theorem coeffMap_injective {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem coeffMap_ofPowerSeries (f : A →+* B) (g : PowerSeries A) :
    coeffMap f (g : LaurentSeries A) = ((PowerSeries.map f g : PowerSeries B) : LaurentSeries B) := by
  ext k
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [map_zero]
  · rw [PowerSeries.coeff_map]

theorem qExpand_ofPowerSeries (p : ℕ) [NeZero p] (g : PowerSeries A) :
    qExpand A p (g : LaurentSeries A) =
      ((PowerSeries.expand p (NeZero.ne p) g : PowerSeries A) : LaurentSeries A) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  ext k
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    by_cases hm : m < 0
    · rw [if_pos hm, if_pos (mul_neg_of_pos_of_neg hp0 hm)]
    · have h0 : ¬ (p : ℤ) * m < 0 := by
        push Not at hm ⊢
        positivity
      rw [if_neg hm, if_neg h0, Int.natAbs_mul, Int.natAbs_natCast, PowerSeries.coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd _ _ hk, PowerSeries.coeff_coe]
    split_ifs with h
    · rfl
    · rw [PowerSeries.coeff_expand_of_not_dvd]
      rwa [Int.natCast_dvd] at hk

theorem pow_eq_qExpand_coeffMap_frobenius (p : ℕ) [Fact p.Prime] [CharP B p]
    (y : LaurentSeries B) :
    y ^ p = qExpand B p (coeffMap (frobenius B p) y) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  conv_lhs => rw [← y.single_order_mul_powerSeriesPart]
  conv_rhs => rw [← y.single_order_mul_powerSeriesPart]
  rw [mul_pow, map_mul, map_mul, coeffMap_single, (frobenius B p).map_one, qExpand_single, single_pow,
    one_pow, nsmul_eq_mul, coeffMap_ofPowerSeries, qExpand_ofPowerSeries, ← PowerSeries.map_expand]
  congr 1
  rw [← map_pow]
  congr 1
  exact (MvPowerSeries.map_frobenius_expand p (NeZero.ne p)).symm

theorem exists_gaussPresentation_of_coeffMap_residue_eq_zero [IsLocalRing A] (f : A →+* B)
    (w : LaurentSeries A) (hw : coeffMap (IsLocalRing.residue A) w = 0) :
    ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ x.map (IsLocalRing.residue A) = 0 ∧
      coeffMap f w * ofPowerSeries ℤ B (y.map f) = ofPowerSeries ℤ B (x.map f) := by
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : PowerSeries A)) w
  have hx' : w * ofPowerSeries ℤ A (PowerSeries.X ^ n) = ofPowerSeries ℤ A x := by
    simpa only [LaurentSeries.coe_algebraMap] using hx
  refine ⟨x, PowerSeries.X ^ n, ?_, ?_, ?_⟩
  · rw [map_pow, PowerSeries.map_X]
    exact pow_ne_zero n PowerSeries.X_ne_zero
  · apply (HahnSeries.ofPowerSeries_injective : Function.Injective (ofPowerSeries ℤ (IsLocalRing.ResidueField A)))
    rw [map_zero, ← coeffMap_ofPowerSeries, ← hx', map_mul, hw, zero_mul]
  · rw [← coeffMap_ofPowerSeries, ← coeffMap_ofPowerSeries, ← map_mul, hx']

end K1C

p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_injective" in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hβdef : letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.HeckeBetaOneDefined (M * p) p)
    (hdeg : letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L (M * p) p) = p)
    (g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ E : Polynomial ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      E.Monic ∧ E.natDegree = p ∧
      E.map ((ModularCurve.qExpand L p).comp
          ((algebraMap ↥K (LaurentSeries L)).comp
            (algebraMap ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ↥K))) =
        ∏ i : Fin p, (Polynomial.X - Polynomial.C
          (ModularCurve.qTwist (ζ ^ (i : ℕ)) (((g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L))) ∧
      (∀ k : ℕ, 0 < k → k < p →
        (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ x.map (IsLocalRing.residue A) = 0 ∧
          (((E.coeff k : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) *
              HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
            HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))) ∧
      (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧ x.map (IsLocalRing.residue A) = 0 ∧
          ((((E.coeff 0 - (-1) ^ p * g) : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) *
              HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
            HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨E, hmon, hdegE, hmap⟩ :=
    ModularCurve.XOneP.exists_monic_map_eq_prod_X_sub_C_qTwist_chartAlgFin_x1_mul p M L ζ hζ K hK A hAp hζA
      j hj hβdef hdeg g

  have hK' : K = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 (M * p))) := hK
  have hint := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartModel_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p)) L K hK' A j hj).1
  set f : A →+* L := algebraMap A L with hf_def
  have hf : Function.Injective f := IsFractionRing.injective A L
  choose e he using fun k : ℕ => hint (E.coeff k)
  obtain ⟨g₀, hg₀⟩ := hint g

  obtain ⟨z, hz⟩ := hζA
  have hzp : z ^ p = 1 := hf (by rw [map_pow, map_one]; exact hz.symm ▸ (by exact_mod_cast hζ.pow_eq_one))
  have hzmul : z * z ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le, hzp]
  set zu : Aˣ := Units.mkOfMulEqOne z (z ^ (p - 1)) hzmul with hzu_def
  have hzu : Units.map (f : A →* L) zu = ζ := Units.ext (by
    rw [Units.coe_map, MonoidHom.coe_coe, hzu_def, Units.val_mkOfMulEqOne, hz])

  set PA : Polynomial (LaurentSeries A) :=
    ∏ i : Fin p, (X - C (ModularCurve.qTwist (zu ^ (i : ℕ)) g₀)) with hPA_def
  have hPA : PA.map (ModularCurve.coeffMap f) =
      ∏ i : Fin p, (Polynomial.X - Polynomial.C
        (ModularCurve.qTwist (ζ ^ (i : ℕ))
          (((g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L))) := by
    rw [hPA_def, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, K1C.coeffMap_qTwist, map_pow, hzu, hg₀]

  have hcoefA : ∀ k : ℕ, ModularCurve.qExpand A p (e k) = PA.coeff k := by
    intro k
    apply K1C.coeffMap_injective hf
    rw [K1C.coeffMap_qExpand, he, ← Polynomial.coeff_map, hPA, ← hmap, Polynomial.coeff_map]
    rfl

  let kA := IsLocalRing.ResidueField A
  let π : A →+* kA := IsLocalRing.residue A
  haveI : CharP kA p := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A p hAp
  haveI : CharP (LaurentSeries kA) p :=
    charP_of_injective_algebraMap (algebraMap kA (LaurentSeries kA)).injective p
  have hFrobπ : (frobenius kA p).comp π = π := by
    refine RingHom.ext fun a => ?_
    obtain ⟨n, hn⟩ :=
      IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp (π a)
    rw [RingHom.comp_apply, ← hn, eq_intCast, map_intCast]
  have hπz : π z = 1 := by
    have h1 : frobenius kA p (π z) = π z := RingHom.congr_fun hFrobπ z
    rw [frobenius_def, ← map_pow, hzp, map_one] at h1
    exact h1.symm
  have hπzu : Units.map (π : A →* kA) zu = 1 := Units.ext (by
    rw [Units.coe_map, MonoidHom.coe_coe, hzu_def, Units.val_mkOfMulEqOne, hπz, Units.val_one])
  set ψ := ModularCurve.coeffMap π with hψ_def
  have hPAπ : PA.map ψ = Polynomial.X ^ p - Polynomial.C (ModularCurve.qExpand kA p (ψ g₀)) := by
    rw [hPA_def, Polynomial.map_prod]
    have hfac : ∀ i : Fin p,
        (Polynomial.X - Polynomial.C (ModularCurve.qTwist (zu ^ (i : ℕ)) g₀)).map ψ =
          Polynomial.X - Polynomial.C (ψ g₀) := fun i => by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hψ_def, K1C.coeffMap_qTwist, map_pow, hπzu,
        one_pow, ModularCurve.qTwist_one_apply]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      sub_pow_char _ _, ← map_pow, K1C.pow_eq_qExpand_coeffMap_frobenius p (ψ g₀), hψ_def,
      ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_congr hFrobπ]
  have hcoefπ : ∀ k : ℕ, ModularCurve.qExpand kA p (ψ (e k)) =
      (Polynomial.X ^ p - Polynomial.C (ModularCurve.qExpand kA p (ψ g₀)) :
        Polynomial (LaurentSeries kA)).coeff k := by
    intro k
    rw [hψ_def, ← K1C.coeffMap_qExpand, hcoefA, ← Polynomial.coeff_map, ← hψ_def, hPAπ]
  have hmid : ∀ k : ℕ, 0 < k → k < p → ψ (e k) = 0 := by
    intro k hk0 hkp
    have h := hcoefπ k
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hkp.ne, Polynomial.coeff_C, if_neg hk0.ne',
      sub_zero, ← (ModularCurve.qExpand kA p).map_zero] at h
    exact ModularCurve.qExpand_injective p h
  have hzero : ψ (e 0) = -ψ g₀ := by
    have h := hcoefπ 0
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (NeZero.ne p).symm, Polynomial.coeff_C_zero,
      zero_sub, ← map_neg] at h
    exact ModularCurve.qExpand_injective p h

  refine ⟨E, hmon, hdegE, hmap, ?_, ?_⟩
  · intro k hk0 hkp
    obtain ⟨x, y, hy, hx, hxy⟩ :=
      K1C.exists_gaussPresentation_of_coeffMap_residue_eq_zero f (e k) (hmid k hk0 hkp)
    refine ⟨x, y, hy, hx, ?_⟩
    rw [← he]
    exact hxy
  · have hw : ψ (e 0 - (-1) ^ p * g₀) = 0 := by
      rw [map_sub, map_mul, map_pow, map_neg, map_one, hzero, neg_one_pow_char _ p]
      ring
    obtain ⟨x, y, hy, hx, hxy⟩ := K1C.exists_gaussPresentation_of_coeffMap_residue_eq_zero f _ hw
    refine ⟨x, y, hy, hx, ?_⟩
    rw [map_sub, map_mul, map_pow, map_neg, map_one, he, hg₀] at hxy
    have hcoe : ((((E.coeff 0 - (-1) ^ p * g) : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) :
          LaurentSeries L) =
        (((E.coeff 0 : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) -
          (-1) ^ p * (((g : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) := by
      push_cast
      ring
    rw [hcoe]
    exact hxy

end S_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_and_gaussPresentation_chartAlgFin_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_monic_map_eq_prod_X_sub_C_qTwist_and_gaussPresentation_chartAlgFin_x1_mul (solution)
