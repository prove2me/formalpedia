-- Prove2me | solution 1 for ModularCurve.exists_monic_int_relation_modularUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/83468fde-0d52-5cc9-a0c0-e8119385a4eb

import Theorems.Thm_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monic_int_relation_modularUnit
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
noncomputable section
open HahnSeries Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "exists_monic_rat_relation_int_coeff_modularUnit IsMonicOfOrder IsMonicOfOrder.single IsMonicOfOrder.ofPowerSeries dedekindEtaUnitQ deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries qExpand dedekindEtaUnit constantCoeff_jNumQ jqModC map_jqModC coeffMap coeffMap_coeff coeffMap_single coeffMap_ofPowerSeries coeffMap_qExpand"
p2m_open "ModularCurve"

namespace QDescent

theorem isMonicOfOrder_jqModC : IsMonicOfOrder (jqModC ℚ) (-1) := by
  have h := (IsMonicOfOrder.single (-1 : ℤ)).mul (IsMonicOfOrder.ofPowerSeries constantCoeff_jNumQ)
  rw [add_zero] at h
  exact h

theorem isMonicOfOrder_jqModC_pow (d : ℕ) : IsMonicOfOrder (jqModC ℚ ^ d) (-(d : ℤ)) := by
  induction d with
  | zero =>
      rw [pow_zero, Nat.cast_zero, neg_zero, ← HahnSeries.single_zero_one]
      exact IsMonicOfOrder.single 0
  | succ d ih =>
      have h := ih.mul isMonicOfOrder_jqModC
      have e : -(d : ℤ) + -1 = -((d + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [← pow_succ, e] at h
      exact h

theorem aeval_map_intCast (T : Polynomial ℤ) :
    aeval (jqModC ℚ) (T.map (Int.castRingHom ℚ)) = coeffMap (Int.castRingHom ℚ) (aeval (jqModC ℤ) T) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂,
    show coeffMap (Int.castRingHom ℚ) (jqModC ℤ) = jqModC ℚ from map_jqModC (Int.castRingHom ℚ),
    RingHom.ext_int ((algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ))
      ((coeffMap (Int.castRingHom ℚ)).comp (algebraMap ℤ (LaurentSeries ℤ)))]

theorem coeff_aeval_neg (S : Polynomial ℚ) {d : ℕ} (hS : S.natDegree ≤ d) :
    (aeval (jqModC ℚ) S).coeff (-(d : ℤ)) = S.coeff d := by
  have hlow : ∀ i ∈ Finset.range d, (HahnSeries.C (S.coeff i) * jqModC ℚ ^ i).coeff (-(d : ℤ)) = 0 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
      (isMonicOfOrder_jqModC_pow i).coeff_of_lt (by omega), mul_zero]
  rw [aeval_def, eval₂_eq_sum_range' (algebraMap ℚ (LaurentSeries ℚ)) (Nat.lt_succ_of_le hS),
    RingHom.ext_rat (algebraMap ℚ (LaurentSeries ℚ)) (HahnSeries.C : ℚ →+* LaurentSeries ℚ), HahnSeries.coeff_sum,
    Finset.sum_range_succ, Finset.sum_eq_zero hlow, zero_add, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    (isMonicOfOrder_jqModC_pow d).coeff_self, mul_one]

theorem exists_map_eq_of_degree_lt (d : ℕ) : ∀ S : Polynomial ℚ, S.degree < d →
    (∀ k : ℤ, ∃ m : ℤ, (aeval (jqModC ℚ) S).coeff k = (m : ℚ)) →
      ∃ T : Polynomial ℤ, T.map (Int.castRingHom ℚ) = S := by
  induction d with
  | zero =>
      intro S hS _
      rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hS
      exact ⟨0, by rw [hS, Polynomial.map_zero]⟩
  | succ d ih =>
      intro S hS hint
      have hcoef : ∀ n : ℕ, d + 1 ≤ n → S.coeff n = 0 := (degree_lt_iff_coeff_zero S (d + 1)).mp hS
      have hdeg : S.natDegree ≤ d := by
        rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
        intro n hn
        exact hcoef n (Nat.succ_le_of_lt (by exact_mod_cast hn))
      obtain ⟨m, hm⟩ := hint (-(d : ℤ))
      have hSd : S.coeff d = (m : ℚ) := by rw [← coeff_aeval_neg S hdeg]; exact hm
      have hmap : (Polynomial.C m * X ^ d : Polynomial ℤ).map (Int.castRingHom ℚ) = Polynomial.C (m : ℚ) * X ^ d := by
        rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, map_X, eq_intCast]
      have hS' : (S - Polynomial.C (m : ℚ) * X ^ d).degree < (d : WithBot ℕ) := by
        rw [degree_lt_iff_coeff_zero]
        intro k hk
        rw [Polynomial.coeff_sub, coeff_C_mul_X_pow]
        split_ifs with h
        · rw [h, hSd, sub_self]
        · rw [hcoef k (by omega), sub_zero]
      have hint' : ∀ k : ℤ, ∃ m' : ℤ, (aeval (jqModC ℚ) (S - Polynomial.C (m : ℚ) * X ^ d)).coeff k = (m' : ℚ) := by
        intro k
        obtain ⟨a, ha⟩ := hint k
        refine ⟨a - (aeval (jqModC ℤ) (Polynomial.C m * X ^ d)).coeff k, ?_⟩
        rw [map_sub, HahnSeries.coeff_sub, ha, ← hmap, aeval_map_intCast, coeffMap_coeff, Int.cast_sub, eq_intCast]
      obtain ⟨T, hT⟩ := ih _ hS' hint'
      exact ⟨T + Polynomial.C m * X ^ d, by rw [Polynomial.map_add, hT, hmap, sub_add_cancel]⟩

end QDescent

end ModularCurve

end

namespace ModularCurve p2m_export "ModularCurve" "exists_monic_rat_relation_int_coeff_modularUnit IsMonicOfOrder IsMonicOfOrder.single IsMonicOfOrder.ofPowerSeries dedekindEtaUnitQ deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries qExpand dedekindEtaUnit constantCoeff_jNumQ jqModC map_jqModC coeffMap coeffMap_coeff coeffMap_single coeffMap_ofPowerSeries coeffMap_qExpand" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.exists_int_polynomial_of_aeval_jqModC_coeff_int (S : Polynomial ℚ)
    (h : ∀ k : ℤ, ∃ m : ℤ, (Polynomial.aeval (ModularCurve.jqModC ℚ) S).coeff k = (m : ℚ)) :
    ∃ T : Polynomial ℤ, T.map (Int.castRingHom ℚ) = S :=
  ModularCurve.QDescent.exists_map_eq_of_degree_lt (S.natDegree + 1) S
    (lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self S.natDegree)) h

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.coeffMap_intCast_aeval_jqModC (T : Polynomial ℤ) :
    ModularCurve.coeffMap (Int.castRingHom ℚ) (Polynomial.aeval (ModularCurve.jqModC ℤ) T) =
      Polynomial.aeval (ModularCurve.jqModC ℚ) (T.map (Int.castRingHom ℚ)) :=
  (ModularCurve.QDescent.aeval_map_intCast T).symm

namespace WZDev

private theorem coeffMap_int_rat_injective :
    Function.Injective (ModularCurve.coeffMap (Int.castRingHom ℚ)) := by
  intro x y h
  ext k
  have hk : (ModularCurve.coeffMap (Int.castRingHom ℚ) x).coeff k =
      (ModularCurve.coeffMap (Int.castRingHom ℚ) y).coeff k := by rw [h]
  rw [ModularCurve.coeffMap_coeff, ModularCurve.coeffMap_coeff] at hk
  exact Int.cast_injective hk

end WZDev

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.solution_impl (p : ℕ) [Fact p.Prime] :
    ∃ (n : ℕ) (S : Fin n → Polynomial ℤ),
      (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit) ^ n +
        ∑ i : Fin n, Polynomial.aeval (ModularCurve.jqModC ℤ) (S i) *
          ((HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit) ^ (i : ℕ) *
            (ModularCurve.qExpand ℤ p (HahnSeries.single (1 : ℤ) 1 *
              HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit)) ^ (n - (i : ℕ))) = 0 := by
  obtain ⟨n, S, hrel, hint⟩ := ModularCurve.exists_monic_rat_relation_int_coeff_modularUnit p
  choose T hT using fun i =>
    ModularCurve.exists_int_polynomial_of_aeval_jqModC_coeff_int (S i) (hint i)
  refine ⟨n, T, ?_⟩
  set ι : ℤ →+* ℚ := Int.castRingHom ℚ with hι

  have hΔ : ModularCurve.coeffMap ι (HahnSeries.single (1 : ℤ) 1 *
      HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit) = ModularCurve.deltaSeries := by
    rw [map_mul, ModularCurve.coeffMap_single, ModularCurve.coeffMap_ofPowerSeries, map_one,
      ModularCurve.deltaSeries, ModularCurve.dedekindEtaUnitQ]
  have hj : ModularCurve.coeffMap ι (ModularCurve.jqModC ℤ) = ModularCurve.jqModC ℚ := by
    have hcomp : (Int.castRingHom ℚ) = ι.comp (Int.castRingHom ℤ) := RingHom.ext_int _ _
    rw [ModularCurve.jqModC, ModularCurve.jqModC, map_mul, ModularCurve.coeffMap_single,
      ModularCurve.coeffMap_ofPowerSeries, map_one, hcomp, PowerSeries.map_comp,
      RingHom.comp_apply]
  have haeval : ∀ i : Fin n,
      ModularCurve.coeffMap ι (Polynomial.aeval (ModularCurve.jqModC ℤ) (T i)) =
        Polynomial.aeval (ModularCurve.jqModC ℚ) (S i) := by
    intro i
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hj]
    rw [← hT i, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext_int _ _

  have hB := ModularCurve.deltaSeriesN_ne_zero p
  have hu : ModularCurve.modularUnitSeries p =
      ModularCurve.deltaSeries * (ModularCurve.deltaSeriesN p)⁻¹ := rfl
  have hexp : ∀ i : Fin n, ModularCurve.modularUnitSeries p ^ (i : ℕ) *
      ModularCurve.deltaSeriesN p ^ n =
      ModularCurve.deltaSeries ^ (i : ℕ) * ModularCurve.deltaSeriesN p ^ (n - (i : ℕ)) := by
    intro i
    have hni : (i : ℕ) + (n - (i : ℕ)) = n := Nat.add_sub_cancel' i.isLt.le
    calc ModularCurve.modularUnitSeries p ^ (i : ℕ) * ModularCurve.deltaSeriesN p ^ n
        = ModularCurve.deltaSeries ^ (i : ℕ) * (ModularCurve.deltaSeriesN p)⁻¹ ^ (i : ℕ) *
          (ModularCurve.deltaSeriesN p ^ (i : ℕ) * ModularCurve.deltaSeriesN p ^ (n - (i : ℕ))) := by
          rw [hu, mul_pow, ← pow_add, hni]
      _ = ModularCurve.deltaSeries ^ (i : ℕ) *
          (((ModularCurve.deltaSeriesN p)⁻¹ * ModularCurve.deltaSeriesN p) ^ (i : ℕ)) *
          ModularCurve.deltaSeriesN p ^ (n - (i : ℕ)) := by
          rw [mul_pow ((ModularCurve.deltaSeriesN p)⁻¹) (ModularCurve.deltaSeriesN p)]; ring
      _ = ModularCurve.deltaSeries ^ (i : ℕ) * ModularCurve.deltaSeriesN p ^ (n - (i : ℕ)) := by
          rw [inv_mul_cancel₀ hB, one_pow, mul_one]
  have hlead : ModularCurve.modularUnitSeries p ^ n * ModularCurve.deltaSeriesN p ^ n =
      ModularCurve.deltaSeries ^ n := by
    rw [hu, mul_pow, mul_assoc, ← mul_pow, inv_mul_cancel₀ hB, one_pow, mul_one]
  have hhom : ModularCurve.deltaSeries ^ n + ∑ i : Fin n,
      Polynomial.aeval (ModularCurve.jqModC ℚ) (S i) *
        (ModularCurve.deltaSeries ^ (i : ℕ) * ModularCurve.deltaSeriesN p ^ (n - (i : ℕ))) = 0 := by
    have h0 : (ModularCurve.modularUnitSeries p ^ n + ∑ i : Fin n,
        Polynomial.aeval (ModularCurve.jqModC ℚ) (S i) *
          ModularCurve.modularUnitSeries p ^ (i : ℕ)) * ModularCurve.deltaSeriesN p ^ n = 0 := by
      rw [hrel, zero_mul]
    rw [add_mul, Finset.sum_mul, hlead] at h0
    rw [← h0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, hexp]

  apply WZDev.coeffMap_int_rat_injective
  rw [map_zero, map_add, map_pow, map_sum, hΔ]
  rw [show ∀ x : LaurentSeries ℚ, ModularCurve.deltaSeries ^ n + x = 0 ↔
      ModularCurve.deltaSeries ^ n + x = 0 from fun _ => Iff.rfl]
  rw [← hhom]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, hΔ, haeval i, ModularCurve.coeffMap_qExpand, hΔ]
  rfl

theorem solution (p : ℕ) [Fact p.Prime] :
    ∃ (n : ℕ) (S : Fin n → Polynomial ℤ), (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit) ^ n + ∑ i : Fin n, Polynomial.aeval (ModularCurve.jqModC ℤ) (S i) * ((HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit) ^ (i : ℕ) * (ModularCurve.qExpand ℤ p (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.dedekindEtaUnit)) ^ (n - (i : ℕ))) = 0 :=
  ModularCurve.solution_impl p

end S_ModularCurve_exists_monic_int_relation_modularUnit
end P2MW
export P2MW.S_ModularCurve_exists_monic_int_relation_modularUnit (solution)
