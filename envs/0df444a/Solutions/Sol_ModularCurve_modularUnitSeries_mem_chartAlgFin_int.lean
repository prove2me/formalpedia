-- Prove2me | solution 1 for ModularCurve.modularUnitSeries_mem_chartAlgFin_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d4071a82-3ae5-517a-ac7d-56dbb60af9f9

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_exists_monic_int_relation_modularUnit
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries_of_neZero
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false

p2m_open "ModularCurve~coeffMap_ofPowerSeries Polynomial"

namespace CU1
set_option synthInstance.maxHeartbeats 800000 in

theorem isIntegral_adjoin_trans {F : Type*} [Field F] {a b x : F}
    (hb : IsIntegral (Algebra.adjoin ℤ ({a} : Set F)) b) (hx : IsIntegral (Algebra.adjoin ℤ ({b} : Set F)) x) :
    IsIntegral (Algebra.adjoin ℤ ({a} : Set F)) x := by
  have hbC : b ∈ integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F := hb
  have hle : Algebra.adjoin ℤ ({b} : Set F) ≤ (integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F).restrictScalars ℤ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hbC)
  let φ : Algebra.adjoin ℤ ({b} : Set F) →+* integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F :=
    { toFun := fun y => ⟨y.1, hle y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hxC : IsIntegral (integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F) x := by
    have := hx.map_of_comp_eq φ (RingHom.id F) (RingHom.ext fun y => rfl)
    simpa using this
  exact isIntegral_trans (R := Algebra.adjoin ℤ ({a} : Set F))
    (A := integralClosure (Algebra.adjoin ℤ ({a} : Set F)) F) x hxC

theorem isIntegral_adjoin_of_rel {F : Type*} [Field F] (y x : F) (n : ℕ) (S : Fin n → Polynomial ℤ)
    (hrel : x ^ n + ∑ i : Fin n, aeval y (S i) * x ^ (i : ℕ) = 0) :
    IsIntegral (Algebra.adjoin ℤ ({y} : Set F)) x := by
  let yA : Algebra.adjoin ℤ ({y} : Set F) := ⟨y, Algebra.self_mem_adjoin_singleton ℤ y⟩
  let Q : Polynomial (Algebra.adjoin ℤ ({y} : Set F)) := X ^ n + ∑ i : Fin n, Polynomial.C (aeval yA (S i)) * X ^ (i : ℕ)
  have hdeg : (∑ i : Fin n, Polynomial.C (aeval yA (S i)) * X ^ (i : ℕ)).degree < (n : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i _ => ?_
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.mpr i.is_lt)
  have hmonic : Q.Monic := by
    refine (monic_X_pow n).add_of_left ?_
    rwa [degree_X_pow]
  refine ⟨Q, hmonic, ?_⟩
  have hcoef : ∀ i, algebraMap (Algebra.adjoin ℤ ({y} : Set F)) F (aeval yA (S i)) = aeval y (S i) := by
    intro i
    exact (aeval_subalgebra_coe (S i) (Algebra.adjoin ℤ ({y} : Set F)) yA).trans rfl
  have hev : Q.eval₂ (algebraMap (Algebra.adjoin ℤ ({y} : Set F)) F) x =
      x ^ n + ∑ i : Fin n, algebraMap (Algebra.adjoin ℤ ({y} : Set F)) F (aeval yA (S i)) * x ^ (i : ℕ) := by
    simp only [Q, eval₂_add, eval₂_pow, eval₂_X, eval₂_finsetSum, eval₂_mul, eval₂_C]
  rw [hev]
  simp_rw [hcoef]
  exact hrel

theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (f : A →+* B) (x : A) (q : Polynomial ℤ) :
    f (aeval x q) = aeval (f x) q := by
  rw [aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

open HahnSeries in

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R u) = HahnSeries.ofPowerSeries ℤ S (u.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

variable (p : ℕ) [Fact p.Prime] [NeZero p]

theorem exists_rel_modularUnitSeries :
    ∃ (n : ℕ) (S : Fin n → Polynomial ℤ),
      modularUnitSeries p ^ n + ∑ i : Fin n, aeval jq (S i) * modularUnitSeries p ^ (i : ℕ) = 0 := by
  obtain ⟨n, S, hrel⟩ := exists_monic_int_relation_modularUnit p
  refine ⟨n, S, ?_⟩

  set ι : LaurentSeries ℤ →+* LaurentSeries ℚ := coeffMap (Int.castRingHom ℚ) with hι
  set Δℤ : LaurentSeries ℤ := HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit with hΔℤ
  have hΔ : ι Δℤ = deltaSeries := by
    rw [hΔℤ, map_mul, hι, coeffMap_single, coeffMap_ofPowerSeries, map_one]
    rfl
  have hΔN : ι (qExpand ℤ p Δℤ) = deltaSeriesN p := by
    rw [hι, coeffMap_qExpand, ← hι, hΔ]
    rfl
  have hj : ι (jqModC ℤ) = jq := by
    rw [← jqModC_rat, jqModC_eq_map_intCast ℚ]
    rfl
  have hS : ∀ i, ι (aeval (jqModC ℤ) (S i)) = aeval jq (S i) := by
    intro i
    rw [← hj]
    exact map_aeval_int ι (jqModC ℤ) (S i)
  have hrelQ := congrArg ι hrel
  rw [map_zero, map_add, map_pow, map_sum] at hrelQ
  simp_rw [map_mul, map_pow, hΔ, hΔN, hS] at hrelQ

  have hD : deltaSeriesN p ≠ 0 := deltaSeriesN_ne_zero p
  have hu : modularUnitSeries p * deltaSeriesN p = deltaSeries := modularUnitSeries_mul_deltaSeriesN p
  have key : ∀ i : ℕ, i ≤ n →
      deltaSeries ^ i * deltaSeriesN p ^ (n - i) * (deltaSeriesN p)⁻¹ ^ n = modularUnitSeries p ^ i := by
    intro i hi
    rw [← hu, mul_pow, mul_assoc (modularUnitSeries p ^ i) (deltaSeriesN p ^ i), ← _root_.pow_add,
      Nat.add_sub_cancel' hi, mul_assoc, ← mul_pow, mul_inv_cancel₀ hD, one_pow, mul_one]
  have := congrArg (· * (deltaSeriesN p)⁻¹ ^ n) hrelQ
  simp only [zero_mul, add_mul, Finset.sum_mul] at this
  rw [← this]
  congr 1
  · have h0 := key n le_rfl
    rw [Nat.sub_self, pow_zero, mul_one] at h0
    exact h0.symm
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, mul_assoc, ← mul_assoc (deltaSeries ^ (i : ℕ)), key i i.is_lt.le]

theorem main (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p)) ∈
        AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ∧
      (p : ↥(modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(modularFunctionFieldFull p))⁻¹ ∈
        AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) := by

  set F := ↥(modularFunctionFieldFull p)
  set uF : F := ⟨modularUnitSeries p, hmem⟩ with huF
  set jF : F := IgusaScheme.jFull p with hjF
  have hinj : Function.Injective (algebraMap F (LaurentSeries ℚ)) := (algebraMap F (LaurentSeries ℚ)).injective
  have hcoe : ∀ x : F, algebraMap F (LaurentSeries ℚ) x = (x : LaurentSeries ℚ) := fun x => rfl

  obtain ⟨n, S, hrelQ⟩ := exists_rel_modularUnitSeries p
  have hrelF : uF ^ n + ∑ i : Fin n, aeval jF (S i) * uF ^ (i : ℕ) = 0 := by
    apply hinj
    rw [map_zero, map_add, map_pow, map_sum]
    simp_rw [map_mul, map_pow]
    have hjq : ∀ i, algebraMap F (LaurentSeries ℚ) (aeval jF (S i)) = aeval jq (S i) := by
      intro i
      rw [map_aeval_int (algebraMap F (LaurentSeries ℚ)) jF (S i)]
      rfl
    simp_rw [hjq]
    exact hrelQ
  have h1 : IsIntegral (Algebra.adjoin ℤ ({jF} : Set F)) uF := isIntegral_adjoin_of_rel jF uF n S hrelF
  refine ⟨h1, ?_⟩

  set w := frickeInvolutionFull p with hw
  have hwF : IsFrickeAutFull p w := isFrickeAutFull_frickeInvolutionFull p (exists_isFrickeAutFull_of_neZero p)
  set jpF : F := w jF with hjpF
  have hjpF_coe : (jpF : LaurentSeries ℚ) = jqN p := by
    have e1 : jF = ⟨qExpand ℚ 1 jq, jqd_mem_full p (Dvd.intro p (one_mul p))⟩ :=
      Subtype.ext (show (jF : LaurentSeries ℚ) = qExpand ℚ 1 jq by rw [qExpand_one_apply]; rfl)
    have := hwF 1 p (one_mul p) inferInstance inferInstance
    rw [← e1] at this
    rw [hjpF, this]
    rfl
  have hv : w uF = (p : F) ^ 12 * uF⁻¹ := by
    apply hinj
    have h1 := coe_frickeInvolutionFull_modularUnitSeries_of_neZero p hmem
    rw [← hw, ← huF] at h1
    rw [hcoe, h1, map_mul, map_pow, map_inv₀, map_natCast, hcoe uF]

    have hC : (HahnSeries.C ((p : ℚ) ^ 12) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 := by
      rw [map_pow, map_natCast]
    first
      | rw [Algebra.smul_def, ← HahnSeries.C_eq_algebraMap, hC]
      | rw [← HahnSeries.C_mul_eq_smul, hC]

  have hrel2 : ((p : F) ^ 12 * uF⁻¹) ^ n + ∑ i : Fin n, aeval jpF (S i) * ((p : F) ^ 12 * uF⁻¹) ^ (i : ℕ) = 0 := by
    have := congrArg w hrelF
    rw [map_zero, map_add, map_pow, map_sum] at this
    simp_rw [map_mul, map_pow, hv] at this
    have hwS : ∀ i, w (aeval jF (S i)) = aeval jpF (S i) := by
      intro i
      rw [hjpF]
      exact map_aeval_int w.toRingEquiv.toRingHom jF (S i)
    simp_rw [hwS] at this
    exact this
  have h2 : IsIntegral (Algebra.adjoin ℤ ({jpF} : Set F)) ((p : F) ^ 12 * uF⁻¹) :=
    isIntegral_adjoin_of_rel jpF _ n S hrel2

  have h3 : IsIntegral (Algebra.adjoin ℤ ({jF} : Set F)) jpF := by
    obtain ⟨Φ⟩ := nonempty_modularPolynomialData p
    let jA : Algebra.adjoin ℤ ({jF} : Set F) := ⟨jF, Algebra.self_mem_adjoin_singleton ℤ jF⟩
    refine ⟨Φ.Φ.map (aeval jA).toRingHom, Φ.monic.map _, ?_⟩
    apply hinj
    rw [map_zero, eval₂_map, hom_eval₂]
    have hcomp : (algebraMap F (LaurentSeries ℚ)).comp
        ((algebraMap (Algebra.adjoin ℤ ({jF} : Set F)) F).comp (aeval jA).toRingHom) = evalAtJ := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · simp [evalAtJ]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X, evalAtJ_X]
        rfl
    rw [hcomp, hcoe, hjpF_coe]
    exact Φ.eval_eq_zero
  exact isIntegral_adjoin_trans h3 h2

end CU1

theorem solution (p : ℕ) [Fact p.Prime] [NeZero p]
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    (⟨modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p)) ∈
        AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p) ∧
      (p : ↥(ModularCurve.modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p))⁻¹ ∈
        AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p) :=
  CU1.main p hmem

end S_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
end P2MW
export P2MW.S_ModularCurve_modularUnitSeries_mem_chartAlgFin_int (solution)
