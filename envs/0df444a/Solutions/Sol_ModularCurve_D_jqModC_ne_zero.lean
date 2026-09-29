-- Prove2me | solution 1 for ModularCurve.D_jqModC_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/57e7458a-0f43-5694-ae5a-f71a87e43a79

import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_D_jqModC_ne_zero

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC modularFunctionFieldC jqModC_mem algebraMap_laurentSeries_eq_single coeff_jqModC_neg_one"
p2m_open "ModularCurve"

section Theta

variable (K : Type*) [Field K]

def thetaCoeff (x : LaurentSeries K) : LaurentSeries K where
  coeff n := (n : K) * x.coeff n
  isPWO_support' := x.isPWO_support.mono fun n hn h => hn (by simp [h])

variable {K}

@[scoped simp] theorem coeff_thetaCoeff (x : LaurentSeries K) (n : ℤ) : (thetaCoeff K x).coeff n = (n : K) * x.coeff n :=
  rfl

theorem support_thetaCoeff_subset (x : LaurentSeries K) : (thetaCoeff K x).support ⊆ x.support :=
  fun n hn h => hn (by simp [h])

theorem thetaCoeff_add (x y : LaurentSeries K) : thetaCoeff K (x + y) = thetaCoeff K x + thetaCoeff K y := by
  ext n
  simp [mul_add]

theorem thetaCoeff_single_zero_mul (c : K) (x : LaurentSeries K) :
    thetaCoeff K (HahnSeries.single 0 c * x) = HahnSeries.single 0 c * thetaCoeff K x := by
  ext n
  simp only [coeff_thetaCoeff, HahnSeries.coeff_single_zero_mul]
  ring

theorem thetaCoeff_algebraMap (c : K) : thetaCoeff K (algebraMap K (LaurentSeries K) c) = 0 := by
  ext n
  rw [algebraMap_laurentSeries_eq_single, coeff_thetaCoeff, HahnSeries.coeff_single, HahnSeries.coeff_zero]
  split_ifs with h
  · subst h; simp
  · rw [mul_zero]

theorem thetaCoeff_mul (x y : LaurentSeries K) :
    thetaCoeff K (x * y) = x * thetaCoeff K y + y * thetaCoeff K x := by
  ext n
  rw [HahnSeries.coeff_add, coeff_thetaCoeff, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_right' y.isPWO_support (support_thetaCoeff_subset y), mul_comm y (thetaCoeff K x),
    HahnSeries.coeff_mul_left' x.isPWO_support (support_thetaCoeff_subset x), Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ij hij => ?_)
  obtain ⟨-, -, hsum⟩ := Finset.mem_antidiagonal.mp hij
  rw [coeff_thetaCoeff, coeff_thetaCoeff, ← hsum, Int.cast_add]
  ring

variable (K)

scoped instance isScalarTower_intermediateField_laurentSeries (F : IntermediateField K (LaurentSeries K)) :
    IsScalarTower K F (LaurentSeries K) :=
  ⟨fun c f x => by
    rw [IntermediateField.smul_def, IntermediateField.smul_def, IntermediateField.coe_smul, smul_eq_mul,
      smul_eq_mul, Algebra.smul_def, algebraMap_laurentSeries_eq_single, ← HahnSeries.single_zero_mul_eq_smul,
      mul_assoc]⟩

def thetaDerivation (F : IntermediateField K (LaurentSeries K)) : Derivation K F (LaurentSeries K) where
  toFun f := thetaCoeff K (f : LaurentSeries K)
  map_add' f g := by
    rw [IntermediateField.coe_add, thetaCoeff_add]
  map_smul' c f := by
    rw [RingHom.id_apply, IntermediateField.coe_smul, Algebra.smul_def,
      algebraMap_laurentSeries_eq_single, thetaCoeff_single_zero_mul, HahnSeries.single_zero_mul_eq_smul]
  map_one_eq_zero' := by
    change thetaCoeff K ((1 : F) : LaurentSeries K) = 0
    rw [IntermediateField.coe_one, ← map_one (algebraMap K (LaurentSeries K)), thetaCoeff_algebraMap]
  leibniz' f g := by
    change thetaCoeff K ((f * g : F) : LaurentSeries K) =
      f • thetaCoeff K (g : LaurentSeries K) + g • thetaCoeff K (f : LaurentSeries K)
    rw [IntermediateField.coe_mul, thetaCoeff_mul, IntermediateField.smul_def, IntermediateField.smul_def,
      smul_eq_mul, smul_eq_mul]

theorem thetaDerivation_apply (F : IntermediateField K (LaurentSeries K)) (f : F) :
    thetaDerivation K F f = thetaCoeff K (f : LaurentSeries K) := rfl

theorem D_ne_zero_of_thetaCoeff_ne_zero (F : IntermediateField K (LaurentSeries K)) (f : F)
    (hf : thetaCoeff K (f : LaurentSeries K) ≠ 0) : KaehlerDifferential.D K F f ≠ 0 := by
  intro h0
  apply hf
  rw [← thetaDerivation_apply K F f, ← Derivation.liftKaehlerDifferential_comp_D (thetaDerivation K F) f, h0,
    map_zero]

theorem coeff_thetaCoeff_jqModC_neg_one : (thetaCoeff K (jqModC K)).coeff (-1) = -1 := by
  rw [coeff_thetaCoeff, coeff_jqModC_neg_one, mul_one, Int.cast_neg, Int.cast_one]

theorem thetaCoeff_jqModC_ne_zero : thetaCoeff K (jqModC K) ≠ 0 := by
  intro h
  have := coeff_thetaCoeff_jqModC_neg_one K
  rw [h, HahnSeries.coeff_zero] at this
  exact one_ne_zero (neg_eq_zero.mp this.symm)

end Theta

theorem D_jqModC_ne_zero_of_isIntermediateField (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (hj : jqModC K ∈ F) : KaehlerDifferential.D K F ⟨jqModC K, hj⟩ ≠ 0 :=
  D_ne_zero_of_thetaCoeff_ne_zero K F _ (thetaCoeff_jqModC_ne_zero K)

private theorem D_jqModC_modularFunctionFieldC_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    KaehlerDifferential.D K (modularFunctionFieldC K N) ⟨jqModC K, jqModC_mem K N⟩ ≠ 0 :=
  D_jqModC_ne_zero_of_isIntermediateField K _ _

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_D_jqModC_ne_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_D_jqModC_ne_zero.ModularCurve"

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    KaehlerDifferential.D K (ModularCurve.modularFunctionFieldC K N)
      ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩ ≠ 0 :=
  ModularCurve.D_jqModC_modularFunctionFieldC_ne_zero K N

end S_ModularCurve_D_jqModC_ne_zero
end P2MW
export P2MW.S_ModularCurve_D_jqModC_ne_zero (solution)
