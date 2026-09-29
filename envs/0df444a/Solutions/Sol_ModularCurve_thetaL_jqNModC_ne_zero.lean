-- Prove2me | solution 1 for ModularCurve.thetaL_jqNModC_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/907a7dba-7596-52d9-ae7e-7bc85da0c905

import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_jqNModC_ne_zero
set_option autoImplicit false
noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single algebraMap_laurentSeries_eq_single coeff_jqModC_neg_one thetaL thetaL_apply"
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

section ChainRule

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem thetaCoeff_qExpand (x : LaurentSeries K) :
    thetaCoeff K (qExpand K N x) = HahnSeries.single 0 (N : K) * qExpand K N (thetaCoeff K x) := by
  ext m
  rw [coeff_thetaCoeff, HahnSeries.coeff_single_zero_mul]
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeff_thetaCoeff, Int.cast_mul, Int.cast_natCast]
    ring
  · rw [qExpand_coeff_of_not_dvd N _ hdvd, qExpand_coeff_of_not_dvd N _ hdvd, mul_zero, mul_zero]

theorem coeff_thetaCoeff_jqNModC_neg : (thetaCoeff K (jqNModC K N)).coeff (-(N : ℤ)) = -(N : K) := by
  rw [coeff_thetaCoeff, jqNModC, show (-(N : ℤ)) = (N : ℤ) * (-1) by ring, qExpand_coeff_mul,
    coeff_jqModC_neg_one, mul_one, Int.cast_mul, Int.cast_natCast, Int.cast_neg, Int.cast_one]
  ring

theorem thetaCoeff_jqNModC_ne_zero (hN : (N : K) ≠ 0) : thetaCoeff K (jqNModC K N) ≠ 0 := by
  intro h
  have := coeff_thetaCoeff_jqNModC_neg K N
  rw [h, HahnSeries.coeff_zero] at this
  exact hN (neg_eq_zero.mp this.symm)

end ChainRule

section Identification

variable (K : Type*) [Field K]

set_option synthInstance.maxHeartbeats 1600000 in

theorem thetaCoeff_eq_mul_thetaCoeff_of_D_eq_smul (F : IntermediateField K (LaurentSeries K)) (f g c₀ : F)
    (h : KaehlerDifferential.D K F f = c₀ • KaehlerDifferential.D K F g) :
    thetaCoeff K (f : LaurentSeries K) = (c₀ : LaurentSeries K) * thetaCoeff K (g : LaurentSeries K) := by
  rw [← thetaDerivation_apply K F f, ← Derivation.liftKaehlerDifferential_comp_D (thetaDerivation K F) f, h,
    map_smul, Derivation.liftKaehlerDifferential_comp_D, thetaDerivation_apply, IntermediateField.smul_def,
    smul_eq_mul]

set_option synthInstance.maxHeartbeats 1600000 in

theorem coe_eq_thetaCoeff_div_of_D_eq_smul (F : IntermediateField K (LaurentSeries K)) (f g c₀ : F)
    (h : KaehlerDifferential.D K F f = c₀ • KaehlerDifferential.D K F g)
    (hg : thetaCoeff K (g : LaurentSeries K) ≠ 0) :
    (c₀ : LaurentSeries K) = thetaCoeff K (f : LaurentSeries K) / thetaCoeff K (g : LaurentSeries K) := by
  rw [thetaCoeff_eq_mul_thetaCoeff_of_D_eq_smul K F f g c₀ h, mul_div_cancel_right₀ _ hg]

end Identification

section Range

variable (K : Type*) [Field K] (p : ℕ) [NeZero p]

theorem ofPowerSeries_mk_eq_qExpand (a : ℕ → K) (h : ∀ n : ℕ, ¬ p ∣ n → a n = 0) :
    (HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk a) : LaurentSeries K) =
      qExpand K p (HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun k => a (p * k))) := by
  ext m
  rw [PowerSeries.coeff_coe]
  by_cases hdvd : (p : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe]
    have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    by_cases hk : k < 0
    · rw [if_pos (mul_neg_of_pos_of_neg hp0 hk), if_pos hk]
    · have hk' : ¬ (p : ℤ) * k < 0 := not_lt.mpr (mul_nonneg hp0.le (not_lt.mp hk))
      rw [if_neg hk', if_neg hk, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Int.natAbs_mul, Int.natAbs_natCast]
  · rw [qExpand_coeff_of_not_dvd p _ hdvd]
    by_cases hm : m < 0
    · rw [if_pos hm]
    · rw [if_neg hm, PowerSeries.coeff_mk]
      apply h
      intro hpn
      apply hdvd
      rw [Int.eq_natAbs_of_nonneg (not_lt.mp hm)]
      exact Int.natCast_dvd_natCast.mpr hpn

theorem ofPowerSeries_mk_mem_range_qExpand (a : ℕ → K) (h : ∀ n : ℕ, ¬ p ∣ n → a n = 0) :
    (HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk a) : LaurentSeries K) ∈ Set.range (qExpand K p) :=
  ⟨_, (ofPowerSeries_mk_eq_qExpand K p a h).symm⟩

theorem div_mem_range_qExpand_aux {u v : LaurentSeries K} (hu : u ∈ Set.range (qExpand K p))
    (hv : v ∈ Set.range (qExpand K p)) : u / v ∈ Set.range (qExpand K p) := by
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  exact ⟨u' / v', map_div₀ _ _ _⟩

theorem mul_mem_range_qExpand_aux {u v : LaurentSeries K} (hu : u ∈ Set.range (qExpand K p))
    (hv : v ∈ Set.range (qExpand K p)) : u * v ∈ Set.range (qExpand K p) := by
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  exact ⟨u' * v', map_mul _ _ _⟩

theorem single_zero_mem_range_qExpand_aux (c : K) : HahnSeries.single 0 c ∈ Set.range (qExpand K p) :=
  ⟨HahnSeries.single 0 c, by rw [qExpand_single, mul_zero]⟩

end Range

section ThetaLForms

variable {K : Type*} [Field K]

theorem coeff_thetaL (f : LaurentSeries K) (n : ℤ) : (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    show n - 1 + ((1 : ℕ) : ℤ) = n by push_cast; ring, Ring.choose_one_right, zsmul_eq_mul]

theorem thetaL_eq_thetaCoeff (f : LaurentSeries K) : thetaL K f = thetaCoeff K f := by
  ext n
  rw [coeff_thetaL, coeff_thetaCoeff]

end ThetaLForms

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_thetaL_jqNModC_ne_zero.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "jqModC jqNModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single algebraMap_laurentSeries_eq_single coeff_jqModC_neg_one thetaL thetaL_apply" end ModularCurve
p2m_open_scoped "ModularCurve" in
set_option synthInstance.maxHeartbeats 1600000 in
theorem ModularCurve.coe_eq_thetaL_div_of_D_eq_smul_aux (K : Type*) [Field K]
    (F : IntermediateField K (LaurentSeries K)) (f g c₀ : F)
    (h : KaehlerDifferential.D K F f = c₀ • KaehlerDifferential.D K F g)
    (hg : ModularCurve.thetaL K (g : LaurentSeries K) ≠ 0) :
    (c₀ : LaurentSeries K) =
      ModularCurve.thetaL K (f : LaurentSeries K) / ModularCurve.thetaL K (g : LaurentSeries K) := by
  simp only [ModularCurve.thetaL_eq_thetaCoeff] at hg ⊢
  exact ModularCurve.coe_eq_thetaCoeff_div_of_D_eq_smul K F f g c₀ h hg

p2m_open_scoped "ModularCurve" in
theorem ModularCurve.thetaL_qExpand_aux (K : Type*) [Field K] (N : ℕ) [NeZero N] (x : LaurentSeries K) :
    ModularCurve.thetaL K (ModularCurve.qExpand K N x) =
      HahnSeries.single (0 : ℤ) (N : K) * ModularCurve.qExpand K N (ModularCurve.thetaL K x) := by
  simp only [ModularCurve.thetaL_eq_thetaCoeff]
  exact ModularCurve.thetaCoeff_qExpand K N x

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.solution_impl (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ModularCurve.thetaL K (ModularCurve.jqNModC K N) ≠ 0 := by
  simp only [ModularCurve.thetaL_eq_thetaCoeff]
  exact ModularCurve.thetaCoeff_jqNModC_ne_zero K N hN

end
p2m_reactivate "P2MW.S_ModularCurve_thetaL_jqNModC_ne_zero.ModularCurve"

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ModularCurve.thetaL K (ModularCurve.jqNModC K N) ≠ 0 :=
  ModularCurve.solution_impl K N hN

end S_ModularCurve_thetaL_jqNModC_ne_zero
end P2MW
export P2MW.S_ModularCurve_thetaL_jqNModC_ne_zero (solution)
