-- Prove2me | solution 1 for ModularCurve.FullLevel.level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/486da9aa-a490-5049-84df-2552172f09f9

import Mathlib
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
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
import Theorems.Thm_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst
import Theorems.Thm_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst
import Theorems.Thm_ModularCurve_coeff_zero_cuspPoint_fst_add_inv_twelve_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

namespace H1Curve

open WeierstrassCurve in
theorem vc_scale {F : Type} [Field F] (μ : F) (hμ : μ ≠ 0) (W : WeierstrassCurve F)
    (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0) :
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₁ = 0 ∧
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₂ = 0 ∧
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₃ = 0 ∧
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₄ = μ⁻¹ ^ 4 * W.a₄ ∧
    ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : VariableChange F) • W).a₆ = μ⁻¹ ^ 6 * W.a₆ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [variableChange_a₁, h1]; simp
  · rw [variableChange_a₂, h1, h2]; simp
  · rw [variableChange_a₃, h1, h3]; simp
  · rw [variableChange_a₄, h1, h2, h3]; simp [Units.val_inv_eq_inv_val]
  · rw [variableChange_a₆, h1, h2, h3]; simp [Units.val_inv_eq_inv_val]

theorem coeffMap_injective {L : Type} [Field L] (ι : L →+* ℂ) : Function.Injective (ModularCurve.coeffMap ι) := by
  intro a b h
  ext n
  have := congrArg (fun s : LaurentSeries ℂ => s.coeff n) h
  simp only [ModularCurve.coeffMap_coeff] at this
  exact ι.injective this

theorem sq_add_ten_mul_add_one_ne_zero {L : Type} [Field L] (ι : L →+* ℂ) {c : L} {N : ℕ} (hN : N ≠ 0)
    (hc : c ^ N = 1) : c ^ 2 + 10 * c + 1 ≠ 0 := by
  intro h
  have hz : (ι c) ^ N = 1 := by rw [← map_pow, hc, map_one]
  have hn : ‖ι c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hN
  have h' : (10 : ℂ) * ι c = -((ι c) ^ 2 + 1) := by
    have := congrArg ι h
    simp only [map_add, map_mul, map_pow, map_one, map_zero, map_ofNat] at this
    linear_combination this
  have h1 : ‖(10 : ℂ) * ι c‖ = 10 := by rw [norm_mul, hn, mul_one]; simp
  have h2 : ‖-((ι c) ^ 2 + 1)‖ ≤ 2 := by
    rw [norm_neg]
    calc ‖(ι c) ^ 2 + 1‖ ≤ ‖(ι c) ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_pow, hn, one_pow, norm_one]; norm_num
  rw [h'] at h1
  linarith

end H1Curve

namespace H1Curve

theorem pow_val_ne_one {L : Type} [Field L] {N : ℕ} [NeZero N] {ξ : L} (hξ : IsPrimitiveRoot ξ N)
    {a : ZMod N} (ha : a ≠ 0) : ξ ^ a.val ≠ 1 := by
  rw [Ne, hξ.pow_eq_one_iff_dvd]
  intro hd
  apply ha
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt a)

theorem pow_val_ne_neg_one {L : Type} [Field L] {N : ℕ} [NeZero N] (hNodd : Odd N) {ξ : L} (hξ : IsPrimitiveRoot ξ N)
    {a : ZMod N} (ha : a ≠ 0) : ξ ^ a.val ≠ -1 := by
  intro h
  have h2 : ξ ^ (a.val * 2) = 1 := by rw [pow_mul, h]; norm_num
  rw [hξ.pow_eq_one_iff_dvd] at h2
  have hd : N ∣ a.val := Nat.Coprime.dvd_of_dvd_mul_right hNodd.coprime_two_right h2
  exact pow_val_ne_one hξ ha ((hξ.pow_eq_one_iff_dvd _).mpr hd)

theorem fst_ne_zero_of_snd_eq_zero {N : ℕ} {v : Fin 2 → ZMod N} (hv : v ≠ 0) (hv1 : v 1 = 0) : v 0 ≠ 0 := by
  intro h0; apply hv; funext i; fin_cases i <;> simp [h0, hv1]

theorem R_ne_zero (L : Type) [Field L] (N : ℕ) [NeZero N] (hNodd : Odd N)
    (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N) (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    2 * (ModularCurve.cuspPoint L N ξ v).2 + (ModularCurve.cuspPoint L N ξ v).1 ≠ 0 := by
  intro h0
  by_cases hv1 : v 1 = 0
  · have hc := ModularCurve.coeff_zero_two_mul_cuspPoint_snd_add_fst L N ξ hξ v hv
    rw [h0, if_pos hv1, Units.val_pow_eq_pow_val] at hc
    simp only [HahnSeries.coeff_zero] at hc
    have hv0 := fst_ne_zero_of_snd_eq_zero hv hv1
    have hc1 := pow_val_ne_one hξ hv0
    have hcm1 := pow_val_ne_neg_one hNodd hξ hv0
    have hc0 : (ξ : L) ^ (v 0).val ≠ 0 := pow_ne_zero _ ξ.ne_zero
    rcases mul_eq_zero.mp hc.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact hc0 h
      · exact hcm1 (by linear_combination h)
    · have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h
      rw [inv_eq_zero, sub_eq_zero] at this
      exact hc1 this.symm
  ·
    set t : ℕ := (v 1).val with ht
    have ht0 : t ≠ 0 := by rw [ht, ne_eq, ZMod.val_eq_zero]; exact hv1
    have htN : t < N := ZMod.val_lt _
    have hvt : v 1 = (t : ZMod N) := by rw [ht, ZMod.natCast_zmod_val]
    have ht2 : 2 * t ≠ N := fun h => by
      have : Even N := ⟨t, by omega⟩
      exact (Nat.not_even_iff_odd.mpr hNodd) this

    have cast_eq : ∀ m : ℕ, m < N → (((m : ℕ) : ZMod N) = v 1 ↔ m = t) := by
      intro m hm
      rw [hvt, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt htN]
    have cast_neg : ∀ m : ℕ, 0 < m + t → m + t < 2 * N → (((m : ℕ) : ZMod N) = -v 1 ↔ m + t = N) := by
      intro m h1 h2
      rw [hvt, eq_neg_iff_add_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      constructor
      · rintro ⟨c, hc⟩
        have : c = 1 := by
          rcases c with _ | _ | c
          · omega
          · rfl
          · nlinarith
        subst this; simpa using hc
      · intro h; rw [h]
    rcases lt_or_gt_of_ne ht2 with hlt | hgt
    ·
      have hco := ModularCurve.coeff_two_mul_cuspPoint_snd_add_fst L N ξ hξ v hv t (Nat.one_le_iff_ne_zero.mpr ht0)
      rw [h0] at hco
      simp only [HahnSeries.coeff_zero] at hco
      rw [Finset.sum_eq_single_of_mem (t, 1) (by rw [Nat.mem_divisorsAntidiagonal]; exact ⟨mul_one t, ht0⟩)] at hco
      · rw [if_pos ((cast_eq t htN).mpr rfl), if_neg] at hco
        · simp only [Nat.cast_one, one_pow, one_mul, sub_zero] at hco
          exact (Units.ne_zero _) hco.symm
        · rw [cast_neg t (by omega) (by omega)]; omega
      · rintro ⟨m, d⟩ hmd hne
        rw [Nat.mem_divisorsAntidiagonal] at hmd
        have hm_le : m ≤ t := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) ⟨d, hmd.1.symm⟩
        have hm_ne : m ≠ t := by
          intro h; apply hne; subst h
          have : d = 1 := by
            have := hmd.1; rw [Nat.mul_eq_left ht0] at this; exact this
          rw [this]
        have hm_lt : m < t := lt_of_le_of_ne hm_le hm_ne
        rw [if_neg, if_neg, sub_zero, mul_zero]
        · rw [cast_neg m (by omega) (by omega)]; omega
        · rw [cast_eq m (by omega)]; exact hm_ne
    ·
      set s : ℕ := N - t with hs
      have hs0 : s ≠ 0 := by omega
      have hst : s < t := by omega
      have hco := ModularCurve.coeff_two_mul_cuspPoint_snd_add_fst L N ξ hξ v hv s (Nat.one_le_iff_ne_zero.mpr hs0)
      rw [h0] at hco
      simp only [HahnSeries.coeff_zero] at hco
      rw [Finset.sum_eq_single_of_mem (s, 1) (by rw [Nat.mem_divisorsAntidiagonal]; exact ⟨mul_one s, hs0⟩)] at hco
      · rw [if_neg, if_pos] at hco
        · simp only [Nat.cast_one, one_pow, one_mul, zero_sub, zero_eq_neg] at hco
          exact (Units.ne_zero _) hco
        · rw [cast_neg s (by omega) (by omega)]; omega
        · rw [cast_eq s (by omega)]; omega
      · rintro ⟨m, d⟩ hmd hne
        rw [Nat.mem_divisorsAntidiagonal] at hmd
        have hm_le : m ≤ s := Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) ⟨d, hmd.1.symm⟩
        have hm_ne : m ≠ s := by
          intro h; apply hne; subst h
          have : d = 1 := by
            have := hmd.1; rw [Nat.mul_eq_left hs0] at this; exact this
          rw [this]
        have hm_lt : m < s := lt_of_le_of_ne hm_le hm_ne
        rw [if_neg, if_neg, sub_zero, mul_zero]
        · rw [cast_neg m (by omega) (by omega)]; omega
        · rw [cast_eq m (by omega)]; omega

theorem X_ne_zero (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ) (N : ℕ) [NeZero N]
    (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N) (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    (ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹) ≠ 0 := by
  intro h0
  have hc := ModularCurve.coeff_zero_cuspPoint_fst_add_inv_twelve_sq L N ξ hξ v hv
  rw [h0, zero_pow two_ne_zero] at hc
  simp only [HahnSeries.coeff_zero] at hc
  by_cases hv1 : v 1 = 0
  · rw [if_pos hv1, Units.val_pow_eq_pow_val] at hc
    have hv0 := fst_ne_zero_of_snd_eq_zero hv hv1
    have hc1 : (1 : L) - (ξ : L) ^ (v 0).val ≠ 0 := sub_ne_zero.mpr (pow_val_ne_one hξ hv0).symm
    have key : (ξ : L) ^ (v 0).val * ((1 - (ξ : L) ^ (v 0).val)⁻¹) ^ 2 + 12⁻¹ = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp hc.symm
    have hN : ((ξ : L) ^ (v 0).val) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
    apply sq_add_ten_mul_add_one_ne_zero ι (NeZero.ne N) hN
    field_simp at key
    linear_combination key
  · rw [if_neg hv1] at hc
    exact pow_ne_zero 2 (inv_ne_zero (by norm_num)) hc.symm

end H1Curve

namespace H1Curve

open scoped MatrixGroups ModularForm in

theorem qExp_pow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] (hper : (1 : ℝ) ∈ Γ.strictPeriods)
    {k : ℤ} (f : ModularForm Γ k) (n : ℕ) :
    UpperHalfPlane.qExpansion 1 ((⇑f) ^ n) = (UpperHalfPlane.qExpansion 1 ⇑f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, UpperHalfPlane.qExpansion_one]
  | succ n ih =>
      rw [pow_succ, pow_succ, ← ih, ← ModularForm.coe_pow, ModularForm.qExpansion_mul_coe one_pos hper (f.pow n) f]

open scoped MatrixGroups ModularForm in

theorem pow_slash (f : UpperHalfPlane → ℂ) (k : ℤ) (A : GL (Fin 2) ℝ) (hA : ((A.det : ℝˣ) : ℝ) = 1) :
    ∀ n : ℕ, (f ^ n) ∣[((n : ℕ) : ℤ) * k] A = (f ∣[k] A) ^ n
  | 0 => by
      ext τ
      simp [ModularForm.slash_def, hA]
  | n + 1 => by
      rw [pow_succ, show (((n + 1 : ℕ) : ℤ) * k) = (n : ℕ) * k + k by push_cast; ring, ModularForm.mul_slash, hA,
        abs_one, one_smul, pow_slash f k A hA n, pow_succ]

open scoped MatrixGroups in
theorem det_conjElemN_val (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) :
    (((ModularCurve.FullLevel.conjElemN m γ).det : ℝˣ) : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (!![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)]) = 1
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  rw [Matrix.det_fin_two_of]
  field_simp
  linear_combination hdet

open scoped MatrixGroups ModularForm in
theorem σ_conjElemN_apply (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) (z : ℂ) :
    UpperHalfPlane.σ (ModularCurve.FullLevel.conjElemN m γ) z = z := by
  rw [UpperHalfPlane.σ, if_pos (by rw [det_conjElemN_val]; exact one_pos)]
  rfl

open scoped MatrixGroups in
theorem inv_apply_11 (γ : SL(2, ℤ)) : (γ⁻¹ : SL(2, ℤ)) 1 1 = γ 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

open scoped MatrixGroups in
theorem inv_apply_10 (γ : SL(2, ℤ)) : (γ⁻¹ : SL(2, ℤ)) 1 0 = -γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

end H1Curve

namespace H2G

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem coeffMap_C {R S : Type} [Field R] [Field S] (f : R →+* S) (a : R) :
    ModularCurve.coeffMap f (HahnSeries.C a) = HahnSeries.C (f a) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, ModularCurve.coeffMap_single]

theorem natDegree_le_and_coeff {T : Type} [CommRing T] {W : WeierstrassCurve T} {p k : ℕ} {h : T[X]}
    (hh : ModularCurve.IsGamma0PowAt W p k h) :
    h.natDegree ≤ ModularCurve.gamma0PowDeg p k ∧ h.coeff (ModularCurve.gamma0PowDeg p k) = 1 := by
  by_cases hpk : p ^ k = 2
  · rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk] at hh
    simp only [ModularCurve.gamma0PowDeg, hpk, if_true]
    exact ⟨hh.natDegree_le, hh.coeff_eq_one⟩
  · rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk] at hh
    simp only [ModularCurve.gamma0PowDeg, hpk, if_false]
    exact ⟨hh.natDegree_le, hh.coeff_eq_one⟩

theorem coeff_kernelVariableChangeDeg {T : Type} [CommRing T] (C : WeierstrassCurve.VariableChange T) (d : ℕ) (P : T[X])
    (j : ℕ) :
    (ModularCurve.kernelVariableChangeDeg C d P).coeff j =
      ((C.u⁻¹ : Tˣ) : T) ^ (2 * d) * ((P.comp (X + Polynomial.C C.r)).coeff j * (((C.u : Tˣ) : T) ^ 2) ^ j) := by
  have hc : Polynomial.C (((C.u : Tˣ) : T) ^ 2) * X + Polynomial.C C.r =
      (X + Polynomial.C C.r).comp (Polynomial.C (((C.u : Tˣ) : T) ^ 2) * X) := by
    rw [add_comp, X_comp, C_comp]
  rw [ModularCurve.kernelVariableChangeDeg, coeff_C_mul, ← Polynomial.C_pow, hc, ← comp_assoc, comp_C_mul_X_coeff]

theorem prod_X_sub_C_comp_X_add_C {T : Type} [CommRing T] {ι' : Type} (s : Finset ι') (x : ι' → T) (b : T) :
    (∏ a ∈ s, (X - Polynomial.C (x a))).comp (X + Polynomial.C b) = ∏ a ∈ s, (X - Polynomial.C (x a - b)) := by
  rw [Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [sub_comp, X_comp, C_comp, map_sub]
  ring

end H2G

open scoped ModularForm in
set_option maxHeartbeats 16000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K)
    (hx : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩

      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L (q * ℓ) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C₀ ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C₀).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L (q * ℓ))

    (hx6 : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C₀.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) )
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1 + HahnSeries.C ((12 : L)⁻¹))))
    (hc : ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).curve = x.curve) :
    ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
            ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) x)).level.1 = x.level.1 := by
  haveI hN : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hN1 : 1 < q * ℓ := by
    have := (Fact.out : q.Prime).two_le; have := (Fact.out : ℓ.Prime).two_le; nlinarith

  set ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit with hξu
  set w : Fin 2 → ZMod (q * ℓ) := ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))] with hw
  set X0 : LaurentSeries L := (ModularCurve.cuspPoint L (q * ℓ) ξu ![1, 0]).1 + HahnSeries.C ((12 : L)⁻¹) with hX0def
  set R0 : LaurentSeries L := 2 * (ModularCurve.cuspPoint L (q * ℓ) ξu ![1, 0]).2 +
    (ModularCurve.cuspPoint L (q * ℓ) ξu ![1, 0]).1 with hR0def
  set Xw : LaurentSeries L := (ModularCurve.cuspPoint L (q * ℓ) ξu w).1 + HahnSeries.C ((12 : L)⁻¹) with hXwdef
  set Rw : LaurentSeries L := 2 * (ModularCurve.cuspPoint L (q * ℓ) ξu w).2 +
    (ModularCurve.cuspPoint L (q * ℓ) ξu w).1 with hRwdef
  set T : WeierstrassCurve (LaurentSeries L) := ModularCurve.tateBase L (q * ℓ) with hT
  set alg : ↥K →+* LaurentSeries L := algebraMap ↥K (LaurentSeries L) with halg
  have halg_apply : ∀ z : ↥K, alg z = (z : LaurentSeries L) := fun z => rfl
  have hinj : Function.Injective alg := fun a b h => Subtype.ext h
  have hCne : ∀ a : L, a ≠ 0 → (HahnSeries.C a : LaurentSeries L) ≠ 0 := fun a ha => HahnSeries.C_ne_zero ha
  have h2ne : (2 : LaurentSeries L) ≠ 0 := by rw [← map_ofNat HahnSeries.C 2]; exact hCne _ two_ne_zero
  set u : LaurentSeries L := ((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) with hu
  have hu0 : u ≠ 0 := C₀.u.ne_zero
  obtain ⟨⟨hpin, hr, hs, ht⟩, hW, -, -, -⟩ := hx
  have h2X0 : 2 * (ModularCurve.cuspPoint L (q * ℓ) ξu ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹) = 2 * X0 := by
    rw [hX0def, mul_add, ← map_ofNat HahnSeries.C 2, ← map_mul]; congr 1; congr 1; norm_num
  rw [h2X0] at hpin

  have hw0 : w ≠ 0 := by
    intro h0
    have ha : ((γ 0 0 : ℤ) : ZMod (q * ℓ)) = 0 := by
      have := congrFun h0 0; simpa [hw] using this
    have hc : ((γ 1 0 : ℤ) : ZMod (q * ℓ)) = 0 := by
      have := congrFun h0 1; simpa [hw] using this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hc
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    have h1 : ((q * ℓ : ℕ) : ℤ) ∣ 1 := by
      rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
    have := Int.eq_one_of_dvd_one (by positivity) h1
    omega

  obtain ⟨ι, hι⟩ := id hιξ

  have hNodd : Odd (q * ℓ) := by
    refine Nat.odd_mul.mpr ⟨?_, ?_⟩
    · exact (Fact.out : q.Prime).odd_of_ne_two (by omega)
    · exact (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)
  have hξu' : IsPrimitiveRoot ((ξu : Lˣ) : L) (q * ℓ) := by rw [hξu, IsUnit.unit_spec]; exact hξ
  have hv10 : (![1, 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := by
    haveI : Fact (1 < q * ℓ) := ⟨hN1⟩
    intro h
    have h1 := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have hR0 : R0 ≠ 0 := H1Curve.R_ne_zero L (q * ℓ) hNodd ξu hξu' ![1, 0] hv10
  have hRw : Rw ≠ 0 := H1Curve.R_ne_zero L (q * ℓ) hNodd ξu hξu' w hw0
  have hXw : Xw ≠ 0 := H1Curve.X_ne_zero L ι (q * ℓ) ξu hξu' w hw0
  have hX0 : X0 ≠ 0 := by
    intro h; apply hR0; rw [← hpin, h, mul_zero, mul_zero]

  have hμ' : ((((μ : (↥K)ˣ) : ↥K)) : LaurentSeries L) * Rw * (2 * X0) = R0 * (2 * Xw) := hμ
  have hμL : ((((μ : (↥K)ˣ) : ↥K)) : LaurentSeries L) * Rw = 2 * u * Xw := by
    apply mul_right_cancel₀ (mul_ne_zero h2ne hX0)
    rw [hμ', ← hpin]; ring
  have hμK0 : (((μ : (↥K)ˣ) : ↥K)) ≠ 0 := μ.ne_zero

  have hper : (1 : ℝ) ∈ ((CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
      Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH _ _)]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨Aw, Bw, Rf, C4, C6, hv, hC4q, hC6q, hsl⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ ι hι
  rw [← hξu] at hv
  obtain ⟨hB0q, -, hAB0, hRq0⟩ := hv ![1, 0] hv10
  obtain ⟨hBwq, -, hABw, hRqw⟩ := hv w hw0
  obtain ⟨hC4sl, hC6sl, hslv⟩ := hsl γ⁻¹ (inv_mem hγ)
  obtain ⟨hAsl, hBsl, hRsl⟩ := hslv ![1, 0]
  have hidx : ∀ (Φ : (Fin 2 → ZMod (q * ℓ)) → (UpperHalfPlane → ℂ)),
      Φ ![(![1, 0] : Fin 2 → ZMod (q * ℓ)) 0 * (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (q * ℓ)) +
            (![1, 0] : Fin 2 → ZMod (q * ℓ)) 1 * (((γ⁻¹ : SL(2, ℤ)) 0 1 : ℤ) : ZMod (q * ℓ)),
          (![1, 0] : Fin 2 → ZMod (q * ℓ)) 0 * (((γ⁻¹ : SL(2, ℤ)) 1 0 : ℤ) : ZMod (q * ℓ)) +
            (![1, 0] : Fin 2 → ZMod (q * ℓ)) 1 * (((γ⁻¹ : SL(2, ℤ)) 0 0 : ℤ) : ZMod (q * ℓ))] = Φ w := by
    intro Φ; congr 1
    rw [hw, H1Curve.inv_apply_11, H1Curve.inv_apply_10]
    funext i; fin_cases i <;> simp
  rw [hidx (fun v => ⇑(Aw v))] at hAsl
  rw [hidx (fun v => ⇑(Bw v))] at hBsl
  rw [hidx (fun v => ⇑(Rf v))] at hRsl
  have det1 := H1Curve.det_conjElemN_val (q * ℓ) γ⁻¹

  have hqG : ∀ (n : ℕ) (v : Fin 2 → ZMod (q * ℓ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ((⇑(Rf v)) ^ n * (⇑(Bw v)) ^ n)) =
        (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Rf v))) ^ n *
          (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v))) ^ n := by
    intro n v
    rw [← ModularForm.coe_pow, ← ModularForm.coe_pow, ModularForm.qExpansion_mul_coe one_pos hper ((Rf v).pow n) ((Bw v).pow n),
      ModularForm.coe_pow, ModularForm.coe_pow, H1Curve.qExp_pow hper, H1Curve.qExp_pow hper, map_mul, map_pow, map_pow]
  have hqF : ∀ {kC : ℤ} (Cf : ModularForm ((CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
      Subgroup (GL (Fin 2) ℝ))) kC) (n : ℕ) (v : Fin 2 → ZMod (q * ℓ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑Cf * (⇑(Aw v)) ^ n)) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Cf) *
          (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Aw v))) ^ n := by
    intro kC Cf n v
    rw [← ModularForm.coe_pow, ModularForm.qExpansion_mul_coe one_pos hper Cf ((Aw v).pow n), ModularForm.coe_pow,
      H1Curve.qExp_pow hper, map_mul, map_pow]
  haveI : CharZero ↥K := by infer_instance

  have step : ∀ (n : ℕ) (hn : n ≠ 0) (kC ktot : ℤ)
      (Cf : ModularForm ((CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') :
        Subgroup (GL (Fin 2) ℝ))) kC) (cT : LaurentSeries L)
      (hCq : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Cf) = ModularCurve.coeffMap ι cT)
      (hCsl : (⇑Cf ∣[kC] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹) = ⇑Cf)
      (hk1 : ((n : ℕ) : ℤ) * 3 + ((n : ℕ) : ℤ) * 4 = ktot) (hk2 : kC + ((n : ℕ) : ℤ) * 6 = ktot)
      (X Y : ↥K) (hXkey : (X : LaurentSeries L) * R0 ^ n = cT * X0 ^ n) (hYkey : (Y : LaurentSeries L) * Rw ^ n = cT * Xw ^ n),
      τ X = Y := by
    intro n hn kC ktot Cf cT hCq hCsl hk1 hk2 X Y hXkey hYkey
    let G := (((Rf ![1, 0]).pow n).mul ((Bw ![1, 0]).pow n)).mcast hk1
    let F := (Cf.mul ((Aw ![1, 0]).pow n)).mcast hk2
    have hGcoe : ⇑G = (⇑(Rf ![1, 0])) ^ n * (⇑(Bw ![1, 0])) ^ n := by
      simp only [G, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
    have hFcoe : ⇑F = ⇑Cf * (⇑(Aw ![1, 0])) ^ n := by
      simp only [F, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
    have hqGv : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) =
        (ModularCurve.coeffMap ι R0) ^ n * (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ![1, 0]))) ^ n := by
      rw [hGcoe, hqG, hRq0]
    have hGsl : (⇑G ∣[ktot] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹) = (⇑(Rf w)) ^ n * (⇑(Bw w)) ^ n := by
      rw [hGcoe, ← hk1, ModularForm.mul_slash, det1, abs_one, one_smul, H1Curve.pow_slash _ _ _ det1 n,
        H1Curve.pow_slash _ _ _ det1 n, hRsl, hBsl]
    have hFsl : (⇑F ∣[ktot] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹) = ⇑Cf * (⇑(Aw w)) ^ n := by
      rw [hFcoe, ← hk2, ModularForm.mul_slash, det1, abs_one, one_smul, H1Curve.pow_slash _ _ _ det1 n, hCsl, hAsl]
    have hGne : G ≠ 0 := by
      intro h0
      have h1 : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) = 0 := by
        rw [h0, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]
      rw [hqGv] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · apply hR0
        apply H1Curve.coeffMap_injective ι
        rw [map_zero]
        exact (pow_eq_zero_iff hn).mp h
      · exact hB0q ((pow_eq_zero_iff hn).mp h)
    have hXq : ModularCurve.coeffMap ι (X : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑F) := by
      rw [hqGv, hFcoe, hqF, hCq, ← hAB0]
      calc ModularCurve.coeffMap ι (X : LaurentSeries L) * ((ModularCurve.coeffMap ι R0) ^ n *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ![1, 0]))) ^ n)
          = ModularCurve.coeffMap ι ((X : LaurentSeries L) * R0 ^ n) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ![1, 0]))) ^ n := by
            rw [map_mul, map_pow]; ring
        _ = ModularCurve.coeffMap ι (cT * X0 ^ n) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ![1, 0]))) ^ n := by rw [hXkey]
        _ = ModularCurve.coeffMap ι cT * (ModularCurve.coeffMap ι X0 *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw ![1, 0]))) ^ n := by
            rw [map_mul, map_pow]; ring
    have hYq : ModularCurve.coeffMap ι (Y : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑G ∣[ktot] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹)) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑F ∣[ktot] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹)) := by
      rw [hGsl, hFsl, hqG, hqF, hRqw, hCq, ← hABw]
      calc ModularCurve.coeffMap ι (Y : LaurentSeries L) * ((ModularCurve.coeffMap ι Rw) ^ n *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ n)
          = ModularCurve.coeffMap ι ((Y : LaurentSeries L) * Rw ^ n) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ n := by
            rw [map_mul, map_pow]; ring
        _ = ModularCurve.coeffMap ι (cT * Xw ^ n) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ n := by rw [hYkey]
        _ = ModularCurve.coeffMap ι cT * (ModularCurve.coeffMap ι Xw *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ n := by
            rw [map_mul, map_pow]; ring
    exact ModularCurve.FullLevel.AuxLevel.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ ι hι K hK γ hγ τ hτ X Y ktot F G hGne hXq hYq

  set τr : ↥K →+* ↥K := ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A).toRingHom with hτrdef
  have hτr : ∀ z : ↥K, τr z = τ z := fun z => rfl
  funext p
  show ModularCurve.kernelVariableChangeDeg (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange ↥K)
      (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) ((x.level.1 p).map τr) = x.level.1 p

  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
  haveI : Fact (p : ℕ).Prime := ⟨hp⟩
  set k : ℕ := M'.factorization (p : ℕ) with hk
  set d : ℕ := ModularCurve.gamma0PowDeg (p : ℕ) k with hd
  set h₀ : Polynomial ↥K := x.level.1 p with hh₀
  have hlev : ModularCurve.IsGamma0PowAt x.curve (p : ℕ) k h₀ := x.isLevel.1 p
  obtain ⟨hdeg', hmonic'⟩ := H2G.natDegree_le_and_coeff hlev
  have hdeg : h₀.natDegree ≤ d := hdeg'
  have hmonic : h₀.coeff d = 1 := hmonic'
  have hpk : (p : ℕ) ^ k ∣ M' := Nat.ordProj_dvd M' (p : ℕ)
  have hpk0 : (p : ℕ) ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((p : ℕ) ^ k : ℕ)) with hζdef
  have hζ : IsPrimitiveRoot ζ ((p : ℕ) ^ k) := Complex.isPrimitiveRoot_exp _ hpk0
  have h6 := hx6 p ℂ ι ζ hζ
  set Aidx : Finset ℕ := (Finset.Icc 1 ((p : ℕ) ^ k / 2)).filter (fun a => ¬ (p : ℕ) ∣ a) with hAidx
  set xa : ℕ → LaurentSeries ℂ := fun a => (ModularCurve.toricPoint ℂ (q * ℓ) (ζ ^ a)).1 with hxa
  set PiT : Polynomial (LaurentSeries ℂ) := ∏ a ∈ Aidx, (Polynomial.X - Polynomial.C (xa a + HahnSeries.C ((12 : ℂ)⁻¹))) with hPiT
  have hιu : ((((C₀.map (ModularCurve.coeffMap ι)).u : (LaurentSeries ℂ)ˣ)) : LaurentSeries ℂ) = ModularCurve.coeffMap ι u := by
    rw [hu]; rfl
  have hιr : (C₀.map (ModularCurve.coeffMap ι)).r = -HahnSeries.C ((12 : ℂ)⁻¹) := by
    show ModularCurve.coeffMap ι C₀.r = _
    rw [hr, H2G.coeffMap_C, map_neg, map_inv₀, map_ofNat, map_neg]
  have hιu0 : ModularCurve.coeffMap ι u ≠ 0 := fun h => hu0 (H1Curve.coeffMap_injective ι (by rw [h, map_zero]))

  have hcoef : ∀ j : ℕ, ModularCurve.coeffMap ι ((h₀.coeff j : ↥K) : LaurentSeries L) * ModularCurve.coeffMap ι u ^ (2 * d) =
      PiT.coeff j * (ModularCurve.coeffMap ι u ^ 2) ^ j := by
    intro j
    have e1 : ModularCurve.coeffMap ι ((h₀.coeff j : ↥K) : LaurentSeries L) =
        (((h₀.map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap ι))).coeff j := by
      rw [Polynomial.coeff_map, Polynomial.coeff_map]; rfl
    rw [e1, h6, H2G.coeff_kernelVariableChangeDeg, hιr, Units.val_inv_eq_inv_val, hιu, ← hk, ← hd]
    have e2 : (∏ a ∈ Aidx, (Polynomial.X - Polynomial.C (xa a))).comp (Polynomial.X + Polynomial.C (-HahnSeries.C ((12 : ℂ)⁻¹))) = PiT := by
      rw [H2G.prod_X_sub_C_comp_X_add_C]
      simp only [hPiT, sub_neg_eq_add]
    rw [e2]
    have hinv : (ModularCurve.coeffMap ι u)⁻¹ ^ (2 * d) * ModularCurve.coeffMap ι u ^ (2 * d) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hιu0, one_pow]
    linear_combination (PiT.coeff j * (ModularCurve.coeffMap ι u ^ 2) ^ j) * hinv

  have heig : ∀ j : ℕ, j ≤ d → τ (h₀.coeff j) = (((μ : (↥K)ˣ) : ↥K)) ^ (2 * (d - j)) * h₀.coeff j := by
    intro j hj
    rcases Nat.eq_or_lt_of_le hj with hjd | hjd
    · rw [hjd, Nat.sub_self, mul_zero, pow_zero, one_mul, hmonic, map_one]
    set m : ℕ := d - j with hm
    have hm0 : m ≠ 0 := by omega
    have hmj : j + m = d := by omega
    obtain ⟨S, hSq, hSsl⟩ :=
      ModularCurve.FullLevel.AuxLevel.exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
        q hq M' hqM' ℓ hℓ3 hℓq hℓM' (p : ℕ) k hpk ζ hζ j hj

    set cT : LaurentSeries L := (2 : LaurentSeries L) ^ (2 * m) * u ^ (2 * m) * ((h₀.coeff j : ↥K) : LaurentSeries L) with hcT
    have hCq : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(((2 : ℂ) ^ (2 * m)) • S))) = ModularCurve.coeffMap ι cT := by
      rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos hper ((2 : ℂ) ^ (2 * m)) S, PowerSeries.smul_eq_C_mul,
        map_mul, HahnSeries.ofPowerSeries_C, hSq, hcT, map_mul, map_mul, map_pow, map_pow, map_ofNat]
      have hud : ModularCurve.coeffMap ι u ^ (2 * d) = ModularCurve.coeffMap ι u ^ (2 * m) * (ModularCurve.coeffMap ι u ^ 2) ^ j := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      have key := hcoef j
      rw [hud] at key
      have hu2j : (ModularCurve.coeffMap ι u ^ 2) ^ j ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hιu0)
      have key' : ModularCurve.coeffMap ι ((h₀.coeff j : ↥K) : LaurentSeries L) * ModularCurve.coeffMap ι u ^ (2 * m) = PiT.coeff j :=
        mul_right_cancel₀ hu2j (by rw [mul_assoc, key])
      rw [show (PiT.coeff j : LaurentSeries ℂ) = (∏ a ∈ Aidx, (Polynomial.X - Polynomial.C (xa a + HahnSeries.C ((12 : ℂ)⁻¹)))).coeff j from rfl] at key'
      rw [← key']
      simp only [map_pow, map_ofNat, map_mul]
      ring
    have hCsl : ((⇑(((2 : ℂ) ^ (2 * m)) • S) : UpperHalfPlane → ℂ) ∣[(2 * ((d - j : ℕ) : ℤ))] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹) =
        ⇑(((2 : ℂ) ^ (2 * m)) • S) := by
      rw [ModularForm.IsGLPos.coe_smul, ModularForm.smul_slash, hSsl γ⁻¹ (inv_mem hγ), H1Curve.σ_conjElemN_apply]
    have hXkey : (((h₀.coeff j : ↥K)) : LaurentSeries L) * R0 ^ (2 * m) = cT * X0 ^ (2 * m) := by
      rw [← hpin, hcT]; ring
    have hYkey : ((((((μ : (↥K)ˣ) : ↥K)) ^ (2 * m) * h₀.coeff j : ↥K)) : LaurentSeries L) * Rw ^ (2 * m) = cT * Xw ^ (2 * m) := by
      rw [hcT]
      calc ((((((μ : (↥K)ˣ) : ↥K)) ^ (2 * m) * h₀.coeff j : ↥K)) : LaurentSeries L) * Rw ^ (2 * m)
          = (((h₀.coeff j : ↥K)) : LaurentSeries L) * (((((μ : (↥K)ˣ) : ↥K)) : LaurentSeries L) * Rw) ^ (2 * m) := by
            push_cast; ring
        _ = _ := by rw [hμL]; ring
    have key := step (2 * m) (by omega) (2 * ((d - j : ℕ) : ℤ)) (((2 * m : ℕ) : ℤ) * 7) (((2 : ℂ) ^ (2 * m)) • S) cT hCq hCsl
      (by push_cast; ring) (by rw [← hm]; push_cast; ring) _ _ hXkey hYkey
    rw [key, hm]

  apply Polynomial.ext
  intro j
  rw [H2G.coeff_kernelVariableChangeDeg]
  simp only [map_zero, add_zero, Polynomial.comp_X, Polynomial.coeff_map, hτr]
  by_cases hj : j ≤ d
  · have hμd : ((((μ : (↥K)ˣ) : ↥K)) ^ 2) ^ j * (((μ : (↥K)ˣ) : ↥K)) ^ (2 * (d - j)) = (((μ : (↥K)ˣ) : ↥K)) ^ (2 * d) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [heig j hj, Units.val_inv_eq_inv_val, inv_pow,
      show (((μ : (↥K)ˣ) : ↥K)) ^ (2 * (d - j)) * h₀.coeff j * ((((μ : (↥K)ˣ) : ↥K)) ^ 2) ^ j =
        (((μ : (↥K)ˣ) : ↥K)) ^ (2 * d) * h₀.coeff j by rw [← hμd]; ring,
      inv_mul_cancel_left₀ (pow_ne_zero _ hμK0)]
  · push Not at hj
    have h0 : h₀.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hj)
    rw [h0, map_zero, zero_mul, mul_zero]

end S_ModularCurve_FullLevel_level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_level_fst_act_mapRing_eq_of_curve_eq_units_of_level_fst_gamma0Pow (solution)
