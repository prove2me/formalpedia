-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/10e5bb3c-98d6-5c78-890d-b687c144545d

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
import Theorems.Thm_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst
import Theorems.Thm_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst
import Theorems.Thm_ModularCurve_coeff_zero_cuspPoint_fst_add_inv_twelve_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

open scoped MatrixGroups

namespace H34B

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

open scoped MatrixGroups in
theorem inv_apply_00 (γ : SL(2, ℤ)) : (γ⁻¹ : SL(2, ℤ)) 0 0 = γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

open scoped MatrixGroups in
theorem inv_apply_01 (γ : SL(2, ℤ)) : (γ⁻¹ : SL(2, ℤ)) 0 1 = -γ 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

end H34B

namespace H34B

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

end H34B

namespace H34B

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

end H34B

open scoped ModularForm in
set_option maxHeartbeats 4000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)

    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hC₀ : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)))

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1 + HahnSeries.C ((12 : L)⁻¹))))
    (v : Fin 2 → ZMod (q * ℓ)) (hv : v ≠ 0)
    (X Y X' Y' : ↥K)
    (hX : ((X : ↥K) : LaurentSeries L) = ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v).1 - C₀.r))
    (hY : ((Y : ↥K) : LaurentSeries L) = ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 3 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v).2 - C₀.s * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v).1 - C₀.r) - C₀.t))
    (hX' : ((X' : ↥K) : LaurentSeries L) =
      ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)) * v 0 - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * v 1, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * v 0) + ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * v 1]).1 - C₀.r))
    (hY' : ((Y' : ↥K) : LaurentSeries L) =
      ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 3 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)) * v 0 - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * v 1, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * v 0) + ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * v 1]).2 - C₀.s * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)) * v 0 - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * v 1, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * v 0) + ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * v 1]).1 - C₀.r) - C₀.t)) :
    τ X = ((μ : (↥K)ˣ) : ↥K) ^ 2 * X' ∧ τ Y = ((μ : (↥K)ˣ) : ↥K) ^ 3 * Y' := by
  haveI hN : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hN1 : 1 < q * ℓ := by
    have := (Fact.out : q.Prime).two_le; have := (Fact.out : ℓ.Prime).two_le; nlinarith

  set ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit with hξu
  set w₁ : Fin 2 → ZMod (q * ℓ) := ![1, 0] with hw₁
  set w : Fin 2 → ZMod (q * ℓ) := ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))] with hw
  set v' : Fin 2 → ZMod (q * ℓ) := ![((γ 0 0 : ℤ) : ZMod (q * ℓ)) * v 0 - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * v 1, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * v 0) + ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * v 1] with hv'
  set X0 : LaurentSeries L := (ModularCurve.cuspPoint L (q * ℓ) ξu w₁).1 + HahnSeries.C ((12 : L)⁻¹) with hX0def
  set R0 : LaurentSeries L := 2 * (ModularCurve.cuspPoint L (q * ℓ) ξu w₁).2 +
    (ModularCurve.cuspPoint L (q * ℓ) ξu w₁).1 with hR0def
  set Xw : LaurentSeries L := (ModularCurve.cuspPoint L (q * ℓ) ξu w).1 + HahnSeries.C ((12 : L)⁻¹) with hXwdef
  set Rw : LaurentSeries L := 2 * (ModularCurve.cuspPoint L (q * ℓ) ξu w).2 +
    (ModularCurve.cuspPoint L (q * ℓ) ξu w).1 with hRwdef
  set Xv : LaurentSeries L := (ModularCurve.cuspPoint L (q * ℓ) ξu v).1 + HahnSeries.C ((12 : L)⁻¹) with hXvdef
  set Rv : LaurentSeries L := 2 * (ModularCurve.cuspPoint L (q * ℓ) ξu v).2 +
    (ModularCurve.cuspPoint L (q * ℓ) ξu v).1 with hRvdef
  set Xv' : LaurentSeries L := (ModularCurve.cuspPoint L (q * ℓ) ξu v').1 + HahnSeries.C ((12 : L)⁻¹) with hXv'def
  set Rv' : LaurentSeries L := 2 * (ModularCurve.cuspPoint L (q * ℓ) ξu v').2 +
    (ModularCurve.cuspPoint L (q * ℓ) ξu v').1 with hRv'def
  set alg : ↥K →+* LaurentSeries L := algebraMap ↥K (LaurentSeries L) with halg
  have halg_apply : ∀ z : ↥K, alg z = (z : LaurentSeries L) := fun z => rfl
  have hinj : Function.Injective alg := fun a b h => Subtype.ext h
  have hCne : ∀ a : L, a ≠ 0 → (HahnSeries.C a : LaurentSeries L) ≠ 0 := fun a ha => HahnSeries.C_ne_zero ha
  have h2ne : (2 : LaurentSeries L) ≠ 0 := by rw [← map_ofNat HahnSeries.C 2]; exact hCne _ two_ne_zero
  have h4ne : (4 : LaurentSeries L) ≠ 0 := by rw [← map_ofNat HahnSeries.C 4]; exact hCne _ (by norm_num)
  set u : LaurentSeries L := ((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) with hu
  have hu0 : u ≠ 0 := C₀.u.ne_zero
  obtain ⟨hpin, hr, hs, ht⟩ := hC₀
  have h2X0 : 2 * (ModularCurve.cuspPoint L (q * ℓ) ξu w₁).1 + HahnSeries.C ((6 : L)⁻¹) = 2 * X0 := by
    rw [hX0def, mul_add, ← map_ofNat HahnSeries.C 2, ← map_mul]; congr 1; congr 1; norm_num
  rw [h2X0] at hpin

  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact h
  have hw0 : w ≠ 0 := by
    intro h0
    have ha : ((γ 0 0 : ℤ) : ZMod (q * ℓ)) = 0 := by
      have := congrFun h0 0; simpa [hw] using this
    have hc : ((γ 1 0 : ℤ) : ZMod (q * ℓ)) = 0 := by
      have := congrFun h0 1; simpa [hw] using this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hc
    have h1 : ((q * ℓ : ℕ) : ℤ) ∣ 1 := by
      rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
    have := Int.eq_one_of_dvd_one (by positivity) h1
    omega

  have hv'0 : v' ≠ 0 := by
    intro h0
    have e0 : ((γ 0 0 : ℤ) : ZMod (q * ℓ)) * v 0 - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * v 1 = 0 := by
      have := congrFun h0 0; simpa [hv'] using this
    have e1 : -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * v 0) + ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * v 1 = 0 := by
      have := congrFun h0 1; simpa [hv'] using this
    have hdetZ : ((γ 0 0 : ℤ) : ZMod (q * ℓ)) * ((γ 1 1 : ℤ) : ZMod (q * ℓ)) - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * ((γ 1 0 : ℤ) : ZMod (q * ℓ)) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod (q * ℓ))) hdet
      push_cast at this
      exact this
    have h0' : v 0 = 0 := by
      linear_combination ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * e0 + ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * e1 - (v 0) * hdetZ
    have h1' : v 1 = 0 := by
      linear_combination ((γ 1 0 : ℤ) : ZMod (q * ℓ)) * e0 + ((γ 0 0 : ℤ) : ZMod (q * ℓ)) * e1 - (v 1) * hdetZ
    apply hv
    funext i; fin_cases i <;> simp [h0', h1']

  have hNodd : Odd (q * ℓ) := by
    refine Nat.odd_mul.mpr ⟨?_, ?_⟩
    · exact (Fact.out : q.Prime).odd_of_ne_two (by omega)
    · exact (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)
  have hξu' : IsPrimitiveRoot ((ξu : Lˣ) : L) (q * ℓ) := by rw [hξu, IsUnit.unit_spec]; exact hξ
  have hv10 : w₁ ≠ 0 := by
    haveI : Fact (1 < q * ℓ) := ⟨hN1⟩
    intro h
    have h1 := congrFun h 0
    simp only [hw₁, Matrix.cons_val_zero, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have hR0 : R0 ≠ 0 := H34B.R_ne_zero L (q * ℓ) hNodd ξu hξu' w₁ hv10
  have hRw : Rw ≠ 0 := H34B.R_ne_zero L (q * ℓ) hNodd ξu hξu' w hw0
  have hX0 : X0 ≠ 0 := by
    intro h; apply hR0; rw [← hpin, h, mul_zero, mul_zero]

  have hμL : ((μ : (↥K)ˣ) : ↥K) * Rw = 2 * u * Xw := by
    apply mul_right_cancel₀ (mul_ne_zero h2ne hX0)
    calc (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * Rw * (2 * X0) = R0 * (2 * Xw) := hμ
      _ = u * (2 * X0) * (2 * Xw) := by rw [hpin]
      _ = 2 * u * Xw * (2 * X0) := by ring

  have h12 : (12 : LaurentSeries L) ≠ 0 := by rw [← map_ofNat HahnSeries.C 12]; exact hCne _ (by norm_num)
  have h24 : (24 : LaurentSeries L) ≠ 0 := by rw [← map_ofNat HahnSeries.C 24]; exact hCne _ (by norm_num)
  have hXc : (X : LaurentSeries L) * u ^ 2 = Xv := by
    rw [hX, hXvdef, Units.val_inv_eq_inv_val, ← hu, hr, map_neg, map_inv₀, map_ofNat]
    field_simp
    ring
  have hYc : (Y : LaurentSeries L) * (2 * u ^ 3) = Rv := by
    rw [hY, hRvdef, Units.val_inv_eq_inv_val, ← hu, hr, hs, ht, map_neg, map_neg, map_inv₀, map_inv₀, map_ofNat, map_ofNat,
      map_inv₀, map_ofNat]
    field_simp
    ring
  have hX'c : (X' : LaurentSeries L) * u ^ 2 = Xv' := by
    rw [hX', hXv'def, Units.val_inv_eq_inv_val, ← hu, hr, map_neg, map_inv₀, map_ofNat]
    field_simp
    ring
  have hY'c : (Y' : LaurentSeries L) * (2 * u ^ 3) = Rv' := by
    rw [hY', hRv'def, Units.val_inv_eq_inv_val, ← hu, hr, hs, ht, map_neg, map_neg, map_inv₀, map_inv₀, map_ofNat, map_ofNat,
      map_inv₀, map_ofNat]
    field_simp
    ring

  have hper : (1 : ℝ) ∈ ((CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH _ _)]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨Aw, Bw, Rf, C4, C6, hvf, -, -, hsl⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ ι hι
  rw [← hξu] at hvf
  obtain ⟨hB0q, -, hAB0, hRq0⟩ := hvf w₁ hv10
  obtain ⟨hBwq, -, hABw, hRqw⟩ := hvf w hw0
  obtain ⟨hBvq, -, hABv, hRqv⟩ := hvf v hv
  obtain ⟨hBv'q, -, hABv', hRqv'⟩ := hvf v' hv'0
  obtain ⟨-, -, hslv⟩ := hsl γ⁻¹ (inv_mem hγ)
  obtain ⟨hAsl0, hBsl0, hRsl0⟩ := hslv w₁
  obtain ⟨hAslv, hBslv, hRslv⟩ := hslv v
  have hidx0 : ∀ (Φ : (Fin 2 → ZMod (q * ℓ)) → (UpperHalfPlane → ℂ)),
      Φ ![w₁ 0 * (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (q * ℓ)) + w₁ 1 * (((γ⁻¹ : SL(2, ℤ)) 0 1 : ℤ) : ZMod (q * ℓ)),
          w₁ 0 * (((γ⁻¹ : SL(2, ℤ)) 1 0 : ℤ) : ZMod (q * ℓ)) + w₁ 1 * (((γ⁻¹ : SL(2, ℤ)) 0 0 : ℤ) : ZMod (q * ℓ))] = Φ w := by
    intro Φ; congr 1
    rw [hw, hw₁, H34B.inv_apply_11, H34B.inv_apply_10]
    funext i; fin_cases i <;> simp
  have hidxv : ∀ (Φ : (Fin 2 → ZMod (q * ℓ)) → (UpperHalfPlane → ℂ)),
      Φ ![v 0 * (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (q * ℓ)) + v 1 * (((γ⁻¹ : SL(2, ℤ)) 0 1 : ℤ) : ZMod (q * ℓ)),
          v 0 * (((γ⁻¹ : SL(2, ℤ)) 1 0 : ℤ) : ZMod (q * ℓ)) + v 1 * (((γ⁻¹ : SL(2, ℤ)) 0 0 : ℤ) : ZMod (q * ℓ))] = Φ v' := by
    intro Φ; congr 1
    rw [hv', H34B.inv_apply_11, H34B.inv_apply_10, H34B.inv_apply_00, H34B.inv_apply_01]
    push_cast
    funext i; fin_cases i <;> simp <;> ring
  rw [hidx0 (fun v => ⇑(Aw v))] at hAsl0
  rw [hidx0 (fun v => ⇑(Bw v))] at hBsl0
  rw [hidx0 (fun v => ⇑(Rf v))] at hRsl0
  rw [hidxv (fun v => ⇑(Aw v))] at hAslv
  rw [hidxv (fun v => ⇑(Bw v))] at hBslv
  rw [hidxv (fun v => ⇑(Rf v))] at hRslv
  have det1 := H34B.det_conjElemN_val (q * ℓ) γ⁻¹

  have hqpow : ∀ {k : ℤ} (f : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ((⇑f) ^ n)) = (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f)) ^ n := by
    intro k f n; rw [H34B.qExp_pow hper, map_pow]
  have hqmul : ∀ {k₁ k₂ : ℤ} (f : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') : Subgroup (GL (Fin 2) ℝ)) k₁) (g : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') : Subgroup (GL (Fin 2) ℝ)) k₂),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f * ⇑g)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) := by
    intro k₁ k₂ f g; rw [ModularForm.qExpansion_mul_coe one_pos hper f g, map_mul]
  haveI : CharZero ↥K := by infer_instance
  have c4K : ((4 : ↥K) : LaurentSeries L) = 4 := by
    rw [← halg_apply, map_ofNat]
  have hτ4 : ∀ z : ↥K, τ (4⁻¹ * z) = 4⁻¹ * τ z := by
    intro z; rw [map_mul, map_inv₀, map_ofNat]
  have h4K : (4⁻¹ : ↥K) ≠ 0 := inv_ne_zero (by norm_num)
  have hpin' : R0 = u * (2 * X0) := hpin.symm
  have h4inv : (4 : LaurentSeries L)⁻¹ * 4 = 1 := inv_mul_cancel₀ h4ne
  refine ⟨?_, ?_⟩
  ·
    have hkG : ((2 : ℕ) : ℤ) * 3 + (((2 : ℕ) : ℤ) * 4 + 4) = 18 := by norm_num
    have hkF : ((2 : ℕ) : ℤ) * 6 + 6 = 18 := by norm_num
    set G : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') : Subgroup (GL (Fin 2) ℝ)) 18 := ModularForm.mcast hkG (((Rf w₁).pow 2).mul (((Bw w₁).pow 2).mul (Bw v))) with hGdef
    set F : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') : Subgroup (GL (Fin 2) ℝ)) 18 := ModularForm.mcast hkF (((Aw w₁).pow 2).mul (Aw v)) with hFdef
    have hGcoe : ⇑G = (⇑(Rf w₁)) ^ 2 * ((⇑(Bw w₁)) ^ 2 * ⇑(Bw v)) := by
      simp only [G, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
    have hFcoe : ⇑F = (⇑(Aw w₁)) ^ 2 * ⇑(Aw v) := by
      simp only [F, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
    have hqG3 : ∀ (a b c : Fin 2 → ZMod (q * ℓ)),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ((⇑(Rf a)) ^ 2 * ((⇑(Bw b)) ^ 2 * ⇑(Bw c)))) =
          (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Rf a))) ^ 2 * ((HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw b))) ^ 2 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw c))) := by
      intro a b c
      rw [← ModularForm.coe_pow, ← ModularForm.coe_pow, ← ModularForm.coe_mul, hqmul, ModularForm.coe_mul, hqmul,
        ModularForm.coe_pow, ModularForm.coe_pow, hqpow, hqpow]
    have hqF2 : ∀ (a c : Fin 2 → ZMod (q * ℓ)),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ((⇑(Aw a)) ^ 2 * ⇑(Aw c))) = (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Aw a))) ^ 2 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Aw c)) := by
      intro a c
      rw [← ModularForm.coe_pow, hqmul, ModularForm.coe_pow, hqpow]
    have hGsl : (⇑G ∣[(18 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹) = (⇑(Rf w)) ^ 2 * ((⇑(Bw w)) ^ 2 * ⇑(Bw v')) := by
      rw [hGcoe, ← hkG, ModularForm.mul_slash, det1, abs_one, one_smul, ModularForm.mul_slash, det1, abs_one, one_smul,
        H34B.pow_slash _ _ _ det1 2, H34B.pow_slash _ _ _ det1 2, hRsl0, hBsl0, hBslv]
    have hFsl : (⇑F ∣[(18 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹) = (⇑(Aw w)) ^ 2 * ⇑(Aw v') := by
      rw [hFcoe, ← hkF, ModularForm.mul_slash, det1, abs_one, one_smul, H34B.pow_slash _ _ _ det1 2, hAsl0, hAslv]
    have hGne : G ≠ 0 := by
      intro h0
      have h1 : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) = 0 := by
        rw [h0, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]
      rw [hGcoe, hqG3, hRq0] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · apply hR0
        apply H34B.coeffMap_injective ι
        rw [map_zero]
        exact (pow_eq_zero_iff two_ne_zero).mp h
      · rcases mul_eq_zero.mp h with h | h
        · exact hB0q ((pow_eq_zero_iff two_ne_zero).mp h)
        · exact hBvq h
    have hXkey : (((4⁻¹ * X : ↥K)) : LaurentSeries L) * R0 ^ 2 = X0 ^ 2 * Xv := by
      push_cast
      rw [c4K, hpin', ← hXc]
      field_simp
      ring
    have hYkey : (((4⁻¹ * (((μ : (↥K)ˣ) : ↥K) ^ 2 * X') : ↥K)) : LaurentSeries L) * Rw ^ 2 = Xw ^ 2 * Xv' := by
      push_cast
      rw [c4K, ← hX'c]
      linear_combination (4⁻¹ * (X' : LaurentSeries L) * ((((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * Rw + 2 * u * Xw)) * hμL +
        (u ^ 2 * Xw ^ 2 * (X' : LaurentSeries L)) * h4inv
    have hXq : ModularCurve.coeffMap ι (((4⁻¹ * X : ↥K)) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑F) := by
      rw [hGcoe, hFcoe, hqG3, hqF2, hRq0, ← hAB0, ← hABv]
      calc ModularCurve.coeffMap ι (((4⁻¹ * X : ↥K)) : LaurentSeries L) * ((ModularCurve.coeffMap ι R0) ^ 2 *
              ((HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w₁))) ^ 2 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v))))
          = ModularCurve.coeffMap ι ((((4⁻¹ * X : ↥K)) : LaurentSeries L) * R0 ^ 2) *
              ((HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w₁))) ^ 2 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v))) := by
            rw [map_mul, map_pow]; ring
        _ = ModularCurve.coeffMap ι (X0 ^ 2 * Xv) *
              ((HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w₁))) ^ 2 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v))) := by rw [hXkey]
        _ = (ModularCurve.coeffMap ι X0 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w₁))) ^ 2 *
              (ModularCurve.coeffMap ι Xv * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v))) := by
            rw [map_mul, map_pow]; ring
    have hYq : ModularCurve.coeffMap ι (((4⁻¹ * (((μ : (↥K)ˣ) : ↥K) ^ 2 * X') : ↥K)) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑G ∣[(18 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹)) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑F ∣[(18 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹)) := by
      rw [hGsl, hFsl, hqG3, hqF2, hRqw, ← hABw, ← hABv']
      calc ModularCurve.coeffMap ι (((4⁻¹ * (((μ : (↥K)ˣ) : ↥K) ^ 2 * X') : ↥K)) : LaurentSeries L) * ((ModularCurve.coeffMap ι Rw) ^ 2 *
              ((HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ 2 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v'))))
          = ModularCurve.coeffMap ι ((((4⁻¹ * (((μ : (↥K)ˣ) : ↥K) ^ 2 * X') : ↥K)) : LaurentSeries L) * Rw ^ 2) *
              ((HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ 2 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v'))) := by
            rw [map_mul, map_pow]; ring
        _ = ModularCurve.coeffMap ι (Xw ^ 2 * Xv') *
              ((HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ 2 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v'))) := by rw [hYkey]
        _ = (ModularCurve.coeffMap ι Xw * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ 2 *
              (ModularCurve.coeffMap ι Xv' * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw v'))) := by
            rw [map_mul, map_pow]; ring
    have key := ModularCurve.FullLevel.AuxLevel.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ ι hι K hK γ hγ τ hτ _ _ 18 F G hGne hXq hYq
    rw [hτ4] at key
    exact mul_left_cancel₀ h4K key
  ·
    have hkG : ((3 : ℕ) : ℤ) * 3 + ((3 : ℕ) : ℤ) * 4 = 21 := by norm_num
    have hkF : ((3 : ℕ) : ℤ) * 6 + 3 = 21 := by norm_num
    set G : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') : Subgroup (GL (Fin 2) ℝ)) 21 := ModularForm.mcast hkG (((Rf w₁).pow 3).mul ((Bw w₁).pow 3)) with hGdef
    set F : ModularForm (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') : Subgroup (GL (Fin 2) ℝ)) 21 := ModularForm.mcast hkF (((Aw w₁).pow 3).mul (Rf v)) with hFdef
    have hGcoe : ⇑G = (⇑(Rf w₁)) ^ 3 * (⇑(Bw w₁)) ^ 3 := by
      simp only [G, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
    have hFcoe : ⇑F = (⇑(Aw w₁)) ^ 3 * ⇑(Rf v) := by
      simp only [F, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
    have hqG2 : ∀ (a b : Fin 2 → ZMod (q * ℓ)),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ((⇑(Rf a)) ^ 3 * (⇑(Bw b)) ^ 3)) = (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Rf a))) ^ 3 * (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw b))) ^ 3 := by
      intro a b
      rw [← ModularForm.coe_pow, ← ModularForm.coe_pow, hqmul, ModularForm.coe_pow, ModularForm.coe_pow, hqpow, hqpow]
    have hqF2 : ∀ (a c : Fin 2 → ZMod (q * ℓ)),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ((⇑(Aw a)) ^ 3 * ⇑(Rf c))) = (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Aw a))) ^ 3 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Rf c)) := by
      intro a c
      rw [← ModularForm.coe_pow, hqmul, ModularForm.coe_pow, hqpow]
    have hGsl : (⇑G ∣[(21 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹) = (⇑(Rf w)) ^ 3 * (⇑(Bw w)) ^ 3 := by
      rw [hGcoe, ← hkG, ModularForm.mul_slash, det1, abs_one, one_smul,
        H34B.pow_slash _ _ _ det1 3, H34B.pow_slash _ _ _ det1 3, hRsl0, hBsl0]
    have hFsl : (⇑F ∣[(21 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹) = (⇑(Aw w)) ^ 3 * ⇑(Rf v') := by
      rw [hFcoe, ← hkF, ModularForm.mul_slash, det1, abs_one, one_smul, H34B.pow_slash _ _ _ det1 3, hAsl0, hRslv]
    have hGne : G ≠ 0 := by
      intro h0
      have h1 : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) = 0 := by
        rw [h0, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]
      rw [hGcoe, hqG2, hRq0] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · apply hR0
        apply H34B.coeffMap_injective ι
        rw [map_zero]
        exact (pow_eq_zero_iff three_ne_zero).mp h
      · exact hB0q ((pow_eq_zero_iff three_ne_zero).mp h)
    have hXkey : (((4⁻¹ * Y : ↥K)) : LaurentSeries L) * R0 ^ 3 = X0 ^ 3 * Rv := by
      push_cast
      rw [c4K, hpin', ← hYc]
      field_simp
      ring
    have hYkey : (((4⁻¹ * (((μ : (↥K)ˣ) : ↥K) ^ 3 * Y') : ↥K)) : LaurentSeries L) * Rw ^ 3 = Xw ^ 3 * Rv' := by
      push_cast
      rw [c4K, ← hY'c]
      linear_combination (4⁻¹ * (Y' : LaurentSeries L) * (((((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * Rw) ^ 2 +
        ((((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * Rw) * (2 * u * Xw) + (2 * u * Xw) ^ 2)) * hμL +
        (2 * u ^ 3 * Xw ^ 3 * (Y' : LaurentSeries L)) * h4inv
    have hXq : ModularCurve.coeffMap ι (((4⁻¹ * Y : ↥K)) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑G) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑F) := by
      rw [hGcoe, hFcoe, hqG2, hqF2, hRq0, hRqv, ← hAB0]
      calc ModularCurve.coeffMap ι (((4⁻¹ * Y : ↥K)) : LaurentSeries L) * ((ModularCurve.coeffMap ι R0) ^ 3 *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w₁))) ^ 3)
          = ModularCurve.coeffMap ι ((((4⁻¹ * Y : ↥K)) : LaurentSeries L) * R0 ^ 3) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w₁))) ^ 3 := by
            rw [map_mul, map_pow]; ring
        _ = ModularCurve.coeffMap ι (X0 ^ 3 * Rv) * (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w₁))) ^ 3 := by rw [hXkey]
        _ = (ModularCurve.coeffMap ι X0 * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w₁))) ^ 3 * ModularCurve.coeffMap ι Rv := by
            rw [map_mul, map_pow]; ring
    have hYq : ModularCurve.coeffMap ι (((4⁻¹ * (((μ : (↥K)ˣ) : ↥K) ^ 3 * Y') : ↥K)) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑G ∣[(21 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹)) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑F ∣[(21 : ℤ)] ModularCurve.FullLevel.conjElemN (q * ℓ) γ⁻¹)) := by
      rw [hGsl, hFsl, hqG2, hqF2, hRqw, hRqv', ← hABw]
      calc ModularCurve.coeffMap ι (((4⁻¹ * (((μ : (↥K)ˣ) : ↥K) ^ 3 * Y') : ↥K)) : LaurentSeries L) * ((ModularCurve.coeffMap ι Rw) ^ 3 *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ 3)
          = ModularCurve.coeffMap ι ((((4⁻¹ * (((μ : (↥K)ˣ) : ↥K) ^ 3 * Y') : ↥K)) : LaurentSeries L) * Rw ^ 3) *
              (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ 3 := by
            rw [map_mul, map_pow]; ring
        _ = ModularCurve.coeffMap ι (Xw ^ 3 * Rv') * (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ 3 := by rw [hYkey]
        _ = (ModularCurve.coeffMap ι Xw * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(Bw w))) ^ 3 * ModularCurve.coeffMap ι Rv' := by
            rw [map_mul, map_pow]; ring
    have key := ModularCurve.FullLevel.AuxLevel.apply_eq_of_isLevelAutAt_of_coeffMap_mul_qExpansion_slash_eq
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ ι hι K hK γ hγ τ hτ _ _ 21 F G hGne hXq hYq
    rw [hτ4] at key
    exact mul_left_cancel₀ h4K key

end S_ModularCurve_FullLevel_AuxLevel_levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange (solution)
