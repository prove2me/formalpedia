-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9b856b3b-5c02-5926-92ca-3ab006d6ca3f

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_RegularSingular_exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems
import Theorems.Thm_RegularSingular_exists_norm_apply_le_const_mul_one_add_pow_mul_rpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems

set_option autoImplicit false

namespace FourRegions

private theorem profile_pow_of_one_le {y₁ y₂ : ℝ} (h₁ : 1 ≤ y₁) (h₂ : 1 ≤ y₂) (N : ℕ) :
    (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N = (y₁ * y₂) ^ N := by
  have h₁' : y₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h₁
  have h₂' : y₂⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h₂
  rw [max_eq_left h₁, max_eq_left h₂, max_eq_right h₁', max_eq_right h₂', mul_one, mul_one]

private theorem weight_of_le_one {y : ℝ} (hy1 : y ≤ 1) (θ : ℝ) (N' : ℕ) :
    min y 1 ^ θ * max y 1 ^ (N' : ℝ) = y ^ θ := by
  rw [min_eq_left hy1, max_eq_right hy1, Real.one_rpow, mul_one]

private theorem weight_of_one_le {y : ℝ} (hy1 : 1 ≤ y) (θ : ℝ) (N' : ℕ) :
    min y 1 ^ θ * max y 1 ^ (N' : ℝ) = y ^ (N' : ℝ) := by
  rw [min_eq_right hy1, max_eq_left hy1, Real.one_rpow, one_mul]

private theorem rpow_nat_le_of_one_le {y : ℝ} (hy1 : 1 ≤ y) {E N' : ℕ} (hE : E ≤ N') : y ^ (E : ℝ) ≤ y ^ (N' : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hy1 (by exact_mod_cast hE)

private theorem weight_pos {y : ℝ} (hy : 0 < y) (θ : ℝ) (N' : ℕ) : 0 < min y 1 ^ θ * max y 1 ^ (N' : ℝ) :=
  mul_pos (Real.rpow_pos_of_pos (lt_min hy one_pos) θ) (Real.rpow_pos_of_pos (lt_max_of_lt_right one_pos) _)

private def patchConst (Cc Cp Cm₁ Cm₂ : ℝ) : ℝ := max (max Cc Cp) (max (max Cm₁ Cm₂) 0)

private theorem le_patchConst_mul_weight_mul_weight (φ : ℝ → ℝ → ℝ) (θ : ℝ) (N E₁ E₂ N' : ℕ) (hN : N ≤ N')
    (hE₁ : E₁ ≤ N')
    (hE₂ : E₂ ≤ N')
    (Cc : ℝ) (hcorner : ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → φ y₁ y₂ ≤ Cc * (y₁ ^ θ * y₂ ^ θ))
    (Cp : ℝ) (hprofile : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      φ y₁ y₂ ≤ Cp * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N)
    (Cm₁ : ℝ) (hmix₁ : ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ∀ y₂ : ℝ, 1 ≤ y₂ → φ y₁ y₂ ≤ Cm₁ * (y₁ ^ θ * y₂ ^ (E₁ : ℝ)))
    (Cm₂ : ℝ)
    (hmix₂ : ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 → ∀ y₁ : ℝ, 1 ≤ y₁ → φ y₁ y₂ ≤ Cm₂ * (y₂ ^ θ * y₁ ^ (E₂ : ℝ))) :
    ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      φ y₁ y₂ ≤
        patchConst Cc Cp Cm₁ Cm₂ * (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)) := by
  set C : ℝ := patchConst Cc Cp Cm₁ Cm₂ with hC
  simp only [patchConst] at hC
  have hCc : Cc ≤ C := hC ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hCp : Cp ≤ C := hC ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hCm₁ : Cm₁ ≤ C := hC ▸ le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hCm₂ : Cm₂ ≤ C := hC ▸ le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hC0 : 0 ≤ C := hC ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  intro y₁ y₂ h₁ h₂
  have w₁ := weight_pos h₁ θ N'
  have w₂ := weight_pos h₂ θ N'
  rcases le_or_gt y₁ 1 with h₁1 | h₁1 <;> rcases le_or_gt y₂ 1 with h₂1 | h₂1
  ·
    rw [weight_of_le_one h₁1, weight_of_le_one h₂1, mul_assoc]
    exact (hcorner y₁ h₁ h₁1 y₂ h₂ h₂1).trans
      (mul_le_mul_of_nonneg_right hCc (mul_nonneg (Real.rpow_nonneg h₁.le _) (Real.rpow_nonneg h₂.le _)))
  ·
    rw [weight_of_le_one h₁1, weight_of_one_le h₂1.le, mul_assoc]
    calc φ y₁ y₂ ≤ Cm₁ * (y₁ ^ θ * y₂ ^ (E₁ : ℝ)) := hmix₁ y₁ h₁ h₁1 y₂ h₂1.le
      _ ≤ C * (y₁ ^ θ * y₂ ^ (E₁ : ℝ)) :=
          mul_le_mul_of_nonneg_right hCm₁ (mul_nonneg (Real.rpow_nonneg h₁.le _) (Real.rpow_nonneg h₂.le _))
      _ ≤ C * (y₁ ^ θ * y₂ ^ (N' : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (rpow_nat_le_of_one_le h₂1.le hE₁) (Real.rpow_nonneg h₁.le _)) hC0
  ·
    rw [weight_of_one_le h₁1.le, weight_of_le_one h₂1, mul_assoc, mul_comm (y₁ ^ (N' : ℝ))]
    calc φ y₁ y₂ ≤ Cm₂ * (y₂ ^ θ * y₁ ^ (E₂ : ℝ)) := hmix₂ y₂ h₂ h₂1 y₁ h₁1.le
      _ ≤ C * (y₂ ^ θ * y₁ ^ (E₂ : ℝ)) :=
          mul_le_mul_of_nonneg_right hCm₂ (mul_nonneg (Real.rpow_nonneg h₂.le _) (Real.rpow_nonneg h₁.le _))
      _ ≤ C * (y₂ ^ θ * y₁ ^ (N' : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (rpow_nat_le_of_one_le h₁1.le hE₂) (Real.rpow_nonneg h₂.le _)) hC0
  ·
    rw [weight_of_one_le h₁1.le, weight_of_one_le h₂1.le, mul_assoc]
    refine (hprofile y₁ y₂ h₁ h₂).trans ?_
    rw [profile_pow_of_one_le h₁1.le h₂1.le, mul_pow, ← Real.rpow_natCast y₁ N, ← Real.rpow_natCast y₂ N]
    have e₁ : y₁ ^ (N : ℝ) ≤ y₁ ^ (N' : ℝ) := rpow_nat_le_of_one_le h₁1.le hN
    have e₂ : y₂ ^ (N : ℝ) ≤ y₂ ^ (N' : ℝ) := rpow_nat_le_of_one_le h₂1.le hN
    have p₁ : 0 ≤ y₁ ^ (N : ℝ) := Real.rpow_nonneg h₁.le _
    have p₂ : 0 ≤ y₂ ^ (N' : ℝ) := Real.rpow_nonneg h₂.le _
    calc Cp * (y₁ ^ (N : ℝ) * y₂ ^ (N : ℝ))
        ≤ C * (y₁ ^ (N : ℝ) * y₂ ^ (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hCp (mul_nonneg p₁ (Real.rpow_nonneg h₂.le _))
      _ ≤ C * (y₁ ^ (N' : ℝ) * y₂ ^ (N' : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          exact mul_le_mul e₁ e₂ (Real.rpow_nonneg h₂.le _) (Real.rpow_nonneg h₁.le _)

end FourRegions

namespace SizeBookkeeping

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℂ V]

private theorem norm_sum_pow_smul_le_of_le_one {d₂ : ℕ} (v : Fin (d₂ + 1) → V) {L₀ : ℝ} (hv : ∀ b, ‖v b‖ ≤ L₀) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : ‖∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • v b‖ ≤ (d₂ + 1) * L₀ := by
  calc ‖∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • v b‖
      ≤ ∑ b : Fin (d₂ + 1), ‖((z : ℂ) ^ (b : ℕ)) • v b‖ := norm_sum_le _ _
    _ ≤ ∑ _b : Fin (d₂ + 1), L₀ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hz]
        calc z ^ (b : ℕ) * ‖v b‖ ≤ 1 * L₀ :=
              mul_le_mul (pow_le_one₀ hz hz1) (hv b) (norm_nonneg _) zero_le_one
          _ = L₀ := one_mul _
    _ = (d₂ + 1) * L₀ := by simp

private theorem norm_sum_pow_smul_le_of_one_le {d₂ : ℕ} (v : Fin (d₂ + 1) → V) {L₀ : ℝ} (hv : ∀ b, ‖v b‖ ≤ L₀) {z : ℝ}
    (hz1 : 1 ≤ z) : ‖∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • v b‖ ≤ (d₂ + 1) * L₀ * z ^ d₂ := by
  have hz : 0 ≤ z := zero_le_one.trans hz1
  calc ‖∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • v b‖
      ≤ ∑ b : Fin (d₂ + 1), ‖((z : ℂ) ^ (b : ℕ)) • v b‖ := norm_sum_le _ _
    _ ≤ ∑ _b : Fin (d₂ + 1), L₀ * z ^ d₂ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hz]
        calc z ^ (b : ℕ) * ‖v b‖ ≤ z ^ d₂ * L₀ :=
              mul_le_mul (pow_le_pow_right₀ hz1 (Nat.lt_succ_iff.mp b.isLt)) (hv b) (norm_nonneg _)
                (pow_nonneg hz _)
          _ = L₀ * z ^ d₂ := mul_comm _ _
    _ = (d₂ + 1) * L₀ * z ^ d₂ := by simp [mul_assoc]

private theorem one_add_mul_pow_le (c : ℝ) {z : ℝ} (hz1 : 1 ≤ z) (d₂ : ℕ) : 1 + c * z ^ d₂ ≤ (1 + c) * z ^ d₂ := by
  have h1 : 1 ≤ z ^ d₂ := one_le_pow₀ hz1
  nlinarith [h1]

private theorem mixed_bound (φ : ℝ → ℝ → ℝ) (θ : ℝ) (N d₂ e : ℕ) {κ₀ L₀ B₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hL₀ : 0 ≤ L₀)
    (hB₀ : 0 ≤ B₀)
    (h : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ z : ℝ, 1 ≤ z →
      φ y z ≤ κ₀ * (1 + (d₂ + 1) * L₀ * z ^ d₂) ^ e * (B₀ * z ^ N) * y ^ θ) :
    ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ z : ℝ, 1 ≤ z →
      φ y z ≤ κ₀ * (1 + (d₂ + 1) * L₀) ^ e * B₀ * (y ^ θ * z ^ ((N + d₂ * e : ℕ) : ℝ)) := by
  intro y hy hy1 z hz1
  have hz : 0 ≤ z := zero_le_one.trans hz1
  have hpow : (1 + (d₂ + 1) * L₀ * z ^ d₂) ^ e ≤ (1 + (d₂ + 1) * L₀) ^ e * z ^ (d₂ * e) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_mul_pow_le _ hz1 d₂) e
  have hyθ : 0 ≤ y ^ θ := Real.rpow_nonneg hy.le _
  rw [Real.rpow_natCast, pow_add]
  calc φ y z ≤ κ₀ * (1 + (d₂ + 1) * L₀ * z ^ d₂) ^ e * (B₀ * z ^ N) * y ^ θ := h y hy hy1 z hz1
    _ ≤ κ₀ * ((1 + (d₂ + 1) * L₀) ^ e * z ^ (d₂ * e)) * (B₀ * z ^ N) * y ^ θ := by
        gcongr
    _ = κ₀ * (1 + (d₂ + 1) * L₀) ^ e * B₀ * (y ^ θ * (z ^ N * z ^ (d₂ * e))) := by ring

end SizeBookkeeping

namespace SystemShapes

variable {r d d₂ : ℕ}

private theorem entry_sum_smul (Mc : Fin (d₂ + 1) → Matrix (Fin r) (Fin r) ℂ) (z : ℝ) (i j : Fin r) :
    (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc b) i j = ∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc b i j := by
  simp only [Matrix.sum_apply, Matrix.smul_apply]

private theorem tail_sum_apply (A : Fin d → Fin (d₂ + 1) → ((Fin r → ℂ) →L[ℂ] (Fin r → ℂ))) (y z : ℝ) (v : Fin r → ℂ) :
    ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • A k b) v =
      ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A k b v := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ContinuousLinearMap.smul_apply, smul_smul]

private theorem rhs_eq (Mc : Fin (d₂ + 1) → Matrix (Fin r) (Fin r) ℂ)
    (A : Fin d → Fin (d₂ + 1) → ((Fin r → ℂ) →L[ℂ] (Fin r → ℂ))) (y z : ℝ) (v : Fin r → ℂ) :
    ((fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc b i j) • v j) +
        ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A k b v) =
      (fun i => ∑ j, (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc b) i j • v j) +
        ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • A k b) v := by
  rw [tail_sum_apply]
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [entry_sum_smul]
  simp only [smul_eq_mul]

private theorem norm_entry_le (Mc : Fin (d₂ + 1) → Matrix (Fin r) (Fin r) ℂ) {L₀ : ℝ} (hMc : ∀ b i j, ‖Mc b i j‖ ≤ L₀)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (i j : Fin r) :
    ‖(∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc b) i j‖ ≤ (d₂ + 1) * L₀ := by
  rw [entry_sum_smul]
  exact SizeBookkeeping.norm_sum_pow_smul_le_of_le_one (fun b => Mc b i j) (fun b => hMc b i j) hz hz1

private theorem profile_pow_of_le_one {y z : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hz : 0 < z) (hz1 : z ≤ 1) (N : ℕ) :
    (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N = y ^ (-(N : ℝ)) * z ^ (-(N : ℝ)) := by
  rw [max_eq_right hy1, max_eq_right hz1, max_eq_left (one_le_inv₀ hy |>.mpr hy1),
    max_eq_left (one_le_inv₀ hz |>.mpr hz1), one_mul, one_mul, mul_pow, Real.rpow_neg hy.le,
    Real.rpow_neg hz.le, Real.rpow_natCast, Real.rpow_natCast, inv_pow, inv_pow]

private theorem profile_pow_of_mixed {y z : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hz1 : 1 ≤ z) (N : ℕ) :
    (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N = z ^ N * y ^ (-(N : ℝ)) := by
  rw [max_eq_right hy1, max_eq_left hz1, max_eq_left (one_le_inv₀ hy |>.mpr hy1),
    max_eq_right (inv_le_one_of_one_le₀ hz1), one_mul, mul_one, mul_pow, Real.rpow_neg hy.le, Real.rpow_natCast,
    inv_pow]

private theorem profile_comm (y z : ℝ) :
    max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1 = max z 1 * max y 1 * max z⁻¹ 1 * max y⁻¹ 1 := by
  ring

private theorem le_posPart_mul_of_le {a κ₀ w : ℝ} (hw : 0 ≤ w) (h : a ≤ κ₀ * w) : a ≤ max κ₀ 0 * w :=
  h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)

private theorem norm_entry_le_of_one_le (Mc : Fin (d₂ + 1) → Matrix (Fin r) (Fin r) ℂ) {L₀ : ℝ}
    (hMc : ∀ b i j, ‖Mc b i j‖ ≤ L₀) {z : ℝ} (hz1 : 1 ≤ z) (i j : Fin r) :
    ‖(∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc b) i j‖ ≤ (d₂ + 1) * L₀ * z ^ d₂ := by
  rw [entry_sum_smul]
  exact SizeBookkeeping.norm_sum_pow_smul_le_of_one_le (fun b => Mc b i j) (fun b => hMc b i j) hz1

private theorem le_posPart_mul_mul_mul {a κ₀ p b w : ℝ} (hp : 0 ≤ p) (hb : 0 ≤ b) (hw : 0 ≤ w) (h : a ≤ κ₀ * p * b * w)
    :
    a ≤ max κ₀ 0 * p * b * w := by
  have hpbw : 0 ≤ p * b * w := mul_nonneg (mul_nonneg hp hb) hw
  calc a ≤ κ₀ * p * b * w := h
    _ = κ₀ * (p * b * w) := by ring
    _ ≤ max κ₀ 0 * (p * b * w) := mul_le_mul_of_nonneg_right (le_max_left _ _) hpbw
    _ = max κ₀ 0 * p * b * w := by ring

end SystemShapes

namespace UniformBounds

variable {G : Type*} [TopologicalSpace G] {r d d' d₂ d₂' : ℕ}

private theorem exists_bound_on_compact {K : Set G} (hK : IsCompact K)
    (Mc : G → Fin (d₂ + 1) → Matrix (Fin r) (Fin r) ℂ) (Mc' : G → Fin (d₂' + 1) → Matrix (Fin r) (Fin r) ℂ)
    (A : G → Fin d → Fin (d₂ + 1) → ((Fin r → ℂ) →L[ℂ] (Fin r → ℂ)))
    (A' : G → Fin d' → Fin (d₂' + 1) → ((Fin r → ℂ) →L[ℂ] (Fin r → ℂ)))
    (hMc : ∀ b, Continuous fun g => Mc g b) (hMc' : ∀ a, Continuous fun g => Mc' g a)
    (hA : ∀ k b, Continuous fun g => A g k b) (hA' : ∀ k a, Continuous fun g => A' g k a) :
    ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ g ∈ K, (∀ b i j, ‖Mc g b i j‖ ≤ L₀) ∧ (∀ a i j, ‖Mc' g a i j‖ ≤ L₀) ∧
      (∀ k b, ‖A g k b‖ ≤ L₀) ∧ (∀ k a, ‖A' g k a‖ ≤ L₀) := by

  set Φ : G → ℝ := fun g =>
    (∑ x : Fin (d₂ + 1) × Fin r × Fin r, ‖Mc g x.1 x.2.1 x.2.2‖) +
    (∑ x : Fin (d₂' + 1) × Fin r × Fin r, ‖Mc' g x.1 x.2.1 x.2.2‖) +
    (∑ x : Fin d × Fin (d₂ + 1), ‖A g x.1 x.2‖) + ∑ x : Fin d' × Fin (d₂' + 1), ‖A' g x.1 x.2‖ with hΦ
  have hcont : Continuous Φ := by
    refine ((Continuous.add (Continuous.add ?_ ?_) ?_).add ?_)
    · exact continuous_finsetSum _ fun x _ =>
        (((continuous_apply x.2.2).comp ((continuous_apply x.2.1).comp (hMc x.1)))).norm
    · exact continuous_finsetSum _ fun x _ =>
        (((continuous_apply x.2.2).comp ((continuous_apply x.2.1).comp (hMc' x.1)))).norm
    · exact continuous_finsetSum _ fun x _ => (hA x.1 x.2).norm
    · exact continuous_finsetSum _ fun x _ => (hA' x.1 x.2).norm
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have s₁ : ∀ g, 0 ≤ ∑ x : Fin (d₂ + 1) × Fin r × Fin r, ‖Mc g x.1 x.2.1 x.2.2‖ :=
    fun g => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have s₂ : ∀ g, 0 ≤ ∑ x : Fin (d₂' + 1) × Fin r × Fin r, ‖Mc' g x.1 x.2.1 x.2.2‖ :=
    fun g => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have s₃ : ∀ g, 0 ≤ ∑ x : Fin d × Fin (d₂ + 1), ‖A g x.1 x.2‖ := fun g => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have s₄ : ∀ g, 0 ≤ ∑ x : Fin d' × Fin (d₂' + 1), ‖A' g x.1 x.2‖ :=
    fun g => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hΦL : ∀ g ∈ K, Φ g ≤ max L 0 := fun g hg =>
    (Real.le_norm_self _).trans ((hL g hg).trans (le_max_left _ _))
  refine ⟨max L 0, le_max_right _ _, fun g hg => ⟨fun b i j => ?_, fun a i j => ?_, fun k b => ?_, fun k a => ?_⟩⟩
  · refine le_trans ?_ (hΦL g hg)
    have := Finset.single_le_sum (f := fun x : Fin (d₂ + 1) × Fin r × Fin r => ‖Mc g x.1 x.2.1 x.2.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (b, i, j))
    simp only [hΦ]; linarith [this, s₂ g, s₃ g, s₄ g]
  · refine le_trans ?_ (hΦL g hg)
    have := Finset.single_le_sum (f := fun x : Fin (d₂' + 1) × Fin r × Fin r => ‖Mc' g x.1 x.2.1 x.2.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (a, i, j))
    simp only [hΦ]; linarith [this, s₁ g, s₃ g, s₄ g]
  · refine le_trans ?_ (hΦL g hg)
    have := Finset.single_le_sum (f := fun x : Fin d × Fin (d₂ + 1) => ‖A g x.1 x.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (k, b))
    simp only [hΦ]; linarith [this, s₁ g, s₂ g, s₄ g]
  · refine le_trans ?_ (hΦL g hg)
    have := Finset.single_le_sum (f := fun x : Fin d' × Fin (d₂' + 1) => ‖A' g x.1 x.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (k, a))
    simp only [hΦ]; linarith [this, s₁ g, s₂ g, s₃ g]

private theorem exists_nonneg_ge (n : ℕ) (C : Fin n → ℝ) : ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ i, C i ≤ B₀ :=
  ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))⟩

end UniformBounds

open IsDedekindDomain NumberField AutomorphicForm

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL componentAt3 archComponent3 whittaker3 orth3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem whittaker3_fun_mul_right (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (k t : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (fun g => u (g * k)) t = whittaker3 pins ψ u (t * k) := by
  unfold whittaker3
  simp only [mul_assoc]

private def SizeExplicitSelection : Prop :=
  ∀ (D d : ℕ) (m τ θ : ℝ), θ < τ →
    ∃ e : ℕ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (r : ℕ) (q : Polynomial ℂ), q ≠ 0 → q.natDegree ≤ D → ∀ i₀ : Fin r,
    ∃ κ₀ : ℝ, ∀ (L : ℝ), 0 ≤ L →
      ∀ (M : Matrix (Fin r) (Fin r) ℂ) (A : Fin d → ((Fin r → E) →L[ℂ] (Fin r → E))),
      (∀ i j, ‖M i j‖ ≤ L) → Polynomial.aeval M q = 0 → (∀ k, ‖A k‖ ≤ L) →
      ∀ (F F' : ℝ → (Fin r → E)) (B : ℝ),
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
        (y : ℂ) • F' y = (fun i => ∑ j, M i j • F y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y)) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ B * y ^ (-m)) →
      (∃ C : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y i₀‖ ≤ C * y ^ τ) →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y i₀‖ ≤ κ₀ * (1 + L) ^ e * B * y ^ θ

private noncomputable def wordVector {r : ℕ} (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (w : Fin (r + 1) → List (Fin 3 × Fin 3))
    (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y z : ℝ) (i : Fin (r + 1)) : ℂ :=
  whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
    NumberField.StandardAddChar.psiQ
    (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
    (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * k * κ i)

private theorem exists_wordVector_le {r : ℕ} (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (w : Fin (r + 1) → List (Fin 3 × Fin 3))
    (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hH2 : ∀ w : List (Fin 3 × Fin 3),
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
          C * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N)
    {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ k ∈ K, ∀ y z : ℝ, 0 < y → 0 < z →
      ‖wordVector u w κ k y z‖ ≤ B₀ * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N := by
  choose C hC using fun i => hH2 (w i) ((fun g => g * κ i) '' K) (hK.image (continuous_mul_const (κ i)))
  obtain ⟨B₀, hB₀, hCB⟩ := UniformBounds.exists_nonneg_ge (r + 1) C
  refine ⟨B₀, hB₀, fun k hk y z hy hz => ?_⟩
  have hprof : 0 ≤ (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N := by positivity
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hB₀ hprof)).2 fun i => ?_
  have h := hC i (k * κ i) ⟨k, hk, rfl⟩ y z hy hz
  rw [← mul_assoc] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hCB i) hprof)

private theorem exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems_of_sizeExplicit
    (hsel : SizeExplicitSelection)
    (θ₀ θ : ℝ) (hθ : θ < θ₀) (N : ℕ) (d d₂ d' d₂' D D' : ℕ) :
    ∃ N' : ℕ,
      ∀ (ι ι' : Finset ℂ) (q q' : Polynomial ℂ),
      (q ≠ 0 ∧ q' ≠ 0 ∧ q.natDegree ≤ D ∧ q'.natDegree ≤ D' ∧
      (∀ e : ℂ, q.IsRoot e → ∃ e₀ ∈ ι, ∃ j : ℕ, e = e₀ + j) ∧
      (∀ e : ℂ, q'.IsRoot e → ∃ e₀ ∈ ι', ∃ j : ℕ, e = e₀ + j)) →
      ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (
      ∃ (r : ℕ) (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
        (Mc : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (Mc' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂' + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (A : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
        (A' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d' → Fin (d₂' + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ))),
        w 0 = [] ∧ κ 0 = 1 ∧
        (∀ i, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (κ i) = 1) ∧
          archComponent3 (𝓞 ℚ) ℚ (κ i) ∈ orth3) ∧
        (∀ b, Continuous fun g => Mc g b) ∧ (∀ a, Continuous fun g => Mc' g a) ∧
        (∀ k b, Continuous fun g => A g k b) ∧ (∀ k a, Continuous fun g => A' g k a) ∧
        ∀ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
          (∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc g₀ b) q = 0) ∧
          (∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' g₀ a) q' = 0) ∧
          ∀ F : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ (y z : ℝ) (i : Fin (r + 1)), F y z i =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ
              (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κ i)) →
          (∀ y z : ℝ, F y z 0 =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀)) ∧
          ∃ Fy Fz : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => F y z) (Fy y z) y ∧
            (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g₀ b i j) • F y z j) +
              ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
                ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g₀ k b (F y z)) ∧
          (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z → HasDerivAt (fun z => F y z) (Fz y z) z ∧
            (z : ℂ) • Fz y z = (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' g₀ a i j) • F y z j) +
              ∑ k : Fin d', ∑ a : Fin (d₂' + 1),
                ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' g₀ k a (F y z))
      ) →
      (∀ w : List (Fin 3 × Fin 3),
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
          C * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N) →
      (∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
        (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀)) →
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K →
        (∀ k ∈ K, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) →
        ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
            C * (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)) := by

  obtain ⟨e, he⟩ := hsel D d (N : ℝ) θ₀ θ hθ
  obtain ⟨e', he'⟩ := hsel D' d' (N : ℝ) θ₀ θ hθ
  refine ⟨N + max (d₂ * e) (d₂' * e'), ?_⟩
  intro ι ι' q q' hqq u hblock hH2 hH3 K hK hKorth
  obtain ⟨hq, hq', hdeg, hdeg', -, -⟩ := hqq
  obtain ⟨r, w, κ, Mc, Mc', A, A', -, -, -, hMc, hMc', hA, hA', hsys⟩ := hblock

  obtain ⟨κ₀, hκ₀⟩ := he ℂ (r + 1) q hq hdeg 0
  obtain ⟨κ₀', hκ₀'⟩ := he' ℂ (r + 1) q' hq' hdeg' 0
  obtain ⟨L₀, hL₀, hbnd⟩ := UniformBounds.exists_bound_on_compact hK Mc Mc' A A' hMc hMc' hA hA'
  obtain ⟨B₀, hB₀, hvec⟩ := exists_wordVector_le N u w κ hH2 hK
  set L₃ : ℝ := (d₂ + 1) * L₀ + (d₂' + 1) * L₀ with hL₃
  obtain ⟨κ₃, hκ₃⟩ := RegularSingular.exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems ℂ (r + 1) d d' q q'
    hq hq' 0 L₃ (N : ℝ) (N : ℝ) θ₀ θ hθ
  set Cm₁ : ℝ := max κ₀ 0 * (1 + (d₂ + 1) * L₀) ^ e * B₀ with hCm₁
  set Cm₂ : ℝ := max κ₀' 0 * (1 + (d₂' + 1) * L₀) ^ e' * B₀ with hCm₂
  refine ⟨FourRegions.patchConst (κ₃ * B₀) B₀ Cm₁ Cm₂, fun k hk y₁ y₂ hy₁ hy₂ => ?_⟩
  have hkorth := hKorth k hk
  obtain ⟨haev, haev', hF⟩ := hsys k hkorth
  obtain ⟨hF0, Fy, Fz, hsysY, hsysZ⟩ := hF (wordVector u w κ k) (fun _ _ _ => rfl)
  obtain ⟨hb₁, hb₂, hb₃, hb₄⟩ := hbnd k hk

  rw [← hF0 y₁ y₂]

  have hray := hH3 k hkorth
  have hrayY : ∀ z : ℝ, 0 < z → ∃ C : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖wordVector u w κ k y z 0‖ ≤ C * y ^ θ₀ := by
    intro z hz
    obtain ⟨C, hC⟩ := hray.1 z hz
    exact ⟨C, fun y hy => by rw [hF0 y z, ← whittaker3_fun_mul_right]; exact hC y hy.1 hy.2⟩
  have hrayZ : ∀ y : ℝ, 0 < y → ∃ C : ℝ, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖wordVector u w κ k y z 0‖ ≤ C * z ^ θ₀ := by
    intro y hy
    obtain ⟨C, hC⟩ := hray.2 y hy
    exact ⟨C, fun z hz => by rw [hF0 y z, ← whittaker3_fun_mul_right]; exact hC z hz.1 hz.2⟩
  have hvk := hvec k hk

  have hcorner : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ z : ℝ, 0 < z → z ≤ 1 →
      ‖wordVector u w κ k y z 0‖ ≤ κ₃ * B₀ * (y ^ θ * z ^ θ) := by
    intro y hy hy1 z hz hz1
    refine hκ₃ (fun z => ∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc k b)
      (fun y => ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' k a)
      (fun z k' => ∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • A k k' b)
      (fun y k' => ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • A' k k' a)
      ?_ ?_ ?_ ?_ (fun z hz => haev z hz.1) (fun y hy => haev' y hy.1)
      (wordVector u w κ k) Fy Fz B₀ ?_ ?_ ?_ (fun z hz => hrayY z hz.1) (fun y hy => hrayZ y hy.1)
      y ⟨hy, hy1⟩ z ⟨hz, hz1⟩
    · intro z hz i j
      refine (SystemShapes.norm_entry_le (Mc k) hb₁ hz.1.le hz.2 i j).trans ?_
      rw [hL₃]; exact le_add_of_nonneg_right (by positivity)
    · intro y hy i j
      refine (SystemShapes.norm_entry_le (Mc' k) hb₂ hy.1.le hy.2 i j).trans ?_
      rw [hL₃]; exact le_add_of_nonneg_left (by positivity)
    · intro z hz k'
      refine (SizeBookkeeping.norm_sum_pow_smul_le_of_le_one (fun b => A k k' b) (hb₃ k') hz.1.le hz.2).trans ?_
      rw [hL₃]; exact le_add_of_nonneg_right (by positivity)
    · intro y hy k'
      refine (SizeBookkeeping.norm_sum_pow_smul_le_of_le_one (fun a => A' k k' a) (hb₄ k') hy.1.le hy.2).trans ?_
      rw [hL₃]; exact le_add_of_nonneg_left (by positivity)
    · intro z hz y hy
      obtain ⟨hd, heq⟩ := hsysY z hz.1 y hy.1
      exact ⟨hd, heq.trans (SystemShapes.rhs_eq (Mc k) (A k) y z _)⟩
    · intro y hy z hz
      obtain ⟨hd, heq⟩ := hsysZ y hy.1 z hz.1
      exact ⟨hd, heq.trans (SystemShapes.rhs_eq (Mc' k) (A' k) z y _)⟩
    · intro y hy z hz
      have h := hvk y z hy.1 hz.1
      rwa [SystemShapes.profile_pow_of_le_one hy.1 hy.2 hz.1 hz.2, ← mul_assoc] at h

  have hprofile : ∀ y z : ℝ, 0 < y → 0 < z →
      ‖wordVector u w κ k y z 0‖ ≤ B₀ * (max y 1 * max z 1 * max y⁻¹ 1 * max z⁻¹ 1) ^ N :=
    fun y z hy hz => (norm_le_pi_norm (wordVector u w κ k y z) 0).trans (hvk y z hy hz)

  have hmixRaw₁ : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ z : ℝ, 1 ≤ z →
      ‖wordVector u w κ k y z 0‖ ≤ max κ₀ 0 * (1 + (d₂ + 1) * L₀ * z ^ d₂) ^ e * (B₀ * z ^ N) * y ^ θ := by
    intro y hy hy1 z hz1
    have hz : 0 < z := zero_lt_one.trans_le hz1
    have hLz : 0 ≤ (d₂ + 1) * L₀ * z ^ d₂ := by positivity
    refine SystemShapes.le_posPart_mul_mul_mul (by positivity) (by positivity) (Real.rpow_nonneg hy.le _) ?_
    refine hκ₀ _ hLz (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc k b)
      (fun k' => ∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • A k k' b)
      (fun i j => SystemShapes.norm_entry_le_of_one_le (Mc k) hb₁ hz1 i j) (haev z hz)
      (fun k' => SizeBookkeeping.norm_sum_pow_smul_le_of_one_le (fun b => A k k' b) (hb₃ k') hz1)
      (fun y => wordVector u w κ k y z) (fun y => Fy y z) (B₀ * z ^ N) ?_ ?_ (hrayY z hz) y ⟨hy, hy1⟩
    · intro y' hy'
      obtain ⟨hd, heq⟩ := hsysY z hz y' hy'.1
      exact ⟨hd, heq.trans (SystemShapes.rhs_eq (Mc k) (A k) y' z _)⟩
    · intro y' hy'
      have h := hvk y' z hy'.1 hz
      rwa [SystemShapes.profile_pow_of_mixed hy'.1 hy'.2 hz1, ← mul_assoc] at h
  have hmix₁ := SizeBookkeeping.mixed_bound (fun y z => ‖wordVector u w κ k y z 0‖) θ N d₂ e (le_max_right _ _) hL₀
    hB₀ hmixRaw₁

  have hmixRaw₂ : ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ y : ℝ, 1 ≤ y →
      ‖wordVector u w κ k y z 0‖ ≤ max κ₀' 0 * (1 + (d₂' + 1) * L₀ * y ^ d₂') ^ e' * (B₀ * y ^ N) * z ^ θ := by
    intro z hz hz1 y hy1
    have hy : 0 < y := zero_lt_one.trans_le hy1
    have hLy : 0 ≤ (d₂' + 1) * L₀ * y ^ d₂' := by positivity
    refine SystemShapes.le_posPart_mul_mul_mul (by positivity) (by positivity) (Real.rpow_nonneg hz.le _) ?_
    refine hκ₀' _ hLy (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' k a)
      (fun k' => ∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • A' k k' a)
      (fun i j => SystemShapes.norm_entry_le_of_one_le (Mc' k) hb₂ hy1 i j) (haev' y hy)
      (fun k' => SizeBookkeeping.norm_sum_pow_smul_le_of_one_le (fun a => A' k k' a) (hb₄ k') hy1)
      (fun z => wordVector u w κ k y z) (fun z => Fz y z) (B₀ * y ^ N) ?_ ?_ (hrayZ y hy) z ⟨hz, hz1⟩
    · intro z' hz'
      obtain ⟨hd, heq⟩ := hsysZ y hy z' hz'.1
      exact ⟨hd, heq.trans (SystemShapes.rhs_eq (Mc' k) (A' k) z' y _)⟩
    · intro z' hz'
      have h := hvk y z' hy hz'.1
      rwa [SystemShapes.profile_comm, SystemShapes.profile_pow_of_mixed hz'.1 hz'.2 hy1, ← mul_assoc] at h
  have hmix₂ := SizeBookkeeping.mixed_bound (fun z y => ‖wordVector u w κ k y z 0‖) θ N d₂' e' (le_max_right _ _)
    hL₀ hB₀ hmixRaw₂

  have hN : N ≤ N + max (d₂ * e) (d₂' * e') := Nat.le_add_right _ _
  have hE₁ : N + d₂ * e ≤ N + max (d₂ * e) (d₂' * e') := Nat.add_le_add_left (le_max_left _ _) _
  have hE₂ : N + d₂' * e' ≤ N + max (d₂ * e) (d₂' * e') := Nat.add_le_add_left (le_max_right _ _) _
  exact FourRegions.le_patchConst_mul_weight_mul_weight (fun y z => ‖wordVector u w κ k y z 0‖) θ N
    (N + d₂ * e) (N + d₂' * e') _ hN hE₁ hE₂ (κ₃ * B₀) hcorner B₀ hprofile Cm₁ hmix₁ Cm₂
    (fun z hz hz1 y hy1 => hmix₂ z hz hz1 y hy1) y₁ y₂ hy₁ hy₂

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems.LanglandsTunnell.CubicInduction in
theorem solution
    (θ₀ θ : ℝ) (hθ : θ < θ₀) (N : ℕ) (d d₂ d' d₂' D D' : ℕ) :
    ∃ N' : ℕ,
      ∀ (ι ι' : Finset ℂ) (q q' : Polynomial ℂ),
      (q ≠ 0 ∧ q' ≠ 0 ∧ q.natDegree ≤ D ∧ q'.natDegree ≤ D' ∧
      (∀ e : ℂ, q.IsRoot e → ∃ e₀ ∈ ι, ∃ j : ℕ, e = e₀ + j) ∧
      (∀ e : ℂ, q'.IsRoot e → ∃ e₀ ∈ ι', ∃ j : ℕ, e = e₀ + j)) →
      ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (
      ∃ (r : ℕ) (w : Fin (r + 1) → List (Fin 3 × Fin 3)) (κ : Fin (r + 1) → AdelicGL 3 (𝓞 ℚ) ℚ)
        (Mc : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂ + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (Mc' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin (d₂' + 1) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
        (A : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d → Fin (d₂ + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ)))
        (A' : AdelicGL 3 (𝓞 ℚ) ℚ → Fin d' → Fin (d₂' + 1) → ((Fin (r + 1) → ℂ) →L[ℂ] (Fin (r + 1) → ℂ))),
        w 0 = [] ∧ κ 0 = 1 ∧
        (∀ i, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (κ i) = 1) ∧
          archComponent3 (𝓞 ℚ) ℚ (κ i) ∈ orth3) ∧
        (∀ b, Continuous fun g => Mc g b) ∧ (∀ a, Continuous fun g => Mc' g a) ∧
        (∀ k b, Continuous fun g => A g k b) ∧ (∀ k a, Continuous fun g => A' g k a) ∧
        ∀ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g₀ ∈ orth3 →
          (∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc g₀ b) q = 0) ∧
          (∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' g₀ a) q' = 0) ∧
          ∀ F : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ (y z : ℝ) (i : Fin (r + 1)), F y z i =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ
              (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u (w i))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀ * κ i)) →
          (∀ y z : ℝ, F y z 0 =
            whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y * z, z, 1] i else 0) * g₀)) ∧
          ∃ Fy Fz : ℝ → ℝ → (Fin (r + 1) → ℂ),
          (∀ z : ℝ, 0 < z → ∀ y : ℝ, 0 < y → HasDerivAt (fun y => F y z) (Fy y z) y ∧
            (y : ℂ) • Fy y z = (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc g₀ b i j) • F y z j) +
              ∑ k : Fin d, ∑ b : Fin (d₂ + 1),
                ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A g₀ k b (F y z)) ∧
          (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 < z → HasDerivAt (fun z => F y z) (Fz y z) z ∧
            (z : ℂ) • Fz y z = (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' g₀ a i j) • F y z j) +
              ∑ k : Fin d', ∑ a : Fin (d₂' + 1),
                ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' g₀ k a (F y z))
      ) →
      (∀ w : List (Fin 3 × Fin 3),
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
          C * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N) →
      (∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
        (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (fun g => u (g * k))
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀)) →
      ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K →
        (∀ k ∈ K, archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) →
        ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
            C * (min y₁ 1 ^ θ * max y₁ 1 ^ (N' : ℝ)) * (min y₂ 1 ^ θ * max y₂ 1 ^ (N' : ℝ)) := by
  exact LanglandsTunnell.CubicInduction.exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems_of_sizeExplicit
    (fun D d m τ θ h => RegularSingular.exists_norm_apply_le_const_mul_one_add_pow_mul_rpow D d m τ θ h)
    θ₀ θ hθ N d d₂ d' d₂' D D'

end S_LanglandsTunnell_CubicInduction_exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_isCompact_orth3_norm_whittaker3_le_of_systems (solution)
