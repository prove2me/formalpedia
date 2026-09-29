-- Prove2me | solution 1 for ModularCurve.CupPairing.cuspSum_comp_eq_of_conjRel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f996171e-3524-54c6-bd35-8ced01246335

import Mathlib
import Definitions.Def_ModularCurve_PDPairing
import Definitions.Def_ModularCurve_PeriodTransfer
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups Matrix

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.cuspSum Period.conjRel"
namespace CupPairing
namespace CuspTransport
p2m_open "ModularCurve"

open ModularCurve.PDPairing ModularCurve.Period MulAction Function

section Width

variable (Δ : Subgroup SL(2, ℤ))

theorem exists_out_smul (x : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Δ) : ∃ κ : Δ, (x • q).out = x * q.out * κ := by
  have h : (x * q.out)⁻¹ * (x • q).out ∈ Δ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← MulAction.Quotient.coe_smul_out, smul_eq_mul]
  exact ⟨⟨_, h⟩, by simp only [mul_inv_cancel_left]⟩

noncomputable def width (ζ : SL(2, ℤ) ⧸ Δ) : ℕ := minimalPeriod (ModularGroup.T • ·) ζ

theorem width_ne_zero [Δ.FiniteIndex] (ζ : SL(2, ℤ) ⧸ Δ) : width Δ ζ ≠ 0 := by
  unfold width; exact NeZero.ne _

theorem conj_zpow_mem_iff (z : SL(2, ℤ)) (n : ℤ) :
    z⁻¹ * ModularGroup.T ^ n * z ∈ Δ ↔ (width Δ (z : SL(2, ℤ) ⧸ Δ) : ℤ) ∣ n := by
  rw [mul_assoc, ← QuotientGroup.eq, ← smul_eq_mul, ← MulAction.Quotient.smul_coe, eq_comm,
    zpow_smul_eq_iff_minimalPeriod_dvd]
  rfl

noncomputable def gen (z : SL(2, ℤ)) : SL(2, ℤ) :=
  z⁻¹ * ModularGroup.T ^ ((width Δ (z : SL(2, ℤ) ⧸ Δ) : ℕ) : ℤ) * z

theorem gen_mem (z : SL(2, ℤ)) : gen Δ z ∈ Δ := (conj_zpow_mem_iff Δ z _).mpr (dvd_refl _)

noncomputable def genΔ (z : SL(2, ℤ)) : Δ := ⟨gen Δ z, gen_mem Δ z⟩

@[scoped simp] theorem coe_genΔ (z : SL(2, ℤ)) : (genΔ Δ z : SL(2, ℤ)) = gen Δ z := rfl

theorem cuspGen_eq (Q : Cusp Δ) : cuspGen Δ Q = genΔ Δ Q.out.out := by
  apply Subtype.ext
  simp only [cuspGen, coe_genΔ, gen, width, QuotientGroup.out_eq', zpow_natCast]

theorem conj_conj (z δ : SL(2, ℤ)) (n m : ℤ) :
    (ModularGroup.T ^ n * z * δ)⁻¹ * ModularGroup.T ^ m * (ModularGroup.T ^ n * z * δ) =
      δ⁻¹ * (z⁻¹ * ModularGroup.T ^ m * z) * δ := by
  have hc : ModularGroup.T ^ m * ModularGroup.T ^ n = ModularGroup.T ^ n * ModularGroup.T ^ m :=
    zpow_mul_comm _ _ _
  simp only [mul_inv_rev, mul_assoc]
  rw [← mul_assoc (ModularGroup.T ^ m) (ModularGroup.T ^ n), hc, mul_assoc (ModularGroup.T ^ n),
    inv_mul_cancel_left]

theorem width_T_zpow_mul (z δ : SL(2, ℤ)) (hδ : δ ∈ Δ) (n : ℤ) :
    width Δ ((ModularGroup.T ^ n * z * δ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ) = width Δ (z : SL(2, ℤ) ⧸ Δ) := by
  have key : ∀ m : ℤ, (ModularGroup.T ^ n * z * δ)⁻¹ * ModularGroup.T ^ m *
      (ModularGroup.T ^ n * z * δ) ∈ Δ ↔ z⁻¹ * ModularGroup.T ^ m * z ∈ Δ := by
    intro m
    rw [conj_conj, Subgroup.mul_mem_cancel_right _ hδ, Subgroup.mul_mem_cancel_left _ (Δ.inv_mem hδ)]
  apply Nat.dvd_antisymm
  · have := (conj_zpow_mem_iff Δ (ModularGroup.T ^ n * z * δ) (width Δ (z : SL(2, ℤ) ⧸ Δ))).mp
      ((key _).mpr ((conj_zpow_mem_iff Δ z _).mpr (dvd_refl _)))
    exact Int.natCast_dvd_natCast.mp this
  · have := (conj_zpow_mem_iff Δ z
      (width Δ ((ModularGroup.T ^ n * z * δ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ))).mp
      ((key _).mp ((conj_zpow_mem_iff Δ _ _).mpr (dvd_refl _)))
    exact Int.natCast_dvd_natCast.mp this

theorem gen_T_zpow_mul (z δ : SL(2, ℤ)) (hδ : δ ∈ Δ) (n : ℤ) :
    gen Δ (ModularGroup.T ^ n * z * δ) = δ⁻¹ * gen Δ z * δ := by
  simp only [gen, width_T_zpow_mul Δ z δ hδ n]
  exact conj_conj z δ n _

theorem exists_of_mem_orbit {z z' : SL(2, ℤ)}
    (h : (z' : SL(2, ℤ) ⧸ Δ) ∈ orbit (Subgroup.zpowers ModularGroup.T) (z : SL(2, ℤ) ⧸ Δ)) :
    ∃ (n : ℤ) (δ : SL(2, ℤ)), δ ∈ Δ ∧ z' = ModularGroup.T ^ n * z * δ := by
  obtain ⟨⟨k, hk⟩, hk'⟩ := h
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  refine ⟨n, (ModularGroup.T ^ n * z)⁻¹ * z', ?_, by rw [mul_inv_cancel_left]⟩
  rw [← QuotientGroup.eq]
  change ModularGroup.T ^ n • (z : SL(2, ℤ) ⧸ Δ) = z' at hk'
  rw [MulAction.Quotient.smul_coe, smul_eq_mul] at hk'
  exact hk'

theorem mem_orbit_of_eq {z z' : SL(2, ℤ)} (n : ℤ) (δ : SL(2, ℤ)) (hδ : δ ∈ Δ)
    (h : z' = ModularGroup.T ^ n * z * δ) :
    (z' : SL(2, ℤ) ⧸ Δ) ∈ orbit (Subgroup.zpowers ModularGroup.T) (z : SL(2, ℤ) ⧸ Δ) := by
  refine ⟨⟨ModularGroup.T ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩, ?_⟩
  change ModularGroup.T ^ n • (z : SL(2, ℤ) ⧸ Δ) = z'
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, h, QuotientGroup.mk_mul_of_mem _ hδ]

theorem mem_orbit_of_eq_neg (hneg : (-1 : SL(2, ℤ)) ∈ Δ) {z z' : SL(2, ℤ)} (n : ℤ) (δ : SL(2, ℤ))
    (hδ : δ ∈ Δ) (h : z' = ModularGroup.T ^ n * z * δ ∨ z' = -(ModularGroup.T ^ n * z * δ)) :
    (z' : SL(2, ℤ) ⧸ Δ) ∈ orbit (Subgroup.zpowers ModularGroup.T) (z : SL(2, ℤ) ⧸ Δ) := by
  rcases h with h | h
  · exact mem_orbit_of_eq Δ n δ hδ h
  · refine mem_orbit_of_eq Δ n (δ * (-1)) (Δ.mul_mem hδ hneg) ?_
    rw [h, ← mul_assoc, mul_neg_one]

theorem trace_conj_T_zpow (z : SL(2, ℤ)) (n : ℤ) :
    ((z⁻¹ * ModularGroup.T ^ n * z : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul,
    ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
  ring

theorem trace_gen_sq (z : SL(2, ℤ)) : ((gen Δ z : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [gen, trace_conj_T_zpow]; norm_num

theorem T_zpow_injective {a b : ℤ} (h : ModularGroup.T ^ a = ModularGroup.T ^ b) : a = b := by
  have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
  simpa [ModularGroup.coe_T_zpow] using this

theorem conj_T_zpow_zpow (z : SL(2, ℤ)) (w c : ℤ) :
    (z⁻¹ * ModularGroup.T ^ w * z) ^ c = z⁻¹ * ModularGroup.T ^ (w * c) * z := by
  have h := conj_zpow (a := z⁻¹) (b := ModularGroup.T ^ w) (i := c)
  rw [inv_inv] at h
  rw [h, ← zpow_mul]

end Width

section Frames

theorem sl2_eq_mk (B : SL(2, ℤ)) :
    (B : Matrix (Fin 2) (Fin 2) ℤ) = !![B 0 0, B 0 1; B 1 0, B 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem eq_T_zpow_of_commute (B : SL(2, ℤ)) (a : ℤ) (ha : a ≠ 0)
    (hc : ModularGroup.T ^ a * B = B * ModularGroup.T ^ a) :
    ∃ m : ℤ, B = ModularGroup.T ^ m ∨ B = -(ModularGroup.T ^ m) := by
  have h := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ)) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01

  have hc0 : B 1 0 = 0 := h00.resolve_left ha
  have hdiag : B 1 1 = B 0 0 := by
    have : a * B 1 1 = a * B 0 0 := by linarith
    exact mul_left_cancel₀ ha this
  have hdet := Matrix.SpecialLinearGroup.det_coe B
  rw [Matrix.det_fin_two] at hdet
  have hdet' : B 0 0 * B 0 0 = 1 := by
    have h1 : (B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = B 1 0 := rfl
    rw [show (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = B 0 0 from rfl,
      show (B : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = B 1 1 from rfl, h1, hc0, mul_zero, sub_zero,
      hdiag] at hdet
    exact hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet' with h1 | h1
  · refine ⟨B 0 1, Or.inl ?_⟩
    apply Subtype.ext
    rw [ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simp
    · simpa using hc0
    · simpa [hdiag] using h1
  · refine ⟨-(B 0 1), Or.inr ?_⟩
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simp
    · simpa using hc0
    · simpa [hdiag] using h1

theorem frame_unique (z z₂ : SL(2, ℤ)) (h h₂ : ℤ) (hh : h ≠ 0)
    (heq : z⁻¹ * ModularGroup.T ^ h * z = z₂⁻¹ * ModularGroup.T ^ h₂ * z₂) :
    (∃ n : ℤ, z₂ = ModularGroup.T ^ n * z ∨ z₂ = -(ModularGroup.T ^ n * z)) ∧ h₂ = h := by
  set β : SL(2, ℤ) := z₂ * z⁻¹ with hβ

  have hcomm : β * ModularGroup.T ^ h = ModularGroup.T ^ h₂ * β := by
    have : ModularGroup.T ^ h₂ = z₂ * (z⁻¹ * ModularGroup.T ^ h * z) * z₂⁻¹ := by
      rw [heq]; group
    rw [this, hβ]; group
  have hm := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ)) hcomm
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11

  have hc0 : β 1 0 = 0 := h11.resolve_right hh
  have hdet := Matrix.SpecialLinearGroup.det_coe β
  rw [Matrix.det_fin_two] at hdet
  have hdet' : β 0 0 * β 1 1 = 1 := by
    rw [show (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = β 0 0 from rfl,
      show (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = β 1 1 from rfl,
      show (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = β 1 0 from rfl, hc0, mul_zero, sub_zero] at hdet
    exact hdet
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet' with h1 | h1
  · have h4 : β 1 1 = 1 := by rw [h1, one_mul] at hdet'; exact hdet'
    have hh₂ : h₂ = h := by
      have : β 0 0 * h = h₂ * β 1 1 := by linarith
      rw [h1, h4, one_mul, mul_one] at this
      exact this.symm
    refine ⟨⟨β 0 1, Or.inl ?_⟩, hh₂⟩
    have hβT : β = ModularGroup.T ^ (β 0 1) := by
      apply Subtype.ext
      rw [ModularGroup.coe_T_zpow]
      ext i j
      fin_cases i <;> fin_cases j
      · simpa using h1
      · simp
      · simpa using hc0
      · simpa using h4
    rw [← hβT, hβ, inv_mul_cancel_right]
  · have h4 : β 1 1 = -1 := by
      rw [h1] at hdet'
      linarith
    have hh₂ : h₂ = h := by
      have : β 0 0 * h = h₂ * β 1 1 := by linarith
      rw [h1, h4] at this
      linarith
    refine ⟨⟨-(β 0 1), Or.inr ?_⟩, hh₂⟩
    have hβT : β = -(ModularGroup.T ^ (-(β 0 1))) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
      ext i j
      fin_cases i <;> fin_cases j
      · simpa using h1
      · simp
      · simpa using hc0
      · simpa using h4
    rw [← neg_mul, ← hβT, hβ, inv_mul_cancel_right]

theorem frame_eq_of_commute (z y : SL(2, ℤ)) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : (z⁻¹ * ModularGroup.T ^ a * z) * (y⁻¹ * ModularGroup.T ^ b * y) =
      (y⁻¹ * ModularGroup.T ^ b * y) * (z⁻¹ * ModularGroup.T ^ a * z)) :
    ∃ n : ℤ, y = ModularGroup.T ^ n * z ∨ y = -(ModularGroup.T ^ n * z) := by

  set β : SL(2, ℤ) := z * y⁻¹ with hβ
  set B : SL(2, ℤ) := β * ModularGroup.T ^ b * β⁻¹ with hB
  have hyB : y⁻¹ * ModularGroup.T ^ b * y = z⁻¹ * B * z := by rw [hB, hβ]; group
  have hcomm : ModularGroup.T ^ a * B = B * ModularGroup.T ^ a := by
    rw [hyB] at hc
    have h1 : z * ((z⁻¹ * ModularGroup.T ^ a * z) * (z⁻¹ * B * z)) * z⁻¹ = ModularGroup.T ^ a * B := by
      group
    have h2 : z * ((z⁻¹ * B * z) * (z⁻¹ * ModularGroup.T ^ a * z)) * z⁻¹ = B * ModularGroup.T ^ a := by
      group
    rw [← h1, hc, h2]
  obtain ⟨m, hm⟩ := eq_T_zpow_of_commute B a ha hcomm

  have hBm : B = ModularGroup.T ^ m := by
    rcases hm with hm | hm
    · exact hm
    · exfalso
      have htr : ((B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
        rw [hB, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, one_mul, ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
        ring
      rw [hm, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, ModularGroup.coe_T_zpow,
        Matrix.trace_fin_two_of] at htr
      norm_num at htr

  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0, zpow_zero] at hBm
    have : ModularGroup.T ^ b = 1 := by
      have h1 : ModularGroup.T ^ b = β⁻¹ * B * β := by rw [hB]; group
      rw [h1, hBm]; group
    have h2 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) this
    simp [ModularGroup.coe_T_zpow] at h2
    exact hb h2

  have hframe : (1 : SL(2, ℤ))⁻¹ * ModularGroup.T ^ m * 1 = β⁻¹⁻¹ * ModularGroup.T ^ b * β⁻¹ := by
    rw [inv_one, one_mul, mul_one, inv_inv, ← hBm, hB]
  obtain ⟨⟨n, hn⟩, -⟩ := frame_unique 1 β⁻¹ m b hm0 hframe
  refine ⟨n, ?_⟩
  rw [mul_one, hβ, _root_.mul_inv_rev, inv_inv] at hn
  rcases hn with hn | hn
  · left
    calc y = (y * z⁻¹) * z := by group
      _ = ModularGroup.T ^ n * z := by rw [hn]
  · right
    calc y = (y * z⁻¹) * z := by group
      _ = -(ModularGroup.T ^ n * z) := by rw [hn, neg_mul]

def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

def PosPar (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop := ∀ v : Fin 2 → ℝ, 0 ≤ v ⬝ᵥ (((M - 1) * J) *ᵥ v)

theorem inv_mul_J (g : GL (Fin 2) ℝ) :
    ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * J =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ • (J * (g : Matrix (Fin 2) (Fin 2) ℝ).transpose) := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv',
    smul_mul_assoc]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]

theorem posPar_conj_iff (g : GL (Fin 2) ℝ) (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    PosPar ((g : Matrix (Fin 2) (Fin 2) ℝ) * M * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) ↔
      PosPar M := by
  have hginv : (g : Matrix (Fin 2) (Fin 2) ℝ) * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

  have key : ((g : Matrix (Fin 2) (Fin 2) ℝ) * M * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) - 1) * J =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ •
        ((g : Matrix (Fin 2) (Fin 2) ℝ) * ((M - 1) * J) * (g : Matrix (Fin 2) (Fin 2) ℝ).transpose) := by
    have h1 : (g : Matrix (Fin 2) (Fin 2) ℝ) * M * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) - 1 =
        (g : Matrix (Fin 2) (Fin 2) ℝ) * (M - 1) * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hginv]
    rw [h1, Matrix.mul_assoc, Matrix.mul_assoc, inv_mul_J, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have form : ∀ v : Fin 2 → ℝ,
      v ⬝ᵥ ((((g : Matrix (Fin 2) (Fin 2) ℝ) * M * ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) - 1) *
        J) *ᵥ v) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ *
        (((g : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ v) ⬝ᵥ (((M - 1) * J) *ᵥ
          ((g : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ v))) := by
    intro v
    rw [key, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  constructor
  · intro h v

    have hT : IsUnit (g : Matrix (Fin 2) (Fin 2) ℝ).transpose.det := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hg.ne'
    set w := ((g : Matrix (Fin 2) (Fin 2) ℝ).transpose)⁻¹ *ᵥ v with hw
    have hv : (g : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ w = v := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]
    have h1 := h w
    rw [form, hv] at h1
    exact nonneg_of_mul_nonneg_right h1 (inv_pos.mpr hg)
  · intro h v
    rw [form]
    exact mul_nonneg (inv_pos.mpr hg).le (h _)

theorem posPar_T_zpow_iff (h : ℤ) :
    PosPar ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ h) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      ↔ 0 ≤ h := by
  have hmat : ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ h) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![1, (h : ℝ); 0, 1] := by
    change ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) = _
    rw [ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hform : ∀ v : Fin 2 → ℝ,
      v ⬝ᵥ (((!![1, (h : ℝ); 0, 1] - 1) * J) *ᵥ v) = (h : ℝ) * (v 0 * v 0) := by
    intro v
    have : (!![1, (h : ℝ); 0, 1] - 1) * J = !![(h : ℝ), 0; 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    rw [this]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  unfold PosPar
  rw [hmat]
  simp only [hform]
  constructor
  · intro hv
    have := hv (fun _ => 1)
    simp at this
    exact_mod_cast this
  · intro hh v
    exact mul_nonneg (by exact_mod_cast hh) (mul_self_nonneg _)

theorem posPar_conj_T_zpow_iff (z : SL(2, ℤ)) (h : ℤ) :
    PosPar ((Matrix.SpecialLinearGroup.mapGL ℝ (z⁻¹ * ModularGroup.T ^ h * z) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) ↔ 0 ≤ h := by
  rw [← posPar_T_zpow_iff h]
  have hdet : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ z⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    have : ((Matrix.SpecialLinearGroup.mapGL ℝ z⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 :=
      Matrix.SpecialLinearGroup.det_coe _
    rw [this]; exact one_pos
  have hmat : ((Matrix.SpecialLinearGroup.mapGL ℝ (z⁻¹ * ModularGroup.T ^ h * z) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((Matrix.SpecialLinearGroup.mapGL ℝ z⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ h) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (((Matrix.SpecialLinearGroup.mapGL ℝ z⁻¹)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [map_mul, map_mul, map_inv, inv_inv, Units.val_mul, Units.val_mul]
  rw [hmat, posPar_conj_iff _ hdet]

theorem posPar_iff_of_conjRel (g : GL (Fin 2) ℝ) (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (u' u : SL(2, ℤ))
    (hrel : g * Matrix.SpecialLinearGroup.mapGL ℝ u' = Matrix.SpecialLinearGroup.mapGL ℝ u * g) :
    PosPar ((Matrix.SpecialLinearGroup.mapGL ℝ u : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ↔
      PosPar ((Matrix.SpecialLinearGroup.mapGL ℝ u' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h : Matrix.SpecialLinearGroup.mapGL ℝ u = g * Matrix.SpecialLinearGroup.mapGL ℝ u' * g⁻¹ := by
    rw [hrel, mul_inv_cancel_right]
  rw [h, Units.val_mul, Units.val_mul]
  exact posPar_conj_iff g hg _

end Frames

section ConjRel

variable {g : GL (Fin 2) ℝ}

theorem coe_mapGL (γ : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℝ) := rfl

theorem trace_eq_of_conjRel {γ' γ : SL(2, ℤ)} (h : conjRel g γ' γ) :
    ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  have hGL : Matrix.SpecialLinearGroup.mapGL ℝ γ = g * Matrix.SpecialLinearGroup.mapGL ℝ γ' * g⁻¹ := by
    unfold conjRel at h
    rw [h, mul_inv_cancel_right]
  have hmat := congrArg (fun M : GL (Fin 2) ℝ => Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℝ)) hGL
  simp only [Units.val_mul] at hmat
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, coe_mapGL,
    coe_mapGL, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace] at hmat
  simp only [eq_intCast] at hmat
  exact_mod_cast hmat

theorem conjRel_neg_one : conjRel g (-1) (-1) := by
  unfold conjRel
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_mapGL]
  simp [Matrix.map_neg, Matrix.map_one]

end ConjRel

section Main

variable (Γ' Γ'' : Subgroup SL(2, ℤ)) [Γ'.FiniteIndex] [Γ''.FiniteIndex]
  (hneg : (-1 : SL(2, ℤ)) ∈ Γ')
  (g : GL (Fin 2) ℝ) (e : Γ' ≃* Γ'') (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
  (he : ∀ γ : Γ', conjRel g (γ : SL(2, ℤ)) (e γ : SL(2, ℤ)))

include he in
theorem he_symm (γ : Γ'') : conjRel g (e.symm γ : SL(2, ℤ)) (γ : SL(2, ℤ)) := by
  have := he (e.symm γ)
  rwa [MulEquiv.apply_symm_apply] at this

include he hneg in

theorem neg_one_mem'' : (-1 : SL(2, ℤ)) ∈ Γ'' := by
  have h1 := he ⟨-1, hneg⟩
  have h2 : (e ⟨-1, hneg⟩ : SL(2, ℤ)) = -1 := conjRel.unique h1 conjRel_neg_one
  rw [← h2]
  exact (e ⟨-1, hneg⟩).2

include he in

theorem trace_e (γ : Γ') :
    ((e γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace :=
  trace_eq_of_conjRel (he γ)

theorem exists_frame_of_trace_two (v : SL(2, ℤ)) (htr : (v : Matrix (Fin 2) (Fin 2) ℤ).trace = 2)
    (hv : v ≠ 1) : ∃ (z : SL(2, ℤ)) (k : ℤ), k ≠ 0 ∧ v = z⁻¹ * ModularGroup.T ^ k * z := by
  obtain ⟨ε, δ, h, hε, hveq⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four v
    (by rw [htr]; norm_num)
  have hδ : δ * ModularGroup.T ^ h * δ⁻¹ = δ⁻¹⁻¹ * ModularGroup.T ^ h * δ⁻¹ := by rw [inv_inv]
  rcases hε with rfl | rfl
  · rw [one_mul] at hveq
    refine ⟨δ⁻¹, h, ?_, by rw [hveq, hδ]⟩
    rintro rfl
    apply hv
    rw [hveq, zpow_zero, mul_one, mul_inv_cancel]
  · exfalso
    rw [hveq, hδ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, neg_mul, one_mul, Matrix.trace_neg, trace_conj_T_zpow] at htr
    norm_num at htr

theorem genΔ_ne_one (Δ : Subgroup SL(2, ℤ)) [Δ.FiniteIndex] (z : SL(2, ℤ)) : (genΔ Δ z : SL(2, ℤ)) ≠ 1 := by
  intro h3
  simp only [coe_genΔ, gen] at h3
  have h4 : ModularGroup.T ^ ((width Δ (z : SL(2, ℤ) ⧸ Δ) : ℕ) : ℤ) = ModularGroup.T ^ (0 : ℤ) := by
    rw [zpow_zero]
    calc ModularGroup.T ^ ((width Δ (z : SL(2, ℤ) ⧸ Δ) : ℕ) : ℤ)
        = z * (z⁻¹ * ModularGroup.T ^ ((width Δ (z : SL(2, ℤ) ⧸ Δ) : ℕ) : ℤ) * z) * z⁻¹ := by group
      _ = 1 := by rw [h3]; group
  exact width_ne_zero Δ _ (by exact_mod_cast T_zpow_injective h4)

include hg he in

theorem exists_frame (z' : SL(2, ℤ)) :
    ∃ (z'' : SL(2, ℤ)) (k : ℤ), 0 < k ∧ (e (genΔ Γ' z') : SL(2, ℤ)) = z''⁻¹ * ModularGroup.T ^ k * z'' := by
  have htr : ((e (genΔ Γ' z') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [trace_e Γ' Γ'' g e he, coe_genΔ, gen, trace_conj_T_zpow]
  have hne : (e (genΔ Γ' z') : SL(2, ℤ)) ≠ 1 := by
    intro h1
    have h2 : e (genΔ Γ' z') = 1 := Subtype.ext h1
    rw [map_eq_one_iff _ e.injective] at h2
    exact genΔ_ne_one Γ' z' (congrArg (fun γ : Γ' => (γ : SL(2, ℤ))) h2)
  obtain ⟨z'', k, hk, hkeq⟩ := exists_frame_of_trace_two _ htr hne
  refine ⟨z'', k, ?_, hkeq⟩

  have hpos' : PosPar ((Matrix.SpecialLinearGroup.mapGL ℝ (genΔ Γ' z' : SL(2, ℤ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [coe_genΔ, gen, posPar_conj_T_zpow_iff]
    exact Int.natCast_nonneg _
  have hpos'' := (posPar_iff_of_conjRel g hg _ _ (he (genΔ Γ' z'))).mpr hpos'
  rw [hkeq, posPar_conj_T_zpow_iff] at hpos''
  exact lt_of_le_of_ne hpos'' (Ne.symm hk)

noncomputable def frame (z' : SL(2, ℤ)) : SL(2, ℤ) :=
  Classical.choose (exists_frame Γ' Γ'' g e hg he z')

noncomputable def kexp (z' : SL(2, ℤ)) : ℤ :=
  Classical.choose (Classical.choose_spec (exists_frame Γ' Γ'' g e hg he z'))

include hg he in
theorem kexp_pos (z' : SL(2, ℤ)) : 0 < kexp Γ' Γ'' g e hg he z' :=
  (Classical.choose_spec (Classical.choose_spec (exists_frame Γ' Γ'' g e hg he z'))).1

include hg he in
theorem e_genΔ (z' : SL(2, ℤ)) :
    (e (genΔ Γ' z') : SL(2, ℤ)) =
      (frame Γ' Γ'' g e hg he z')⁻¹ * ModularGroup.T ^ kexp Γ' Γ'' g e hg he z' *
        frame Γ' Γ'' g e hg he z' :=
  (Classical.choose_spec (Classical.choose_spec (exists_frame Γ' Γ'' g e hg he z'))).2

noncomputable def Ψ (Q' : Cusp Γ') : Cusp Γ'' :=
  Quotient.mk _ ((frame Γ' Γ'' g e hg he Q'.out.out : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'')

include hg he hneg in

theorem frame_rel {z₁ z₂ : SL(2, ℤ)} (γ : Γ')
    (h : genΔ Γ' z₂ = γ⁻¹ * genΔ Γ' z₁ * γ) :
    ((frame Γ' Γ'' g e hg he z₂ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') ∈
      orbit (Subgroup.zpowers ModularGroup.T)
        ((frame Γ' Γ'' g e hg he z₁ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') := by
  have h1 : (e (genΔ Γ' z₂) : SL(2, ℤ)) = (e γ : SL(2, ℤ))⁻¹ * (e (genΔ Γ' z₁) : SL(2, ℤ)) * (e γ) := by
    rw [h, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e_genΔ Γ' Γ'' g e hg he, e_genΔ Γ' Γ'' g e hg he] at h1
  have h2 : (frame Γ' Γ'' g e hg he z₂)⁻¹ * ModularGroup.T ^ kexp Γ' Γ'' g e hg he z₂ *
      frame Γ' Γ'' g e hg he z₂ =
      (frame Γ' Γ'' g e hg he z₁ * (e γ : SL(2, ℤ)))⁻¹ * ModularGroup.T ^ kexp Γ' Γ'' g e hg he z₁ *
        (frame Γ' Γ'' g e hg he z₁ * (e γ : SL(2, ℤ))) := by
    rw [h1]; group
  obtain ⟨⟨n, hn⟩, -⟩ := frame_unique (frame Γ' Γ'' g e hg he z₁ * (e γ : SL(2, ℤ)))
    (frame Γ' Γ'' g e hg he z₂) _ _ (kexp_pos Γ' Γ'' g e hg he z₁).ne' h2.symm
  refine mem_orbit_of_eq_neg Γ'' (neg_one_mem'' Γ' Γ'' hneg g e he) n (e γ : SL(2, ℤ)) (e γ).2 ?_
  rcases hn with hn | hn
  · left; rw [hn, mul_assoc]
  · right; rw [hn, mul_assoc]

include hg he hneg in

theorem frame_rel_of_mem_orbit {z₁ z₂ : SL(2, ℤ)}
    (h : (z₂ : SL(2, ℤ) ⧸ Γ') ∈ orbit (Subgroup.zpowers ModularGroup.T) (z₁ : SL(2, ℤ) ⧸ Γ')) :
    ((frame Γ' Γ'' g e hg he z₂ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') ∈
      orbit (Subgroup.zpowers ModularGroup.T)
        ((frame Γ' Γ'' g e hg he z₁ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') := by
  obtain ⟨n, δ, hδ, rfl⟩ := exists_of_mem_orbit Γ' h
  refine frame_rel Γ' Γ'' hneg g e hg he ⟨δ, hδ⟩ (Subtype.ext ?_)
  simp only [coe_genΔ, Subgroup.coe_mul, Subgroup.coe_inv]
  exact gen_T_zpow_mul Γ' z₁ δ hδ n

include hg he hneg in

theorem Ψ_injective : Function.Injective (Ψ Γ' Γ'' g e hg he) := by
  letI s' := orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ')
  letI s'' := orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ'')
  intro Q₁ Q₂ hΨ
  set z₁ := Q₁.out.out with hz₁
  set z₂ := Q₂.out.out with hz₂
  set f₁ := frame Γ' Γ'' g e hg he z₁ with hf₁
  set k₁ := kexp Γ' Γ'' g e hg he z₁ with hk₁
  set k₂ := kexp Γ' Γ'' g e hg he z₂ with hk₂

  have hrel : ((frame Γ' Γ'' g e hg he z₂ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') ∈
      orbit (Subgroup.zpowers ModularGroup.T) ((f₁ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') :=
    orbitRel_apply.mp (Quotient.exact hΨ.symm)
  obtain ⟨n, γ'', hγ'', hf₂⟩ := exists_of_mem_orbit Γ'' hrel

  set γ' : Γ' := e.symm ⟨γ'', hγ''⟩ with hγ'
  have hv₂ : (e (genΔ Γ' z₂) : SL(2, ℤ)) = γ''⁻¹ * (f₁⁻¹ * ModularGroup.T ^ k₂ * f₁) * γ'' := by
    rw [e_genΔ Γ' Γ'' g e hg he, hf₂]
    exact conj_conj f₁ γ'' n k₂
  have h3 : (e (γ' * genΔ Γ' z₂ * γ'⁻¹) : SL(2, ℤ)) = f₁⁻¹ * ModularGroup.T ^ k₂ * f₁ := by
    rw [map_mul, map_mul, map_inv, hγ', MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_mk, hv₂]
    group
  have hcomm'' : (e (γ' * genΔ Γ' z₂ * γ'⁻¹) : SL(2, ℤ)) * (e (genΔ Γ' z₁) : SL(2, ℤ)) =
      (e (genΔ Γ' z₁) : SL(2, ℤ)) * (e (γ' * genΔ Γ' z₂ * γ'⁻¹) : SL(2, ℤ)) := by
    rw [h3, e_genΔ Γ' Γ'' g e hg he]
    change f₁⁻¹ * ModularGroup.T ^ k₂ * f₁ * (f₁⁻¹ * ModularGroup.T ^ k₁ * f₁) =
      f₁⁻¹ * ModularGroup.T ^ k₁ * f₁ * (f₁⁻¹ * ModularGroup.T ^ k₂ * f₁)
    group
  have hcomm' : (γ' * genΔ Γ' z₂ * γ'⁻¹) * genΔ Γ' z₁ = genΔ Γ' z₁ * (γ' * genΔ Γ' z₂ * γ'⁻¹) := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul e (γ' * genΔ Γ' z₂ * γ'⁻¹) (genΔ Γ' z₁), map_mul e (genΔ Γ' z₁) (γ' * genΔ Γ' z₂ * γ'⁻¹),
      Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcomm''
  have hcommSL := congrArg (fun γ : Γ' => (γ : SL(2, ℤ))) hcomm'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_genΔ, gen] at hcommSL

  have hy : (γ' : SL(2, ℤ)) * (z₂⁻¹ * ModularGroup.T ^ ((width Γ' (z₂ : SL(2, ℤ) ⧸ Γ') : ℕ) : ℤ) * z₂) *
      (γ' : SL(2, ℤ))⁻¹ = (z₂ * (γ' : SL(2, ℤ))⁻¹)⁻¹ *
        ModularGroup.T ^ ((width Γ' (z₂ : SL(2, ℤ) ⧸ Γ') : ℕ) : ℤ) * (z₂ * (γ' : SL(2, ℤ))⁻¹) := by group
  rw [hy] at hcommSL
  obtain ⟨m, hm⟩ := frame_eq_of_commute z₁ (z₂ * (γ' : SL(2, ℤ))⁻¹) _ _
    (by exact_mod_cast width_ne_zero Γ' _) (by exact_mod_cast width_ne_zero Γ' _) hcommSL.symm

  have horb : (z₂ : SL(2, ℤ) ⧸ Γ') ∈ orbit (Subgroup.zpowers ModularGroup.T) (z₁ : SL(2, ℤ) ⧸ Γ') := by
    refine mem_orbit_of_eq_neg Γ' hneg m (γ' : SL(2, ℤ)) γ'.2 ?_
    rcases hm with hm | hm
    · left
      calc z₂ = z₂ * (γ' : SL(2, ℤ))⁻¹ * γ' := by group
        _ = ModularGroup.T ^ m * z₁ * γ' := by rw [hm]
    · right
      calc z₂ = z₂ * (γ' : SL(2, ℤ))⁻¹ * γ' := by group
        _ = -(ModularGroup.T ^ m * z₁ * γ') := by rw [hm, neg_mul]
  rw [hz₁, hz₂, QuotientGroup.out_eq', QuotientGroup.out_eq'] at horb
  have : Q₂.out ≈ Q₁.out := orbitRel_apply.mpr horb
  exact (Quotient.out_equiv_out.mp this).symm

include hg he hneg in

theorem Ψ_surjective : Function.Surjective (Ψ Γ' Γ'' g e hg he) := by
  letI s' := orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ')
  letI s'' := orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ'')
  intro Q''
  set z'' := Q''.out.out with hz''

  set u' : Γ' := e.symm (genΔ Γ'' z'') with hu'
  have htr : ((u' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [← trace_eq_of_conjRel (he_symm Γ' Γ'' g e he (genΔ Γ'' z'')), coe_genΔ, gen, trace_conj_T_zpow]
  have hne : (u' : SL(2, ℤ)) ≠ 1 := by
    intro h1
    have h2 : u' = 1 := Subtype.ext h1
    rw [hu', map_eq_one_iff _ e.symm.injective] at h2
    exact genΔ_ne_one Γ'' z'' (congrArg (fun γ : Γ'' => (γ : SL(2, ℤ))) h2)
  obtain ⟨z', h', hh', hu'eq⟩ := exists_frame_of_trace_two _ htr hne
  refine ⟨Quotient.mk _ ((z' : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'), ?_⟩
  set Q' : Cusp Γ' := Quotient.mk _ ((z' : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ') with hQ'
  have horb1 : (Q'.out.out : SL(2, ℤ) ⧸ Γ') ∈ orbit (Subgroup.zpowers ModularGroup.T)
      (z' : SL(2, ℤ) ⧸ Γ') := by
    rw [QuotientGroup.out_eq']
    exact orbitRel_apply.mp (Quotient.mk_out (z' : SL(2, ℤ) ⧸ Γ'))
  have hrel := frame_rel_of_mem_orbit Γ' Γ'' hneg g e hg he horb1

  set f := frame Γ' Γ'' g e hg he z' with hf
  set k := kexp Γ' Γ'' g e hg he z' with hk
  have hcomm' : genΔ Γ' z' * u' = u' * genΔ Γ' z' := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_genΔ, gen, hu'eq]
    group
  have hcomm'' := congrArg (fun γ : Γ' => ((e γ : Γ'') : SL(2, ℤ))) hcomm'
  simp only [map_mul, Subgroup.coe_mul, hu', MulEquiv.apply_symm_apply, coe_genΔ, gen,
    e_genΔ Γ' Γ'' g e hg he] at hcomm''
  obtain ⟨m, hm⟩ := frame_eq_of_commute z'' f _ k
    (by exact_mod_cast width_ne_zero Γ'' _) (kexp_pos Γ' Γ'' g e hg he z').ne' hcomm''.symm
  have horb2 : (f : SL(2, ℤ) ⧸ Γ'') ∈ orbit (Subgroup.zpowers ModularGroup.T) (z'' : SL(2, ℤ) ⧸ Γ'') := by
    refine mem_orbit_of_eq_neg Γ'' (neg_one_mem'' Γ' Γ'' hneg g e he) m 1 Γ''.one_mem ?_
    simpa using hm
  have hfin : ((frame Γ' Γ'' g e hg he Q'.out.out : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') ∈
      orbit (Subgroup.zpowers ModularGroup.T) (z'' : SL(2, ℤ) ⧸ Γ'') := by
    rw [← orbit_eq_iff.mpr horb2]
    exact hrel
  calc Ψ Γ' Γ'' g e hg he Q'
      = Quotient.mk _ ((frame Γ' Γ'' g e hg he Q'.out.out : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') := rfl
    _ = Quotient.mk _ ((z'' : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') := Quotient.sound (orbitRel_apply.mpr hfin)
    _ = Quotient.mk _ Q''.out := by rw [hz'', QuotientGroup.out_eq']
    _ = Q'' := Quotient.out_eq Q''

include hg he in

theorem e_genΔ_eq_genΔ_frame (z₁ : SL(2, ℤ)) :
    e (genΔ Γ' z₁) = genΔ Γ'' (frame Γ' Γ'' g e hg he z₁) := by
  have hk₁pos := kexp_pos Γ' Γ'' g e hg he z₁
  have hev := e_genΔ Γ' Γ'' g e hg he z₁
  set f₁ := frame Γ' Γ'' g e hg he z₁ with hf₁
  set k₁ := kexp Γ' Γ'' g e hg he z₁ with hk₁
  set w'' : ℤ := ((width Γ'' (f₁ : SL(2, ℤ) ⧸ Γ'') : ℕ) : ℤ) with hw''

  have hdvd1 : w'' ∣ k₁ := by
    have hmem : f₁⁻¹ * ModularGroup.T ^ k₁ * f₁ ∈ Γ'' := by rw [← hev]; exact (e (genΔ Γ' z₁)).2
    exact (conj_zpow_mem_iff Γ'' f₁ k₁).mp hmem

  set p' : Γ' := e.symm (genΔ Γ'' f₁) with hp'
  have htr : ((p' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [← trace_eq_of_conjRel (he_symm Γ' Γ'' g e he (genΔ Γ'' f₁)), coe_genΔ, gen, trace_conj_T_zpow]
  have hne : (p' : SL(2, ℤ)) ≠ 1 := by
    intro h1
    have h2 : p' = 1 := Subtype.ext h1
    rw [hp', map_eq_one_iff _ e.symm.injective] at h2
    exact genΔ_ne_one Γ'' f₁ (congrArg (fun γ : Γ'' => (γ : SL(2, ℤ))) h2)
  obtain ⟨y, b, hb, hp'eq⟩ := exists_frame_of_trace_two _ htr hne

  have hcomm'' : (e p' : SL(2, ℤ)) * (e (genΔ Γ' z₁) : SL(2, ℤ)) =
      (e (genΔ Γ' z₁) : SL(2, ℤ)) * (e p' : SL(2, ℤ)) := by
    rw [hp', MulEquiv.apply_symm_apply, coe_genΔ, gen, hev, ← hw'']
    group
  have hcomm' : p' * genΔ Γ' z₁ = genΔ Γ' z₁ * p' := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul e p' (genΔ Γ' z₁), map_mul e (genΔ Γ' z₁) p', Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcomm''
  have hcommSL := congrArg (fun γ : Γ' => (γ : SL(2, ℤ))) hcomm'
  simp only [Subgroup.coe_mul, coe_genΔ, gen, hp'eq] at hcommSL
  obtain ⟨n, hn⟩ := frame_eq_of_commute z₁ y _ b (by exact_mod_cast width_ne_zero Γ' _) hb hcommSL.symm

  have hp'z : (p' : SL(2, ℤ)) = z₁⁻¹ * ModularGroup.T ^ b * z₁ := by
    rw [hp'eq]
    rcases hn with rfl | rfl
    · group
    · rw [← neg_inv, neg_mul, neg_mul_neg]
      group

  obtain ⟨c, hc⟩ := (conj_zpow_mem_iff Γ' z₁ b).mp (by rw [← hp'z]; exact p'.2)

  have hp'pow : p' = genΔ Γ' z₁ ^ c := by
    apply Subtype.ext
    rw [hp'z, Subgroup.coe_zpow, coe_genΔ, gen, conj_T_zpow_zpow, ← hc]
  have himg : (genΔ Γ'' f₁ : SL(2, ℤ)) = (e (genΔ Γ' z₁) : SL(2, ℤ)) ^ c := by
    rw [← Subgroup.coe_zpow, ← map_zpow, ← hp'pow, hp', MulEquiv.apply_symm_apply]
  rw [hev, conj_T_zpow_zpow, coe_genΔ, gen] at himg
  have hT : ModularGroup.T ^ w'' = ModularGroup.T ^ (k₁ * c) := by
    have h1 : ModularGroup.T ^ w'' = f₁ * (f₁⁻¹ * ModularGroup.T ^ w'' * f₁) * f₁⁻¹ := by group
    rw [h1, hw'', himg]; group
  have hdvd2 : k₁ ∣ w'' := ⟨c, T_zpow_injective hT⟩

  have hkw : k₁ = w'' := Int.dvd_antisymm hk₁pos.le (Int.natCast_nonneg _) hdvd2 hdvd1
  apply Subtype.ext
  rw [hev, coe_genΔ, gen, ← hw'', hkw]

include hg he in

theorem F_e_cuspGen (F : Γ'' → ℚ)
    (hF : ∀ p δ : Γ'', ((p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → F (δ * p * δ⁻¹) = F p)
    (Q' : Cusp Γ') : F (e (cuspGen Γ' Q')) = F (cuspGen Γ'' (Ψ Γ' Γ'' g e hg he Q')) := by
  letI s'' := orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ'')
  set z₁ := Q'.out.out with hz₁
  set f₁ := frame Γ' Γ'' g e hg he z₁ with hf₁
  rw [cuspGen_eq, cuspGen_eq, e_genΔ_eq_genΔ_frame Γ' Γ'' g e hg he]

  have horb : ((Ψ Γ' Γ'' g e hg he Q').out.out : SL(2, ℤ) ⧸ Γ'') ∈
      orbit (Subgroup.zpowers ModularGroup.T) ((f₁ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ'') := by
    rw [QuotientGroup.out_eq']
    exact orbitRel_apply.mp (Quotient.mk_out ((f₁ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ''))
  obtain ⟨n, δ, hδ, hout⟩ := exists_of_mem_orbit Γ'' horb
  have hgen : genΔ Γ'' (Ψ Γ' Γ'' g e hg he Q').out.out = (⟨δ, hδ⟩ : Γ'')⁻¹ * genΔ Γ'' f₁ * ⟨δ, hδ⟩ := by
    apply Subtype.ext
    simp only [coe_genΔ, Subgroup.coe_mul, Subgroup.coe_inv, hout]
    exact gen_T_zpow_mul Γ'' f₁ δ hδ n
  rw [hgen]
  have := hF (genΔ Γ'' f₁) (⟨δ, hδ⟩ : Γ'')⁻¹ (trace_gen_sq Γ'' f₁)
  rw [inv_inv] at this
  exact this.symm

include hg he hneg in

theorem main (F : Γ'' → ℚ)
    (hF : ∀ p δ : Γ'', ((p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → F (δ * p * δ⁻¹) = F p) :
    cuspSum Γ' (fun γ => F (e γ)) = cuspSum Γ'' F := by
  unfold cuspSum
  exact Fintype.sum_bijective (Ψ Γ' Γ'' g e hg he)
    ⟨Ψ_injective Γ' Γ'' hneg g e hg he, Ψ_surjective Γ' Γ'' hneg g e hg he⟩ _ _
    (fun Q' => F_e_cuspGen Γ' Γ'' g e hg he F hF Q')

end Main

end ModularCurve.CupPairing.CuspTransport
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel.ModularCurve P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel.ModularCurve.CupPairing P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel.ModularCurve.CupPairing.CuspTransport"
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel.ModularCurve P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel.ModularCurve.CupPairing"
p2m_reactivate "P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel.ModularCurve"

theorem solution (Γ' Γ'' : Subgroup SL(2, ℤ))
    [Γ'.FiniteIndex] [Γ''.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ')
    (g : GL (Fin 2) ℝ) (e : Γ' ≃* Γ'') (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (he : ∀ γ : Γ', ModularCurve.Period.conjRel g (γ : SL(2, ℤ)) (e γ : SL(2, ℤ)))
    (F : Γ'' → ℚ)
    (hF : ∀ p δ : Γ'', ((p : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
      F (δ * p * δ⁻¹) = F p) :
    ModularCurve.PDPairing.cuspSum Γ' (fun γ => F (e γ)) = ModularCurve.PDPairing.cuspSum Γ'' F :=
  ModularCurve.CupPairing.CuspTransport.main Γ' Γ'' hneg g e hg he F hF

end S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel
end P2MW
export P2MW.S_ModularCurve_CupPairing_cuspSum_comp_eq_of_conjRel (solution)
