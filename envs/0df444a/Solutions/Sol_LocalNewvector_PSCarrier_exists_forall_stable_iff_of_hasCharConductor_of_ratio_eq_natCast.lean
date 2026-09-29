-- Prove2me | solution 1 for LocalNewvector.PSCarrier.exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fc639b89-2869-5f62-8bfa-7a1e36e19215

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Theorems.Thm_LocalNewvector_mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_PSCarrier_exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
p2m_attr_erase "instance" "FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

noncomputable section

namespace PSRatioP

open LocalNewvector

variable (p : ℕ) [hp : Fact p.Prime]

private theorem qp_ne_zero : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero

private theorem pR_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos

private def ϖ : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

private theorem coe_ϖ : ((ϖ p : ℚ_[p]ˣ) : ℚ_[p]) = (p : ℚ_[p]) := rfl

private theorem norm_ϖ : ‖((ϖ p : ℚ_[p]ˣ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [coe_ϖ]; exact Padic.norm_p

theorem halfModulus_pos (a₁ a₂ : ℚ_[p]ˣ) : 0 < Real.sqrt (‖(a₁ : ℚ_[p])‖ / ‖(a₂ : ℚ_[p])‖) :=
  Real.sqrt_pos.mpr (div_pos (norm_pos_iff.mpr a₁.ne_zero) (norm_pos_iff.mpr a₂.ne_zero))

theorem halfModulus_ne_zero (a₁ a₂ : ℚ_[p]ˣ) : halfModulus p a₁ a₂ ≠ 0 := by
  unfold halfModulus
  exact_mod_cast (halfModulus_pos p a₁ a₂).ne'

theorem halfModulus_one_right (a : ℚ_[p]ˣ) : halfModulus p a 1 = ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ) := by
  simp [halfModulus]

theorem halfModulus_mul_one (a b : ℚ_[p]ˣ) : halfModulus p (a * b) 1 = halfModulus p a 1 * halfModulus p b 1 := by
  rw [← halfModulus_mul, mul_one]

theorem exists_borelElem_eq {b : GL (Fin 2) ℚ_[p]} (hb : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0) :
    ∃ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]), b = borelElem p a₁ a₂ x := by
  have hdet : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det b).ne_zero
  rw [Matrix.det_fin_two, hb, mul_zero, sub_zero] at hdet
  have h₀ : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h₁ : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ h₀, Units.mk0 _ h₁, (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1, Units.ext ?_⟩
  rw [coe_borelElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb]

theorem exists_forall_apply_upper_mul {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {b : GL (Fin 2) ℚ_[p]}
    (hb : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0) :
    ∃ χ : ℂ, χ ≠ 0 ∧ ∀ F ∈ principalSeries p μ₁ μ₂, ∀ g : GL (Fin 2) ℚ_[p], F (b * g) = χ * F g := by
  obtain ⟨a₁, a₂, x, rfl⟩ := exists_borelElem_eq p hb
  refine ⟨(μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂,
    mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (halfModulus_ne_zero p a₁ a₂), ?_⟩
  intro F hF g
  exact apply_borelElem_mul_of_mem_principalSeries p hF a₁ a₂ x g

section CharIdentity

variable {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}

theorem exists_eq_mul_zpow (a : ℚ_[p]ˣ) : ∃ (u : ℚ_[p]ˣ) (k : ℤ), ‖(u : ℚ_[p])‖ = 1 ∧ a = u * (ϖ p) ^ k := by
  set k : ℤ := (a : ℚ_[p]).valuation with hk
  refine ⟨a * (ϖ p) ^ (-k), k, ?_, by rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, norm_ϖ,
    Padic.norm_eq_zpow_neg_valuation a.ne_zero, ← hk, inv_zpow', neg_neg, ← zpow_add₀ (pR_pos p).ne',
    neg_add_cancel, zpow_zero]

theorem coe_apply_eq_mul_norm (hrat : IsUnramified p (μ₁⁻¹ * μ₂))
    (hγ : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) *
        ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹ = (p : ℂ))
    (a : ℚ_[p]ˣ) : (μ₂ a : ℂ) = (μ₁ a : ℂ) * ‖(a : ℚ_[p])‖ := by

  have hunit : ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 → μ₂ u = μ₁ u := by
    intro u hu
    have h := hrat u hu
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_eq_one] at h
    exact h.symm

  have hϖ : (μ₂ (ϖ p) : ℂ) = (μ₁ (ϖ p) : ℂ) * (p : ℂ)⁻¹ := by
    change (μ₁ (ϖ p) : ℂ) * ((μ₂ (ϖ p) : ℂ))⁻¹ = (p : ℂ) at hγ
    have h2 : (μ₂ (ϖ p) : ℂ) ≠ 0 := Units.ne_zero _
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    field_simp
    field_simp at hγ
    linear_combination -hγ
  obtain ⟨u, k, hu, rfl⟩ := exists_eq_mul_zpow p a
  rw [map_mul, map_mul, map_zpow, map_zpow, Units.val_mul, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.val_zpow_eq_zpow_val, hunit u hu, hϖ, mul_zpow, Units.val_mul, norm_mul, hu, one_mul,
    Units.val_zpow_eq_zpow_val, norm_zpow, norm_ϖ, inv_zpow', inv_zpow']
  push_cast
  ring

end CharIdentity

section TwistChar

variable (μ₁ : ℚ_[p]ˣ →* ℂˣ)

def Tfn (g : GL (Fin 2) ℚ_[p]) : ℂ :=
  (μ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) * halfModulus p (Matrix.GeneralLinearGroup.det g) 1

theorem Tfn_apply (g : GL (Fin 2) ℚ_[p]) :
    Tfn p μ₁ g = (μ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) * halfModulus p (Matrix.GeneralLinearGroup.det g) 1 :=
  rfl

theorem Tfn_mul (g h : GL (Fin 2) ℚ_[p]) : Tfn p μ₁ (g * h) = Tfn p μ₁ g * Tfn p μ₁ h := by
  simp only [Tfn, map_mul, Units.val_mul, halfModulus_mul_one]
  ring

theorem Tfn_one : Tfn p μ₁ 1 = 1 := by
  simp [Tfn]

theorem Tfn_ne_zero (g : GL (Fin 2) ℚ_[p]) : Tfn p μ₁ g ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (halfModulus_ne_zero p _ _)

theorem det_mem_higherUnits {L : ℕ} (hL : 1 ≤ L) {m : GL (Fin 2) ℚ_[p]}
    (hm : m ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p L) :
    Matrix.GeneralLinearGroup.det m ∈ higherUnits p L := by
  have h := ((FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff p).mp hm).1
  set A : Matrix (Fin 2) (Fin 2) ℚ_[p] := (m : Matrix (Fin 2) (Fin 2) ℚ_[p]) with hA
  have hr1 : (p : ℝ) ^ (-(L : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hp.out.one_lt.le))
  have hlt1 : (p : ℝ) ^ (-(L : ℤ)) < 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by exact_mod_cast hp.out.one_lt) (by omega))
  have h00 : ‖A 0 0 - 1‖ ≤ (p : ℝ) ^ (-(L : ℤ)) := by
    have := h 0 0; rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this
  have h11 : ‖A 1 1 - 1‖ ≤ (p : ℝ) ^ (-(L : ℤ)) := by
    have := h 1 1; rwa [Matrix.sub_apply, Matrix.one_apply_eq] at this
  have h01 : ‖A 0 1‖ ≤ (p : ℝ) ^ (-(L : ℤ)) := by
    have := h 0 1; rwa [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at this
  have h10 : ‖A 1 0‖ ≤ (p : ℝ) ^ (-(L : ℤ)) := by
    have := h 1 0; rwa [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at this
  have hdet : ((Matrix.GeneralLinearGroup.det m : ℚ_[p]ˣ) : ℚ_[p]) = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hsub : ((Matrix.GeneralLinearGroup.det m : ℚ_[p]ˣ) : ℚ_[p]) - 1
      = (A 0 0 - 1) * (A 1 1 - 1) + ((A 0 0 - 1) + (A 1 1 - 1)) + -(A 0 1 * A 1 0) := by
    rw [hdet]; ring
  have hball : ‖((Matrix.GeneralLinearGroup.det m : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(L : ℤ)) := by
    rw [hsub]
    refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le ?_ ?_)) ?_)
    · rw [norm_mul]
      calc ‖A 0 0 - 1‖ * ‖A 1 1 - 1‖ ≤ (p : ℝ) ^ (-(L : ℤ)) * 1 :=
            mul_le_mul h00 (h11.trans hr1) (norm_nonneg _) (zpow_nonneg (pR_pos p).le _)
        _ = (p : ℝ) ^ (-(L : ℤ)) := mul_one _
    · exact (Padic.nonarchimedean _ _).trans (max_le h00 h11)
    · rw [norm_neg, norm_mul]
      calc ‖A 0 1‖ * ‖A 1 0‖ ≤ (p : ℝ) ^ (-(L : ℤ)) * 1 :=
            mul_le_mul h01 (h10.trans hr1) (norm_nonneg _) (zpow_nonneg (pR_pos p).le _)
        _ = (p : ℝ) ^ (-(L : ℤ)) := mul_one _
  refine ⟨FLT.SmoothVectors.norm_eq_one_of_norm_sub_one_lt_one p (hball.trans_lt hlt1), Or.inr hball⟩

theorem Tfn_eq_one_of_mem {c : ℕ} (h₁ : HasCharConductor p μ₁ c) {L : ℕ} (hL : 1 ≤ L) (hcL : c ≤ L)
    {m : GL (Fin 2) ℚ_[p]} (hm : m ∈ FLT.SmoothVectors.gl2CongruenceSubgroup p L) : Tfn p μ₁ m = 1 := by
  have hdet := det_mem_higherUnits p hL hm
  rw [Tfn, h₁.1 _ (higherUnits_antitone p hcL hdet), Units.val_one, one_mul]
  exact halfModulus_eq_one_of_norm_eq_one p hdet.1 (by simp)

theorem isLocallyConstant_Tfn {c : ℕ} (h₁ : HasCharConductor p μ₁ c) : IsLocallyConstant (Tfn p μ₁) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  set L : ℕ := max 1 c with hL
  refine ⟨(fun m => x * m) '' (FLT.SmoothVectors.gl2CongruenceSubgroup p L : Set (GL (Fin 2) ℚ_[p])),
    (isOpenMap_mul_left x) _ (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup p L),
    ⟨1, (FLT.SmoothVectors.gl2CongruenceSubgroup p L).one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  rw [Tfn_mul, Tfn_eq_one_of_mem p μ₁ h₁ (le_max_left _ _) (le_max_right _ _) hm, mul_one]

private theorem sqrt_identity {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) :
    Real.sqrt (r₁ / 1) * Real.sqrt (r₂ / 1) = r₂ * Real.sqrt (r₁ / r₂) := by
  rw [div_one, div_one, Real.sqrt_div h₁, mul_div_assoc', mul_comm r₂, mul_div_assoc, Real.div_sqrt]

variable {μ₁}

theorem Tfn_mem_principalSeries {μ₂ : ℚ_[p]ˣ →* ℂˣ} {c : ℕ} (h₁ : HasCharConductor p μ₁ c)
    (hμ₂ : ∀ a : ℚ_[p]ˣ, (μ₂ a : ℂ) = (μ₁ a : ℂ) * ‖(a : ℚ_[p])‖) :
    Tfn p μ₁ ∈ principalSeries p μ₁ μ₂ := by
  refine (mem_principalSeries_iff p).mpr ⟨isLocallyConstant_Tfn p μ₁ h₁, fun a₁ a₂ x g => ?_⟩
  have hdet : Matrix.GeneralLinearGroup.det (borelElem p a₁ a₂ x) = a₁ * a₂ := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_borelElem, Matrix.det_fin_two_of, Units.val_mul]
    ring
  rw [Tfn_mul, Tfn, hdet, map_mul, Units.val_mul, halfModulus_mul_one, hμ₂ a₂, halfModulus_one_right,
    halfModulus_one_right, Tfn]
  unfold halfModulus
  have hreal : ((‖(a₂ : ℚ_[p])‖ : ℝ) : ℂ) * (Real.sqrt (‖(a₁ : ℚ_[p])‖ / ‖(a₂ : ℚ_[p])‖) : ℂ)
      = (Real.sqrt ‖(a₁ : ℚ_[p])‖ : ℂ) * (Real.sqrt ‖(a₂ : ℚ_[p])‖ : ℂ) := by
    have h := sqrt_identity (r₂ := ‖(a₂ : ℚ_[p])‖) (norm_nonneg (a₁ : ℚ_[p]))
    rw [div_one, div_one] at h
    exact_mod_cast h.symm
  linear_combination ((μ₁ a₁ : ℂ) * (μ₁ a₂ : ℂ) *
    ((μ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
      (Real.sqrt (‖((Matrix.GeneralLinearGroup.det g : ℚ_[p]ˣ) : ℚ_[p])‖ / ‖((1 : ℚ_[p]ˣ) : ℚ_[p])‖) : ℂ))) * hreal.symm

end TwistChar

section Twist

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def twLin : PSCarrier p μ₁ μ₂ →ₗ[ℂ] (GL (Fin 2) ℚ_[p] → ℂ) where
  toFun w := fun g => (Tfn p μ₁ g)⁻¹ * PSCarrier.toFn p μ₁ μ₂ w g
  map_add' w w' := by
    funext g
    change (Tfn p μ₁ g)⁻¹ * (PSCarrier.toFn p μ₁ μ₂ w g + PSCarrier.toFn p μ₁ μ₂ w' g) = _
    rw [mul_add]
    rfl
  map_smul' c w := by
    funext g
    change (Tfn p μ₁ g)⁻¹ * (c * PSCarrier.toFn p μ₁ μ₂ w g) = c * ((Tfn p μ₁ g)⁻¹ * PSCarrier.toFn p μ₁ μ₂ w g)
    ring

theorem twLin_apply (w : PSCarrier p μ₁ μ₂) (g : GL (Fin 2) ℚ_[p]) :
    twLin p μ₁ μ₂ w g = (Tfn p μ₁ g)⁻¹ * PSCarrier.toFn p μ₁ μ₂ w g := rfl

theorem toFn_eq_Tfn_mul_twLin (w : PSCarrier p μ₁ μ₂) (g : GL (Fin 2) ℚ_[p]) :
    PSCarrier.toFn p μ₁ μ₂ w g = Tfn p μ₁ g * twLin p μ₁ μ₂ w g := by
  rw [twLin_apply, ← mul_assoc, mul_inv_cancel₀ (Tfn_ne_zero p μ₁ g), one_mul]

theorem twLin_injective : Function.Injective (twLin p μ₁ μ₂) := by
  intro w w' h
  refine PSCarrier.ext p μ₁ μ₂ fun g => ?_
  rw [toFn_eq_Tfn_mul_twLin, toFn_eq_Tfn_mul_twLin, h]

theorem rt_twLin (h : GL (Fin 2) ℚ_[p]) (w : PSCarrier p μ₁ μ₂) :
    (fun g => twLin p μ₁ μ₂ w (g * h)) = (Tfn p μ₁ h)⁻¹ • twLin p μ₁ μ₂ (h • w) := by
  funext g
  rw [Pi.smul_apply, smul_eq_mul, twLin_apply, twLin_apply, PSCarrier.toFn_smul, Tfn_mul, mul_inv]
  ring

theorem twLin_upper_mul (hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂) (w : PSCarrier p μ₁ μ₂)
    {b : GL (Fin 2) ℚ_[p]} (hb : (b : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 = 0) (g : GL (Fin 2) ℚ_[p]) :
    twLin p μ₁ μ₂ w (b * g) = twLin p μ₁ μ₂ w g := by
  obtain ⟨χ, hχ, hlaw⟩ := exists_forall_apply_upper_mul p (μ₁ := μ₁) (μ₂ := μ₂) hb
  rw [twLin_apply, twLin_apply, hlaw _ hT g, hlaw _ (PSCarrier.toFn_mem p μ₁ μ₂ w) g, mul_inv]
  field_simp

theorem isLocallyConstant_twLin (hT : IsLocallyConstant (Tfn p μ₁)) (w : PSCarrier p μ₁ μ₂) :
    IsLocallyConstant (twLin p μ₁ μ₂ w) :=
  hT.comp₂ (isLocallyConstant_of_mem_principalSeries p (PSCarrier.toFn_mem p μ₁ μ₂ w)) (fun a b => a⁻¹ * b)

end Twist

section Classification

variable {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}

def Tps (hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂) : PSCarrier p μ₁ μ₂ :=
  PSCarrier.mk p μ₁ μ₂ ⟨Tfn p μ₁, hT⟩

theorem toFn_Tps (hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂) (g : GL (Fin 2) ℚ_[p]) :
    PSCarrier.toFn p μ₁ μ₂ (Tps p hT) g = Tfn p μ₁ g := rfl

theorem smul_Tps (hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂) (h : GL (Fin 2) ℚ_[p]) :
    h • Tps p hT = Tfn p μ₁ h • Tps p hT := by
  refine PSCarrier.ext p μ₁ μ₂ fun g => ?_
  rw [PSCarrier.toFn_smul, PSCarrier.toFn_csmul, toFn_Tps, toFn_Tps, Tfn_mul, mul_comm]

theorem span_Tps_stable (hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂) (h : GL (Fin 2) ℚ_[p])
    (v : PSCarrier p μ₁ μ₂) (hv : v ∈ Submodule.span ℂ {Tps p hT}) : h • v ∈ Submodule.span ℂ {Tps p hT} := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [smul_comm, smul_Tps, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨c * Tfn p μ₁ h, rfl⟩

theorem twLin_Tps (hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂) (g : GL (Fin 2) ℚ_[p]) :
    twLin p μ₁ μ₂ (Tps p hT) g = 1 := by
  rw [twLin_apply, toFn_Tps, inv_mul_cancel₀ (Tfn_ne_zero p μ₁ g)]

theorem mem_span_Tps_of_forall_twLin_eq (hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂) (w : PSCarrier p μ₁ μ₂)
    (hw : ∀ g, twLin p μ₁ μ₂ w g = twLin p μ₁ μ₂ w 1) : w ∈ Submodule.span ℂ {Tps p hT} := by
  refine Submodule.mem_span_singleton.mpr ⟨twLin p μ₁ μ₂ w 1, ?_⟩
  refine PSCarrier.ext p μ₁ μ₂ fun g => ?_
  rw [PSCarrier.toFn_csmul, toFn_Tps, toFn_eq_Tfn_mul_twLin p μ₁ μ₂ w g, hw g, mul_comm]

theorem eq_top_of_stable_of_not_mem_span {c : ℕ} (h₁ : HasCharConductor p μ₁ c)
    (hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂)
    (W : Submodule ℂ (PSCarrier p μ₁ μ₂)) (hW : ∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W)
    {x : PSCarrier p μ₁ μ₂} (hxW : x ∈ W) (hx : x ∉ Submodule.span ℂ {Tps p hT}) : W = ⊤ := by
  have hTlc : IsLocallyConstant (Tfn p μ₁) := isLocallyConstant_Tfn p μ₁ h₁

  set S : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ) := W.map (twLin p μ₁ μ₂) with hS
  have hSrt : ∀ (h : GL (Fin 2) ℚ_[p]), ∀ F ∈ S, (fun g => F (g * h)) ∈ S := by
    intro h F hF
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hF
    rw [rt_twLin]
    exact S.smul_mem _ (Submodule.mem_map_of_mem (hW h w hw))

  have hnc : ∃ g, twLin p μ₁ μ₂ x g ≠ twLin p μ₁ μ₂ x 1 := by
    by_contra hall
    push Not at hall
    exact hx (mem_span_Tps_of_forall_twLin_eq p hT x hall)
  rw [eq_top_iff]
  intro y _
  have hmem : twLin p μ₁ μ₂ y ∈ S :=
    LocalNewvector.mem_of_isLocallyConstant_of_borelInvariant_of_rightTranslate_stable p S hSrt
      (twLin p μ₁ μ₂ x) (Submodule.mem_map_of_mem hxW) (isLocallyConstant_twLin p μ₁ μ₂ hTlc x)
      (fun b g hb => twLin_upper_mul p μ₁ μ₂ hT x hb g) hnc
      (twLin p μ₁ μ₂ y) (isLocallyConstant_twLin p μ₁ μ₂ hTlc y) (fun b g hb => twLin_upper_mul p μ₁ μ₂ hT y hb g)
  obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.mp hmem
  rw [← twLin_injective p μ₁ μ₂ hwy]
  exact hw

theorem eq_bot_or_eq_of_le_span {V : Type*} [AddCommGroup V] [Module ℂ V] {T : V} {W : Submodule ℂ V}
    (hle : W ≤ Submodule.span ℂ {T}) : W = ⊥ ∨ W = Submodule.span ℂ {T} := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    refine le_antisymm hle ?_
    obtain ⟨w, hwW, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hle hwW)
    have hc : c ≠ 0 := by rintro rfl; exact hwne (zero_smul ℂ T)
    have hT : T ∈ W := by
      have := W.smul_mem c⁻¹ hwW
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    exact (Submodule.span_singleton_le_iff_mem T W).mpr hT

end Classification

end PSRatioP

end

open PSRatioP LocalNewvector in

theorem solution
    (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {c : ℕ}
    (h₁ : LocalNewvector.HasCharConductor p μ₁ c)
    (hrat : LocalNewvector.IsUnramified p (μ₁⁻¹ * μ₂))
    (hγ : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) *
        ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹
          = (p : ℂ)) :
    ∃ T : LocalNewvector.PSCarrier p μ₁ μ₂,
      (∀ g : GL (Fin 2) ℚ_[p], LocalNewvector.PSCarrier.toFn p μ₁ μ₂ T g =
        (μ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
          LocalNewvector.halfModulus p (Matrix.GeneralLinearGroup.det g) 1) ∧
      ∀ W : Submodule ℂ (LocalNewvector.PSCarrier p μ₁ μ₂),
        (∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) ↔
          (W = ⊥ ∨ W = Submodule.span ℂ {T} ∨ W = ⊤) := by
  have hμ₂ := coe_apply_eq_mul_norm p hrat hγ
  have hT : Tfn p μ₁ ∈ principalSeries p μ₁ μ₂ := Tfn_mem_principalSeries p h₁ hμ₂
  refine ⟨Tps p hT, fun g => rfl, fun W => ⟨fun hW => ?_, fun hW => ?_⟩⟩
  · by_cases hle : W ≤ Submodule.span ℂ {Tps p hT}
    · rcases eq_bot_or_eq_of_le_span hle with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨x, hxW, hx⟩ := Set.not_subset.mp hle
      exact Or.inr (Or.inr (eq_top_of_stable_of_not_mem_span p h₁ hT W hW hxW hx))
  · rcases hW with rfl | rfl | rfl
    · intro g v hv
      rw [(Submodule.mem_bot ℂ).mp hv, smul_zero]
      exact Submodule.zero_mem _
    · exact span_Tps_stable p hT
    · intro g v _
      exact Submodule.mem_top

end S_LocalNewvector_PSCarrier_exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
end P2MW
export P2MW.S_LocalNewvector_PSCarrier_exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast (solution)
