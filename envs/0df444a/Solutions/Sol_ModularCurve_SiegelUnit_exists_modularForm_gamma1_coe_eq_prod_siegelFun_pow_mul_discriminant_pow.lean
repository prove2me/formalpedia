-- Prove2me | solution 1 for ModularCurve.SiegelUnit.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/eb0ecb72-2b8c-5bfa-bd28-43b4b314ea5f

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_differentiableOn_siegelFun
import Theorems.Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow
import Theorems.Thm_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow

set_option autoImplicit false

namespace FORM
open ModularCurve UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

variable (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ)

noncomputable def uFun (τ : ℍ) : ℂ :=
  ∏ r : ZMod N, ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)

def Ord (x y : ZMod N) : ℤ :=
  ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
    (6 * ((r * x + s * y).val : ℤ) ^ 2 - 6 * (N : ℤ) * ((r * x + s * y).val : ℤ) + (N : ℤ) ^ 2)

noncomputable def thetaFun (t : ℕ) (τ : ℍ) : ℂ := uFun N m τ * ModularForm.discriminant τ ^ t

theorem discr_slash (β : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (β • τ) * UpperHalfPlane.denom β τ ^ (-(12 : ℤ)) = ModularForm.discriminant τ := by
  have h := congrFun (SlashInvariantForm.slash_action_generators_SL2Z ModularForm.discriminant_S_invariant
    ModularForm.discriminant_T_invariant β) τ
  rwa [ModularForm.SL_slash_apply] at h

theorem thetaFun_slash_apply (t : ℕ) (β : SL(2, ℤ)) (τ : ℍ) :
    ((thetaFun N m t) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) τ = uFun N m (β • τ) * ModularForm.discriminant τ ^ t := by
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, thetaFun, ← discr_slash β τ, mul_pow, mul_assoc]
  congr 2
  rw [← zpow_natCast (UpperHalfPlane.denom β τ ^ (-(12 : ℤ))) t, ← zpow_mul]
  congr 1

def e00 (β : SL(2, ℤ)) : ZMod N := ((β 0 0 : ℤ) : ZMod N)
def e01 (β : SL(2, ℤ)) : ZMod N := ((β 0 1 : ℤ) : ZMod N)
def e10 (β : SL(2, ℤ)) : ZMod N := ((β 1 0 : ℤ) : ZMod N)
def e11 (β : SL(2, ℤ)) : ZMod N := ((β 1 1 : ℤ) : ZMod N)

omit [NeZero N] in
theorem det_rel (β : SL(2, ℤ)) : e00 N β * e11 N β - e01 N β * e10 N β = 1 := by
  have h := β.det_coe
  rw [Matrix.det_fin_two] at h
  have h' := congrArg (fun z : ℤ => (z : ZMod N)) h
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h'
  simpa [e00, e01, e10, e11] using h'

def rowMul (β : SL(2, ℤ)) : ZMod N × ZMod N ≃ ZMod N × ZMod N where
  toFun p := (p.1 * e00 N β + p.2 * e10 N β, p.1 * e01 N β + p.2 * e11 N β)
  invFun p := (p.1 * e11 N β - p.2 * e10 N β, -(p.1 * e01 N β) + p.2 * e00 N β)
  left_inv p := by
    obtain ⟨r, s⟩ := p
    have h := det_rel N β
    ext
    · simp only; linear_combination r * h
    · simp only; linear_combination s * h
  right_inv p := by
    obtain ⟨x, y⟩ := p
    have h := det_rel N β
    ext
    · simp only; linear_combination x * h
    · simp only; linear_combination y * h

def mT (β : SL(2, ℤ)) (r' s' : ZMod N) : ℕ := m ((rowMul N β).symm (r', s')).1 ((rowMul N β).symm (r', s')).2

omit [NeZero N] in
theorem mT_zero (hm0 : m 0 0 = 0) (β : SL(2, ℤ)) : mT N m β 0 0 = 0 := by
  have : (rowMul N β).symm (0, 0) = (0, 0) := by
    rw [Equiv.symm_apply_eq]; ext <;> simp [rowMul]
  simp [mT, this, hm0]

omit [NeZero N] in
theorem mT_rowMul (β : SL(2, ℤ)) (r s : ZMod N) :
    mT N m β (rowMul N β (r, s)).1 (rowMul N β (r, s)).2 = m r s := by
  simp [mT]

theorem idx_cast (r s : ZMod N) (a b : ℤ) :
    ((((r.val : ℤ) * a + (s.val : ℤ) * b : ℤ) : ZMod N).val : ℤ) = (((r * (a : ZMod N) + s * (b : ZMod N)) : ZMod N).val : ℤ) := by
  congr 2
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem uFun_smul (β : SL(2, ℤ)) (τ : ℍ) : uFun N m (β • τ) = uFun N (mT N m β) τ := by
  rw [uFun, (ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul N m).1 β τ, uFun]
  simp_rw [idx_cast]

  rw [← Fintype.prod_prod_type' (f := fun r s => siegelFun N ((r * (↑(β 0 0) : ZMod N) + s * ↑(β 1 0)).val : ℤ)
      ((r * (↑(β 0 1) : ZMod N) + s * ↑(β 1 1)).val : ℤ) (τ : ℂ) ^ (12 * N * m r s)),
    ← Fintype.prod_prod_type' (f := fun r s => siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * mT N m β r s))]
  refine Fintype.prod_equiv (rowMul N β) _ _ fun p => ?_
  obtain ⟨r, s⟩ := p
  rw [mT_rowMul]
  rfl

theorem ord_eq (β : SL(2, ℤ)) :
    Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) =
      ∑ r : ZMod N, ∑ s : ZMod N, (mT N m β r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) := by
  rw [Ord, ← Fintype.sum_prod_type' (f := fun r s => (m r s : ℤ) *
      (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
        - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) + (N : ℤ) ^ 2)),
    ← Fintype.sum_prod_type' (f := fun r s => (mT N m β r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2))]
  refine Fintype.sum_equiv (rowMul N β) _ _ fun p => ?_
  obtain ⟨r, s⟩ := p
  rw [mT_rowMul]
  rfl

theorem discr_isBigO : (fun τ : ℍ => ModularForm.discriminant τ) =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi) * τ.im) := by
  have h := CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  rw [CuspForm.coe_discriminant] at h
  refine h.congr_right fun τ => ?_
  congr 1
  ring

theorem norm_C_eq_one {C : ℂ} (hC : C ^ N = 1) : ‖C‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one hC (NeZero.ne N)

theorem thetaFun_slash_isBigO (hm0 : m 0 0 = 0) (t : ℕ) (β : SL(2, ℤ)) :
    ((thetaFun N m t) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) =O[atImInfty]
      fun τ : ℍ => Real.exp (-(2 * Real.pi *
        (((Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) / (N : ℝ) + (t : ℝ))) * τ.im) := by

  obtain ⟨C, d, hC, -, -, hd0, -, -, htend⟩ :=
    ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow N (mT N m β) (mT_zero N m hm0 β)
  set E : ℤ := ∑ r : ZMod N, ∑ s : ZMod N, (mT N m β r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) with hE
  have hOrd : Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) = E := ord_eq N m β

  have hEC : ((∑ r : ZMod N, ∑ s : ZMod N,
      (mT N m β r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) = ((E : ℤ) : ℂ) := by
    rw [hE]; push_cast; rfl
  rw [hEC] at htend
  set L : ℍ → ℂ := fun τ => C * Complex.exp (2 * Real.pi * Complex.I * ((E : ℤ) : ℂ) * (τ : ℂ) / (N : ℂ)) with hL
  set F : ℍ → ℂ := fun τ => (∏ r : ZMod N, ∏ s : ZMod N,
      siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * mT N m β r s)) / L τ with hF
  have hCne : C ≠ 0 := fun h0 => by
    rw [h0, zero_pow (NeZero.ne N)] at hC; exact zero_ne_one hC
  have hLne : ∀ τ, L τ ≠ 0 := fun τ => mul_ne_zero hCne (Complex.exp_ne_zero _)
  have hsplit : ∀ τ : ℍ, ((thetaFun N m t) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) τ = L τ * F τ * ModularForm.discriminant τ ^ t := by
    intro τ
    rw [thetaFun_slash_apply, uFun_smul, hF]
    simp only
    rw [mul_div_cancel₀ _ (hLne τ)]
    rfl

  have hLnorm : ∀ τ : ℍ, ‖L τ‖ = Real.exp (-(2 * Real.pi * ((E : ℝ) / (N : ℝ))) * τ.im) := by
    intro τ
    rw [hL]
    simp only [norm_mul, norm_C_eq_one N hC, one_mul, Complex.norm_exp]
    congr 1
    have : (2 * (Real.pi : ℂ) * Complex.I * (E : ℂ) * (τ : ℂ) / (N : ℂ)).re = -(2 * Real.pi * ((E : ℝ) / (N : ℝ))) * τ.im := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (E : ℂ) * (τ : ℂ) / (N : ℂ)) =
          ((2 * Real.pi * (E : ℝ) / (N : ℝ) : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) by push_cast; ring]
      rw [Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
      ring
    exact this
  have hLO : L =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi * ((E : ℝ) / (N : ℝ))) * τ.im) :=
    Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => by
      rw [hLnorm, one_mul, Real.norm_of_nonneg (Real.exp_nonneg _)])
  have hFO : F =O[atImInfty] (fun _ : ℍ => (1 : ℝ)) := htend.isBigO_one ℝ
  have hΔO : (fun τ : ℍ => ModularForm.discriminant τ ^ t) =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi) * τ.im) ^ t :=
    discr_isBigO.pow t
  have hprod := (hLO.mul hFO).mul hΔO
  refine (hprod.congr_left fun τ => (hsplit τ).symm).congr_right fun τ => ?_
  rw [mul_one, ← Real.exp_nat_mul, ← Real.exp_add, hOrd]
  congr 1
  ring

theorem mdifferentiable_thetaFun (t : ℕ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaFun N m t) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hΔ : DifferentiableOn ℂ (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 CuspForm.discriminant.holo'
  have hu : DifferentiableOn ℂ (fun z : ℂ => ∏ r : ZMod N, ∏ s : ZMod N,
      siegelFun N (r.val : ℤ) (s.val : ℤ) z ^ (12 * N * m r s)) {z : ℂ | 0 < z.im} := by
    have h1 : ∀ r : ZMod N, DifferentiableOn ℂ (fun z : ℂ => ∏ s : ZMod N,
        siegelFun N (r.val : ℤ) (s.val : ℤ) z ^ (12 * N * m r s)) {z : ℂ | 0 < z.im} := fun r => by
      have h := DifferentiableOn.finsetProd (u := Finset.univ)
        (f := fun (s : ZMod N) (z : ℂ) => siegelFun N (r.val : ℤ) (s.val : ℤ) z ^ (12 * N * m r s))
        (fun s _ => ((ModularCurve.SiegelUnit.differentiableOn_siegelFun N (r.val : ℤ) (s.val : ℤ)).1).pow _)
      rwa [Finset.prod_fn] at h
    have h2 := DifferentiableOn.finsetProd (u := Finset.univ)
      (f := fun (r : ZMod N) (z : ℂ) => ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) z ^ (12 * N * m r s)) (fun r _ => h1 r)
    rwa [Finset.prod_fn] at h2
  refine ((hu.mul (hΔ.pow t)).congr fun z hz => ?_)
  simp only [Function.comp_apply, thetaFun, uFun, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Pi.mul_apply, Pi.pow_apply]

noncomputable def theta (hm0 : m 0 0 = 0) (hm : ∀ r s : ZMod N, m r (s + r) = m r s) (t : ℕ)
    (ht : ∀ β : SL(2, ℤ), 0 ≤ Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) + (N : ℤ) * t) :
    ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)) where
  toFun := thetaFun N m t
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    funext τ
    change ((thetaFun N m t) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ)) τ = thetaFun N m t τ
    rw [thetaFun_slash_apply, thetaFun, uFun, uFun,
      (ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul N m).2 hm γ hγ τ]
  holo' := mdifferentiable_thetaFun N m t
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _

    have hO := thetaFun_slash_isBigO N m hm0 t γ
    rw [ModularForm.SL_slash]
    change Filter.BoundedAtFilter atImInfty ((thetaFun N m t) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ))
    refine hO.trans (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_))
    have hpos : 0 ≤ (((Ord N m ((γ 0 0 : ℤ) : ZMod N) ((γ 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) / (N : ℝ) + (t : ℝ)) := by
      have h1 := ht γ
      have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 (NeZero.pos N)
      have h2 : (0 : ℝ) ≤ ((Ord N m ((γ 0 0 : ℤ) : ZMod N) ((γ 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) + (N : ℝ) * (t : ℝ) := by
        exact_mod_cast h1
      have : (((Ord N m ((γ 0 0 : ℤ) : ZMod N) ((γ 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) / (N : ℝ) + (t : ℝ)) =
          ((((Ord N m ((γ 0 0 : ℤ) : ZMod N) ((γ 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) + (N : ℝ) * (t : ℝ))) / (N : ℝ) := by
        field_simp
      rw [this]
      exact div_nonneg h2 hNpos.le
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Pi.one_apply, norm_one, mul_one, Real.exp_le_one_iff, neg_mul]
    exact neg_nonpos.2 (mul_nonneg (mul_nonneg (by positivity) hpos) τ.im_pos.le)

theorem theta_apply (hm0 : m 0 0 = 0) (hm : ∀ r s : ZMod N, m r (s + r) = m r s) (t : ℕ)
    (ht : ∀ β : SL(2, ℤ), 0 ≤ Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) + (N : ℤ) * t) (τ : ℍ) :
    theta N m hm0 hm t ht τ = uFun N m τ * ModularForm.discriminant τ ^ t := rfl

end FORM

open scoped MatrixGroups ModularForm in
theorem solution
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (hm0 : m 0 0 = 0)
    (hm : ∀ r s : ZMod N, m r (s + r) = m r s) (t : ℕ)
    (ht : ∀ β : SL(2, ℤ),
      0 ≤ (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
          (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
            - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) + (N : ℤ) ^ 2)) + (N : ℤ) * t) :
    ∃ ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)),
      (∀ τ : UpperHalfPlane, ϑ τ =
        (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
          ModularForm.discriminant τ ^ t) ∧
      ∀ β : SL(2, ℤ),
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane =>
            Real.exp (-(2 * Real.pi *
              ((((∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
                (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
                  - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) + (N : ℤ) ^ 2)) : ℤ) : ℝ) / (N : ℝ) + (t : ℝ))) * τ.im) := by
  refine ⟨FORM.theta N m hm0 hm t ht, fun τ => rfl, fun β => ?_⟩
  exact FORM.thetaFun_slash_isBigO N m hm0 t β

end S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow (solution)
