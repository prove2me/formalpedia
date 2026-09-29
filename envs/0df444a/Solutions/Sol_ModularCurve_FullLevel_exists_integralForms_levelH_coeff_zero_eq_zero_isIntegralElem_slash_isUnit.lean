-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/120e7488-35bc-5954-b928-535d680ff147

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub
import Theorems.Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
import Theorems.Thm_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace WFAsm

open ModularCurve ModularForm CongruenceSubgroup

theorem gammaH_le_gamma1 (q M' : ℕ) [Fact q.Prime] [NeZero M'] :
    CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ≤ Gamma1 q := by
  intro A hA
  obtain ⟨hA0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  have hdvd : q ∣ q ^ 2 * M' := Dvd.dvd.mul_right (dvd_pow_self q two_ne_zero) M'
  have hc : ((A 1 0 : ℤ) : ZMod q) = 0 := by
    have h0 : ((A 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 := Gamma0_mem.mp hA0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) h0
  have hd : ((A 1 1 : ℤ) : ZMod q) = 1 := by
    have h1 : ModularCurve.FullLevel.levelH q M' = (ZMod.unitsMap hdvd).ker := rfl
    rw [h1, MonoidHom.mem_ker] at hH
    have h2 := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hH
    simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units, Units.val_one] at h2
    rw [← h2]
    show ((A 1 1 : ℤ) : ZMod q) = ZMod.castHom hdvd (ZMod q) (((A 1 1 : ℤ) : ZMod (q ^ 2 * M')))
    rw [ZMod.castHom_apply, ZMod.cast_intCast hdvd]
  have hdet := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdet
  have ha : ((A 0 0 : ℤ) : ZMod q) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, hd, mul_zero, sub_zero, mul_one] at h
    exact h
  rw [Gamma1_mem]
  exact ⟨ha, hd, hc⟩

noncomputable def e4pow (t : ℕ) : ModularForm 𝒮ℒ (12 * (t : ℤ)) :=
  (ModularForm.E₄.pow (3 * t)).mcast (by push_cast; ring)

theorem coe_e4pow (t : ℕ) : (e4pow t : UpperHalfPlane → ℂ) = (ModularForm.E₄ : UpperHalfPlane → ℂ) ^ (3 * t) := by
  rw [e4pow, coe_mcast, ModularForm.coe_pow]

theorem isIntegralQExp_e4pow (t : ℕ) : IsIntegralQExp (e4pow t) (eisenstein4 ^ (3 * t)) := by
  rw [IsIntegralQExp, e4pow, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularCurve.qExpansion_E4_eq_map_eisenstein4, map_pow]

theorem e4pow_slash (t : ℕ) (γ : SL(2, ℤ)) :
    (e4pow t : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ) = (e4pow t : UpperHalfPlane → ℂ) :=
  SlashInvariantFormClass.slash_action_eq (e4pow t) _ ⟨γ, rfl⟩

theorem eisenstein4_pow_ne_zero (n : ℕ) : (eisenstein4 ^ n : PowerSeries ℤ) ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [map_pow, constantCoeff_eisenstein4, one_pow, map_zero] at this
  exact one_ne_zero this

theorem eisenstein4_pow_mul_inv (n : ℕ) :
    (eisenstein4 ^ n : PowerSeries ℤ) * PowerSeries.invOfUnit (eisenstein4 ^ n) 1 = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [map_pow, constantCoeff_eisenstein4, one_pow, Units.val_one])

end WFAsm

namespace WFAsm

open ModularCurve ModularForm CongruenceSubgroup

theorem a_mul_d_eq_one {q : ℕ} (β : SL(2, ℤ)) (hβ : (((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod q) = 0) :
    (((β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) * (((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe β
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (fun z : ℤ => (z : ZMod q)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hβ, mul_zero, sub_zero] at h
  exact h

theorem prod_siegel_smul (q : ℕ) [Fact q.Prime] (μ : ZMod q → ℕ) (β : SL(2, ℤ))
    (hβ : (((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod q) = 0) (τ : UpperHalfPlane) :
    (∏ r : ZMod q, ∏ s : ZMod q,
        siegelFun q (r.val : ℤ) (s.val : ℤ) ((β • τ : UpperHalfPlane) : ℂ) ^ (12 * q * μ r)) =
      ∏ r : ZMod q, ∏ s : ZMod q,
        siegelFun q (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^
          (12 * q * μ (((((β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q))⁻¹ * r)) := by
  classical
  obtain ⟨h1, -⟩ := ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul q (fun r _ => μ r)
  rw [h1 β τ]
  set a : ZMod q := (((β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) with ha
  set b : ZMod q := (((β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod q) with hb
  set d : ZMod q := (((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q) with hd
  have had : a * d = 1 := a_mul_d_eq_one β hβ
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at had; exact zero_ne_one had
  have hd0 : d ≠ 0 := fun h => by rw [h, mul_zero] at had; exact zero_ne_one had

  let φ : ZMod q × ZMod q → ZMod q × ZMod q := fun rs => (rs.1 * a, rs.1 * b + rs.2 * d)
  have hφ : Function.Bijective φ := by
    refine (Finite.injective_iff_bijective).mp ?_
    rintro ⟨r, s⟩ ⟨r', s'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    have hr : r = r' := mul_right_cancel₀ ha0 h₁
    subst hr
    have hs : s * d = s' * d := by linear_combination h₂
    exact Prod.ext rfl (mul_right_cancel₀ hd0 hs)

  have hidx : ∀ r s : ZMod q,
      ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod q)) = (φ (r, s)).1 ∧
      ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q)) = (φ (r, s)).2 := by
    intro r s
    constructor
    · push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hβ, mul_zero, add_zero]
    · push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  let G : ZMod q × ZMod q → ℂ := fun rs =>
    siegelFun q (rs.1.val : ℤ) (rs.2.val : ℤ) (τ : ℂ) ^ (12 * q * μ (a⁻¹ * rs.1))
  have hexp : ∀ r : ZMod q, μ r = μ (a⁻¹ * (φ (r, 0)).1) := by
    intro r
    show μ r = μ (a⁻¹ * (r * a))
    rw [mul_comm r a, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  calc (∏ r : ZMod q, ∏ s : ZMod q,
          siegelFun q
            (((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod q)).val : ℤ)
            (((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q)).val : ℤ)
            (τ : ℂ) ^ (12 * q * μ r))
      = ∏ rs : ZMod q × ZMod q, G (φ rs) := by
        rw [← Fintype.prod_prod_type']
        refine Fintype.prod_congr _ _ (fun rs => ?_)
        obtain ⟨r, s⟩ := rs
        obtain ⟨e1, e2⟩ := hidx r s
        simp only [G]
        rw [e1, e2]
        congr 2
        · show μ r = μ (a⁻¹ * (r * a))
          rw [mul_comm r a, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    _ = ∏ rs : ZMod q × ZMod q, G rs := (Equiv.ofBijective φ hφ).prod_comp G
    _ = _ := by rw [← Fintype.prod_prod_type']

end WFAsm

open WFAsm ModularCurve ModularForm CongruenceSubgroup in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] :
    ∃ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') : Subgroup (GL (Fin 2) ℝ)) k)
      (pf pg h : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp f pf ∧ ModularCurve.IsIntegralQExp g pg ∧ pg ≠ 0 ∧ pf = pg * h ∧
      PowerSeries.constantCoeff h = 0 ∧
      (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) (ModularCurve.jq)⁻¹).IsIntegralElem
        (ModularCurve.intSeriesC ℚ h) ∧
      ∀ γ : CongruenceSubgroup.Gamma0 (q ^ 2 * M'),
        ∃ (f₁ g₁ : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') : Subgroup (GL (Fin 2) ℝ)) k)
          (pf₁ pg₁ h₁ : PowerSeries ℤ) (c : ℂ),
          c ≠ 0 ∧ ModularCurve.IsIntegralQExp f₁ pf₁ ∧ ModularCurve.IsIntegralQExp g₁ pg₁ ∧
          (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∧
          (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∧
          pg₁ ≠ 0 ∧ pf₁ = pg₁ * h₁ ∧
          (CohCarrier.gamma0Units (q ^ 2 * M') γ ∉
              ModularCurve.FullLevel.levelH q M' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M'))ˣ) →
            IsUnit (PowerSeries.constantCoeff h₁)) := by
  classical

  obtain ⟨μ, t, e, hμ0, he, hF⟩ :=
    ModularCurve.SiegelUnit.exists_exponent_sum_levelBernoulliWeight_mul_eq_indicator_sub q

  have key : ∀ a : ZMod q, a ≠ 0 → ∀ x : ZMod q, x ≠ 0 →
      (∑ r : ZMod q, ((μ (a⁻¹ * r) : ℕ) : ℤ) * (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2)) =
        (if a * x = 1 ∨ a * x = -1 then (e : ℤ) else 0) - (t : ℤ) := by
    intro a ha x hx
    rw [← hF (a * x) (mul_ne_zero ha hx)]
    symm
    refine Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun r => ?_)
    show ((μ r : ℕ) : ℤ) * (6 * (((r * (a * x)).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * (a * x)).val : ℕ) : ℤ) + (q : ℤ) ^ 2) = ((μ (a⁻¹ * (a * r)) : ℕ) : ℤ) * (6 * (((a * r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((a * r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2)
    rw [inv_mul_cancel_left₀ ha, show r * (a * x) = a * r * x by ring]

  have key1 : ∀ a : ZMod q, a ≠ 0 →
      (∑ r : ZMod q, ((μ (a⁻¹ * r) : ℕ) : ℤ) * (6 * ((r.val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * ((r.val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) =
        (if a = 1 ∨ a = -1 then (e : ℤ) else 0) := by
    intro a ha
    have h := key a ha 1 one_ne_zero
    simp only [mul_one] at h
    rw [h]
    ring
  have hbound : ∀ a : ZMod q, a ≠ 0 → ∀ x : ZMod q, x ≠ 0 →
      0 ≤ (∑ r : ZMod q, ((μ (a⁻¹ * r) : ℕ) : ℤ) * (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) := by
    intro a ha x hx
    rw [key a ha x hx]
    split_ifs <;> omega

  have hμ1 : (fun r : ZMod q => μ ((1 : ZMod q)⁻¹ * r)) = μ := by
    funext r; rw [inv_one, one_mul]
  have ht : ∀ x : ZMod q, x ≠ 0 →
      0 ≤ (∑ r : ZMod q, ((μ r : ℕ) : ℤ) * (6 * (((r * x).val : ℕ) : ℤ) ^ 2 - 6 * (q : ℤ) * (((r * x).val : ℕ) : ℤ) + (q : ℤ) ^ 2)) + (t : ℤ) := by
    intro x hx
    have := hbound 1 one_ne_zero x hx
    simpa only [inv_one, one_mul] using this

  obtain ⟨ϑ, hϑ, p, n₀, hp, hn₀, hlow, hlead, hintϑ⟩ :=
    ModularCurve.SiegelUnit.exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
      q μ hμ0 t ht
  have hn₀e : n₀ = e := by
    have h := key1 1 one_ne_zero
    simp only [inv_one, one_mul, true_or, if_true] at h
    have : (n₀ : ℤ) = (e : ℤ) := by rw [hn₀]; exact h
    exact_mod_cast this
  have hp0 : PowerSeries.constantCoeff p = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hlow 0 (by rw [hn₀e]; exact he)

  have hle1 : ((CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) ≤ ((Gamma1 q : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (gammaH_le_gamma1 q M')
  have hleSL : ((CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := Subgroup.map_le_range _ _

  refine ⟨12 * (t : ℤ), restrictForm hle1 ϑ, restrictForm hleSL (e4pow t), p, eisenstein4 ^ (3 * t),
    p * PowerSeries.invOfUnit (eisenstein4 ^ (3 * t)) 1, hp, isIntegralQExp_e4pow t, eisenstein4_pow_ne_zero _, ?_, ?_, ?_, ?_⟩
  · rw [mul_left_comm, eisenstein4_pow_mul_inv, mul_one]
  · rw [map_mul, hp0, zero_mul]
  ·
    have h12 : (12 * (t : ℤ)) = ((12 * t : ℕ) : ℤ) := by push_cast; ring
    obtain ⟨-, hI⟩ :=
      ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
        q (12 * t) (ϑ.mcast h12) p (by rw [IsIntegralQExp, ModularForm.coe_mcast]; exact hp) (fun γ n => by
          rw [ModularForm.coe_mcast, ← h12]
          exact hintϑ γ n)

    have hEinv : intSeriesC ℚ (eisenstein4 ^ (3 * t)) * intSeriesC ℚ (PowerSeries.invOfUnit (eisenstein4 ^ (3 * t)) 1) = 1 := by
      rw [← intSeriesC_mul, eisenstein4_pow_mul_inv, intSeriesC_one]
    have hE0 : intSeriesC ℚ (eisenstein4 ^ (3 * t)) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hEinv; exact zero_ne_one hEinv
    have hpow : ∀ (x : PowerSeries ℤ) (n : ℕ), intSeriesC ℚ (x ^ n) = intSeriesC ℚ x ^ n := by
      intro x n
      induction n with
      | zero => rw [pow_zero, pow_zero, intSeriesC_one]
      | succ m ih => rw [pow_succ, pow_succ, intSeriesC_mul, ih]
    have heq : intSeriesC ℚ (p ^ 12) / intSeriesC ℚ (eisenstein4 ^ (3 * (12 * t))) =
        intSeriesC ℚ (p * PowerSeries.invOfUnit (eisenstein4 ^ (3 * t)) 1) ^ 12 := by
      have hinv : intSeriesC ℚ (PowerSeries.invOfUnit (eisenstein4 ^ (3 * t)) 1) = (intSeriesC ℚ (eisenstein4 ^ (3 * t)))⁻¹ :=
        (eq_inv_of_mul_eq_one_right hEinv)
      rw [intSeriesC_mul, hinv, mul_pow, hpow p 12, show 3 * (12 * t) = 3 * t * 12 by ring, pow_mul, hpow,
        inv_pow, div_eq_mul_inv]
    rw [heq] at hI
    letI : Algebra (Polynomial ℤ) (LaurentSeries ℚ) :=
      (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) (ModularCurve.jq)⁻¹).toAlgebra
    have hI' : IsIntegral (Polynomial ℤ) (intSeriesC ℚ (p * PowerSeries.invOfUnit (eisenstein4 ^ (3 * t)) 1) ^ 12) := hI
    exact hI'.of_pow (by norm_num)
  ·
    intro γ
    have hdvd : q ∣ q ^ 2 * M' := Dvd.dvd.mul_right (dvd_pow_self q two_ne_zero) M'
    have hc0 : ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod q) = 0 := by
      have h0 : ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod (q ^ 2 * M')) = 0 := Gamma0_mem.mp γ.2
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
      exact dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) h0
    set a : ZMod q := ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) with ha
    set d : ZMod q := ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q) with hd
    have had : a * d = 1 := a_mul_d_eq_one (γ : SL(2, ℤ)) hc0
    have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at had; exact zero_ne_one had

    obtain ⟨ϑ₁, hϑ₁, p₁, n₁, hp₁, hn₁, hlow₁, hlead₁, -⟩ :=
      ModularCurve.SiegelUnit.exists_modularForm_gamma1_isIntegralQExp_coeff_eq_one_and_forall_slash_isIntegral
        q (fun r => μ (a⁻¹ * r)) (by simp only [mul_zero]; exact hμ0) t (hbound a ha0)
    refine ⟨restrictForm hle1 ϑ₁, restrictForm hleSL (e4pow t), p₁, eisenstein4 ^ (3 * t),
      p₁ * PowerSeries.invOfUnit (eisenstein4 ^ (3 * t)) 1, 1, one_ne_zero, hp₁, isIntegralQExp_e4pow t, ?_, ?_,
      eisenstein4_pow_ne_zero _, ?_, ?_⟩
    ·
      rw [one_smul, coe_restrictForm, coe_restrictForm]
      funext τ
      rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, hϑ, hϑ₁, prod_siegel_smul q μ (γ : SL(2, ℤ)) hc0 τ]
      have hΔ : ModularForm.discriminant ((γ : SL(2, ℤ)) • τ) * UpperHalfPlane.denom (γ : SL(2, ℤ)) τ ^ (-(12 : ℤ)) =
          ModularForm.discriminant τ := by
        have h := congrFun (SlashInvariantFormClass.slash_action_eq CuspForm.discriminant
          (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ⟨(γ : SL(2, ℤ)), rfl⟩) τ
        rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply] at h
        exact h
      rw [← hΔ, mul_pow, mul_assoc, ← zpow_natCast (UpperHalfPlane.denom (γ : SL(2, ℤ)) τ ^ (-(12 : ℤ))) t, ← zpow_mul,
        show (-(12 : ℤ)) * (t : ℤ) = -(12 * (t : ℤ)) by ring]
    ·
      rw [one_smul, coe_restrictForm, e4pow_slash]
    · rw [mul_left_comm, eisenstein4_pow_mul_inv, mul_one]
    ·
      intro hγ
      rw [map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have hn₁0 : n₁ = 0 := by
        have h := key1 a ha0
        rw [← hn₁] at h
        have hne : ¬ (a = 1 ∨ a = -1) := by
          rintro (h1 | h1)
          · apply hγ
            refine Subgroup.mem_sup_left ?_
            show CohCarrier.gamma0Units (q ^ 2 * M') γ ∈ (ZMod.unitsMap hdvd).ker
            rw [MonoidHom.mem_ker]
            ext
            simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units, Units.val_one]
            show ZMod.castHom hdvd (ZMod q) ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (q ^ 2 * M')) = 1
            rw [ZMod.castHom_apply, ZMod.cast_intCast hdvd]
            rw [h1, one_mul] at had
            exact had
          · apply hγ
            have hsplit : CohCarrier.gamma0Units (q ^ 2 * M') γ =
                (CohCarrier.gamma0Units (q ^ 2 * M') γ * (-1)⁻¹) * (-1) := by rw [inv_mul_cancel_right]
            rw [hsplit]
            refine Subgroup.mul_mem_sup ?_ (Subgroup.mem_zpowers _)
            show CohCarrier.gamma0Units (q ^ 2 * M') γ * (-1)⁻¹ ∈ (ZMod.unitsMap hdvd).ker
            rw [MonoidHom.mem_ker]
            ext
            simp only [map_mul, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units,
              Units.val_mul, Units.val_one, map_neg, map_one, inv_neg, inv_one, Units.val_neg]
            show ZMod.castHom hdvd (ZMod q) ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (q ^ 2 * M')) * -1 = 1
            rw [ZMod.castHom_apply, ZMod.cast_intCast hdvd]
            rw [h1, neg_one_mul] at had
            linear_combination had
        rw [if_neg hne] at h
        exact_mod_cast h
      rw [hn₁0] at hlead₁
      rw [hlead₁, one_mul]
      have h1 : PowerSeries.constantCoeff (eisenstein4 ^ (3 * t) * PowerSeries.invOfUnit (eisenstein4 ^ (3 * t)) (1 : ℤˣ)) = 1 := by
        rw [eisenstein4_pow_mul_inv, map_one]
      rw [map_mul, map_pow, constantCoeff_eisenstein4, one_pow, one_mul] at h1
      rw [h1]
      exact isUnit_one

end S_ModularCurve_FullLevel_exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit (solution)
