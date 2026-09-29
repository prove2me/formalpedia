-- Prove2me | solution 1 for ModularCurve.exists_gamma1_peaked_auxiliary_form
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/032f90c1-44c5-5129-b5e8-d47a1818aa78

import Theorems.Thm_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd
import Theorems.Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_gamma1_peaked_auxiliary_form
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real MatrixGroups ModularForm Topology Pointwise

namespace PeakedAuxiliaryU

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Group

variable {N : ℕ}

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁(N)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 N)]
  exact AddSubgroup.mem_zmultiples 1

theorem T_pow_mem_Gamma (N : ℕ) : ModularGroup.T ^ N ∈ CongruenceSubgroup.Gamma N := by
  rw [Gamma_mem, ← zpow_natCast]
  simp only [ModularGroup.coe_T_zpow]
  simp

theorem Gamma_le_Gamma1 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  (Gamma_normal N).conj_mem g hg α

theorem coeGL_mul (β γ : SL(2, ℤ)) :
    ((β * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) β γ

theorem coeGL_inv (β : SL(2, ℤ)) :
    ((β⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ)⁻¹ :=
  map_inv (Matrix.SpecialLinearGroup.mapGL ℝ) β

def GammaS (N : ℕ) : Subgroup SL(2, ℤ) :=
  (ConjAct.toConjAct ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N)).comap
    (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem mem_conj_iff (g x : GL (Fin 2) ℝ) (Γ : Subgroup (GL (Fin 2) ℝ)) :
    x ∈ ConjAct.toConjAct g⁻¹ • Γ ↔ g * x * g⁻¹ ∈ Γ := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]

theorem mem_GammaS_iff {γ : SL(2, ℤ)} :
    γ ∈ GammaS N ↔ ((ModularGroup.S * γ * ModularGroup.S⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ Γ₁(N) := by
  rw [GammaS, Subgroup.mem_comap, mem_conj_iff, coeGL_mul, coeGL_mul, coeGL_inv]
  rfl

theorem mem_GammaS_of {γ : SL(2, ℤ)} (h : ModularGroup.S * γ * ModularGroup.S⁻¹ ∈ Gamma1 N) :
    γ ∈ GammaS N :=
  mem_GammaS_iff.mpr ⟨_, h, rfl⟩

theorem Gamma_le_GammaS (N : ℕ) : CongruenceSubgroup.Gamma N ≤ GammaS N := fun _ hγ =>
  mem_GammaS_of (Gamma_le_Gamma1 N (conj_mem_Gamma ModularGroup.S hγ))

scoped instance instFiniteIndexGammaS (N : ℕ) [NeZero N] : (GammaS N).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaS N)

theorem T_pow_mem_GammaS (N : ℕ) : ModularGroup.T ^ N ∈ GammaS N :=
  Gamma_le_GammaS N (T_pow_mem_Gamma N)

theorem natCast_mem_strictPeriods_GammaS (N : ℕ) :
    (N : ℝ) ∈ ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T ^ N, T_pow_mem_GammaS N, ?_⟩
  apply Units.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    ← zpow_natCast, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

theorem GammaS_le_conjS (N : ℕ) :
    ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N) :=
  Subgroup.map_comap_le _ _

end Group

section Forms

variable {N : ℕ} [NeZero N] {w : ℤ}

def restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

def Thetaform (ϑ : ModularForm Γ₁(N) w) :
    ModularForm ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w :=
  restrictMF (GammaS_le_conjS N)
    (ModularForm.translate ϑ ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))

omit [NeZero N] in
theorem coe_Thetaform (ϑ : ModularForm Γ₁(N) w) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) = (⇑ϑ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) :=
  rfl

theorem analyticAt_cuspFunction_slash_S (ϑ : ModularForm Γ₁(N) w) :
    AnalyticAt ℂ (cuspFunction (N : ℝ)
      ((⇑ϑ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))) 0 := by
  rw [← coe_Thetaform]
  exact ModularFormClass.analyticAt_cuspFunction_zero (Thetaform ϑ)
    (Nat.cast_pos.mpr (NeZero.pos N)) (natCast_mem_strictPeriods_GammaS N)

end Forms

theorem coeff_mul_of_coeff_lt_eq_zero {φ ψ : PowerSeries ℂ} {m₀ : ℕ}
    (h : ∀ n : ℕ, n < m₀ → φ.coeff n = 0) :
    (φ * ψ).coeff m₀ = φ.coeff m₀ * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (m₀, 0)]
  · intro p hp hne
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hlt : p.1 < m₀ := by
      rcases lt_or_ge p.1 m₀ with h' | h'
      · exact h'
      · exfalso
        apply hne
        have h1 : p.1 = m₀ := by omega
        have h2 : p.2 = 0 := by omega
        exact Prod.ext h1 h2
    rw [h p.1 hlt, zero_mul]
  · intro hn
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hn

theorem coeff_mul_eq_zero_of_lt {φ ψ : PowerSeries ℂ} {m₀ n : ℕ}
    (h : ∀ n : ℕ, n < m₀ → φ.coeff n = 0) (hn : n < m₀) :
    (φ * ψ).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [h p.1 (by omega), zero_mul]

theorem isIntegral_pow_mul_coeff_mul {φ ψ : PowerSeries ℂ} {N a b : ℕ}
    (hφ : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * φ.coeff n))
    (hψ : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ b * ψ.coeff n)) (n : ℕ) :
    IsIntegral ℤ ((N : ℂ) ^ (a + b) * (φ * ψ).coeff n) := by
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  refine IsIntegral.sum _ fun p _ => ?_
  have e : (N : ℂ) ^ (a + b) * (φ.coeff p.1 * ψ.coeff p.2) =
      ((N : ℂ) ^ a * φ.coeff p.1) * ((N : ℂ) ^ b * ψ.coeff p.2) := by
    rw [pow_add]; ring
  rw [e]
  exact (hφ p.1).mul (hψ p.2)

theorem coe_mul_slash {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ}
    (f : ModularForm Γ k₁) (g : ModularForm Γ k₂) (β : SL(2, ℤ)) :
    ((⇑(f.mul g) : ℍ → ℂ) ∣[k₁ + k₂] (β : GL (Fin 2) ℝ)) =
      ((⇑f : ℍ → ℂ) ∣[k₁] (β : GL (Fin 2) ℝ)) * ((⇑g : ℍ → ℂ) ∣[k₂] (β : GL (Fin 2) ℝ)) := by
  rw [ModularForm.coe_mul]
  exact ModularForm.mul_slash_SL2 k₁ k₂ β _ _

end PeakedAuxiliaryU
p2m_reactivate "P2MW.S_ModularCurve_exists_gamma1_peaked_auxiliary_form.PeakedAuxiliaryU"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_gamma1_peaked_auxiliary_form.PeakedAuxiliaryU"

open PeakedAuxiliaryU in
open scoped MatrixGroups ModularForm in
theorem solution (N : ℕ) (hN : 2 ≤ N) (k : ℤ)
    (hk : Odd k → 3 ≤ N) :
    ∃ (w : ℤ) (m₀ a : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) w),
      Even (k + w) ∧ w < 12 * (m₀ : ℤ) ∧ 0 < δ ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)) ∧
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n)) ∧
      ∀ β : SL(2, ℤ),
        (β ∉ CongruenceSubgroup.Gamma1 N ∧ -β ∉ CongruenceSubgroup.Gamma1 N) →
        (∀ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉ CongruenceSubgroup.Gamma1 N ∧
          -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∉ CongruenceSubgroup.Gamma1 N) →
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨w, m₀, a, δ, ϑ, h12, hw, hδ, h1, h2a, h2b, h2c, h2d, h3⟩ :=
    ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd N hN
  obtain ⟨c, hc⟩ := h12
  rcases Int.even_or_odd k with hke | hko
  · obtain ⟨r, hr⟩ := hke
    exact ⟨w, m₀, a, δ, ϑ, ⟨r + 6 * c, by omega⟩, hw, hδ, h1, h2a, h2b, h2c, h2d, h3⟩
  · have hN3 : 3 ≤ N := hk hko
    obtain ⟨E, b, hE1, hE0, hEinv, hES⟩ :=
      ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion N hN3
    obtain ⟨j, hj⟩ := hko
    have hq1 : UpperHalfPlane.qExpansion 1 (⇑(ϑ.mul E) : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ) *
          UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ) :=
      ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods N) ϑ E
    have hqN : UpperHalfPlane.qExpansion (N : ℝ)
          ((⇑(ϑ.mul E) : UpperHalfPlane → ℂ) ∣[w + 3] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        UpperHalfPlane.qExpansion (N : ℝ)
            ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) *
          UpperHalfPlane.qExpansion (N : ℝ)
            ((⇑E : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
      rw [coe_mul_slash ϑ E ModularGroup.S]
      exact UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_slash_S ϑ)
        (analyticAt_cuspFunction_slash_S E)
    refine ⟨w + 3, m₀, a + b, δ, ϑ.mul E, ⟨j + 6 * c + 2, by omega⟩, by omega, hδ,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      rw [hqN]
      exact isIntegral_pow_mul_coeff_mul h1 hES n
    · intro n hn
      rw [hq1]
      exact coeff_mul_eq_zero_of_lt h2a hn
    · rw [hq1, coeff_mul_of_coeff_lt_eq_zero h2a]
      exact mul_ne_zero h2b hE0
    · rw [hq1, coeff_mul_of_coeff_lt_eq_zero h2a, mul_inv, pow_add]
      have e : (N : ℂ) ^ a * (N : ℂ) ^ b *
          (((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹ *
            ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) =
          ((N : ℂ) ^ a * ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) *
            ((N : ℂ) ^ b * ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) := by
        ring
      rw [e]
      exact h2c.mul hEinv
    · intro n
      rw [hq1]
      exact isIntegral_pow_mul_coeff_mul h2d hE1 n
    · intro β hβ hβ0
      rw [coe_mul_slash ϑ E β]
      have hE : UpperHalfPlane.IsBoundedAtImInfty
          ((⇑E : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] (β : GL (Fin 2) ℝ)) :=
        ModularFormClass.bdd_at_infty_slash E β
      exact ((h3 β hβ hβ0).mul hE).congr (fun _ => rfl) (fun _ => mul_one _)

end S_ModularCurve_exists_gamma1_peaked_auxiliary_form
end P2MW
export P2MW.S_ModularCurve_exists_gamma1_peaked_auxiliary_form (solution)
