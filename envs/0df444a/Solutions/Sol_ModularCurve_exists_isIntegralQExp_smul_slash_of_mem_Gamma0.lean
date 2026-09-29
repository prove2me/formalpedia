-- Prove2me | solution 1 for ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/fac53f21-6af3-5d32-b373-7a3d3084334f

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve
open scoped MatrixGroups ModularForm Manifold

namespace X1DiamondIntegral

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem conj_mem_Gamma1 {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ Gamma1 M) :
    γ * A * γ⁻¹ ∈ Gamma1 M := by
  have hA0 : A ∈ Gamma0 M := Gamma1_in_Gamma0 M hA
  set A₀ : Gamma0 M := ⟨A, hA0⟩
  set γ₀ : Gamma0 M := ⟨γ, hγ⟩
  have hA1 : A₀ ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M A).mp hA
  haveI : (Gamma1' M).Normal := by
    change ((Gamma0Map M).ker).Normal
    infer_instance
  have hconj : γ₀ * A₀ * γ₀⁻¹ ∈ Gamma1' M := Subgroup.Normal.conj_mem inferInstance A₀ hA1 γ₀
  rw [Gamma1_to_Gamma0_mem] at hconj
  rw [Gamma1_mem]
  exact hconj

def diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁(M) k) :
    ModularForm Γ₁(M) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ Gamma1 M := conj_mem_Gamma1 hγ hA
    have hGL : (γ : GL (Fin 2) ℝ) * (A : GL (Fin 2) ℝ)
        = ((γ * A * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) := by
      simp only [map_mul, map_inv, inv_mul_cancel_right]
    change ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (A : GL (Fin 2) ℝ)
      = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hconj)
  holo' := f.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ₁(M)).mp hc
    have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) Γ₁(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hcSL.smul_of_mem ⟨γ, rfl⟩
    exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

theorem coe_diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁(M) k) :
    (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [ModularForm.SL_slash]; rfl

theorem rat_of_isIntegralQExp {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 f).coeff n = (r : ℂ) :=
  ⟨(PowerSeries.coeff n p : ℤ), by rw [← h.coeff n]; push_cast; rfl⟩

end X1DiamondIntegral

open X1DiamondIntegral in
theorem solution (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (D : ℤ) (f₁ : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
      (p₁ : PowerSeries ℤ), D ≠ 0 ∧ ModularCurve.IsIntegralQExp f₁ p₁ ∧
        (⇑f₁ : UpperHalfPlane → ℂ) = (D : ℂ) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by

  have hrat := ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 M f
    (rat_of_isIntegralQExp hp) γ hγ

  set g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k := diamondSlash γ hγ f
    with hg
  have hcoe : (⇑g : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := coe_diamondSlash γ hγ f
  have hrat' : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ) := by
    rw [hcoe]; exact hrat

  obtain ⟨D, p₁, hD, hint⟩ := ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion M g hrat'
  refine ⟨D, (D : ℂ) • g, p₁, hD, ?_, ?_⟩
  · rw [IsGLPos.coe_smul]; exact hint
  · rw [IsGLPos.coe_smul, hcoe]

end
end S_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
end P2MW
export P2MW.S_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (solution)
