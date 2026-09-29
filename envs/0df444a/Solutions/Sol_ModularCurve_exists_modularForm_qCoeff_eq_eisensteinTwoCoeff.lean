-- Prove2me | solution 1 for ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7f516d39-c62f-5185-8d28-a582639c92ee

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_eisensteinTwoSlash_slash_eq_self
import Theorems.Thm_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash
import Theorems.Thm_ModularCurve_hasSum_eisensteinTwoCoeff_mul_cexp_pow
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff

set_option autoImplicit false

p2m_open "UpperHalfPlane OnePoint ModularCurve P2MW.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff.ModularCurve EisensteinSeries"
open scoped ModularForm MatrixGroups Manifold

namespace S09RDA

variable (p : ℕ) [NeZero p]

noncomputable abbrev eisFun : ℍ → ℂ := E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - E2

noncomputable def eisForm : ModularForm (CongruenceSubgroup.Gamma0 p) 2 where
  toFun := eisFun p
  slash_action_eq' := eisensteinTwoSlash_slash_eq_self p
  holo' := (E2_mdifferentiable.slash 2 (ModularForm.heckeDiagMatrix p)).sub E2_mdifferentiable
  bdd_at_cusps' := by
    intro c hc
    have hc' : IsCusp c 𝒮ℒ := hc.mono (Subgroup.map_le_range _ _)
    rw [isBoundedAt_iff_forall_SL2Z hc']
    intro γ _
    exact isBoundedAtImInfty_eisensteinTwoSlash_slash p γ

theorem eisForm_apply (τ : ℍ) : eisForm p τ = (p : ℂ) * E2 (ModularForm.heckeDiagMatrix p • τ) - E2 τ := by
  show eisFun p τ = _
  simp only [eisFun, Pi.sub_apply, ModularForm.slash_heckeDiagMatrix_apply 2 (NeZero.ne p)]
  norm_num

omit [NeZero p] in
theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine Subgroup.mem_map.mpr ⟨ModularGroup.T, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom, Matrix.SpecialLinearGroup.mapGL]

theorem qCoeff_eisForm (n : ℕ) : ModularFormClass.qCoeff (eisForm p) n = (eisensteinTwoCoeff p n : ℂ) := by
  unfold ModularFormClass.qCoeff
  symm
  refine ModularFormClass.qExpansion_coeff_unique (h := 1) (c := fun m => (eisensteinTwoCoeff p m : ℂ)) one_pos
    (one_mem_strictPeriods p) (f := eisForm p) ?_ n
  intro τ
  have h := hasSum_eisensteinTwoCoeff_mul_cexp_pow p τ
  rw [← eisForm_apply p τ] at h
  have hq : Function.Periodic.qParam (1 : ℝ) (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * τ) := by
    simp [Function.Periodic.qParam]
  simpa [hq, smul_eq_mul] using h

end S09RDA

namespace ModularCurve p2m_export "ModularCurve" "eisensteinTwoCoeff eisensteinTwoSlash_slash_eq_self isBoundedAtImInfty_eisensteinTwoSlash_slash hasSum_eisensteinTwoCoeff_mul_cexp_pow" end ModularCurve
p2m_open_scoped "ModularCurve" in
open S09RDA in
private theorem ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff (p : ℕ) [Fact p.Prime] :
    ∃ E : ModularForm (CongruenceSubgroup.Gamma0 p) 2, ∀ n : ℕ, ModularFormClass.qCoeff E n = (eisensteinTwoCoeff p n : ℂ) :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ⟨eisForm p, qCoeff_eisForm p⟩

theorem solution (p : ℕ) [Fact p.Prime] : ∃ E : ModularForm (CongruenceSubgroup.Gamma0 p) 2, ∀ n : ℕ, ModularFormClass.qCoeff E n = (eisensteinTwoCoeff p n : ℂ) :=
  ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff p

end S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff (solution)
