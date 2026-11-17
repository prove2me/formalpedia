-- Prove2me | solution 1 for N25.unitDenominatorForm25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:32.905315+00:00
-- url     : https://prove2.me/submissions/d99e72ad-b478-4c9a-b9d1-93b2ae961ec7

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open UpperHalfPlane ModularCurve

open scoped MatrixGroups

namespace N25

private theorem integral_mul {k l : ℤ}
    (f : ModularForm GammaH25GL k) (g : ModularForm GammaH25GL l)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f.mul g) (pf * pg) := by
  have hp : (1 : ℝ) ∈ GammaH25GL.strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH 25 N25.H25)]
    exact AddSubgroup.mem_zmultiples 1
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hp
  have hb := ModularFormClass.analyticAt_cuspFunction_zero g one_pos hp
  unfold IsIntegralQExp at *
  rw [map_mul, hf, hg, ModularForm.coe_mul, qExpansion_mul ha hb]

/-- The cube of the discriminant realizes the integral common denominator. -/
theorem _root_.solution :
    ∃ G : ModularForm GammaH25GL 36,
      (∀ τ : UpperHalfPlane, G τ = ModularForm.discriminant τ ^ 3) ∧
      ModularCurve.IsIntegralQExp G unitDenominatorSeries25 := by
  have hle : GammaH25GL ≤ 𝒮ℒ := by
    rintro A ⟨B, _, rfl⟩
    exact ⟨B, rfl⟩
  let d := CuspForm.toModularFormₗ CuspForm.discriminant
  let δ : ModularForm GammaH25GL 12 :=
    { toFun := d
      slash_action_eq' := fun A hA => d.slash_action_eq' A (hle hA)
      holo' := d.holo'
      bdd_at_cusps' := fun hc => d.bdd_at_cusps' (hc.mono hle) }
  have hδ : IsIntegralQExp δ (PowerSeries.X * ModularCurve.dedekindEtaUnit) :=
    ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm
  refine ⟨(δ.mul δ).mul δ, ?_, ?_⟩
  · intro τ
    change (ModularForm.discriminant τ * ModularForm.discriminant τ) *
      ModularForm.discriminant τ = ModularForm.discriminant τ ^ 3
    ring
  · simpa only [unitDenominatorSeries25, pow_succ, pow_one, pow_zero, one_mul] using
      integral_mul (δ.mul δ) δ (integral_mul δ δ hδ hδ) hδ

end N25
