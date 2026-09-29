-- Prove2me | solution 1 for ModPForms.mul_mem_modPMod_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/64796ce0-2add-5401-9fac-ad029859e6e0

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_mul_mem_modPMod_add

set_option autoImplicit false

open scoped MatrixGroups

namespace FltWs24
namespace ModPMul

theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]

theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_mul_of_intCast {N : ℕ} {a b : ℤ} {F : Type} [Field F]
    {G₁ G₂ : Type*} [FunLike G₁ UpperHalfPlane ℂ] [FunLike G₂ UpperHalfPlane ℂ]
    (f : G₁) [ModularFormClass G₁ (CongruenceSubgroup.Gamma0 N) a]
    (g : G₂) [ModularFormClass G₂ (CongruenceSubgroup.Gamma0 N) b]
    (c d : ℕ → ℤ) (hc : ∀ n, ModularFormClass.qCoeff f n = (c n : ℂ))
    (hd : ∀ n, ModularFormClass.qCoeff g n = (d n : ℂ)) :
    (∀ n, ModularFormClass.qCoeff (⇑f * ⇑g) n = ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2 : ℤ) : ℂ)) ∧
      (PowerSeries.mk fun n => ((c n : ℤ) : F)) * (PowerSeries.mk fun n => ((d n : ℤ) : F)) =
        PowerSeries.mk fun n => (((∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * d p.2 : ℤ) : ℤ) : F) := by
  refine ⟨fun n => ?_, ?_⟩
  · unfold ModularFormClass.qCoeff at hc hd ⊢
    rw [ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods_Gamma0 N) f g, PowerSeries.coeff_mul]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by rw [hc, hd]
  · ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Int.cast_sum, Int.cast_mul]

end FltWs24.ModPMul

open FltWs24.ModPMul in
theorem solution (N : ℕ) (a b : ℤ) (F : Type) [Field F]
    (φ ψ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N a F) (hψ : ψ ∈ ModPForms.modPMod N b F) :
    φ * ψ ∈ ModPForms.modPMod N (a + b) F := by
  unfold ModPForms.modPMod at hφ hψ ⊢
  refine Submodule.mul_le.mp ?_ φ hφ ψ hψ
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨x, ⟨f, c, hc, rfl⟩, y, ⟨g, d, hd, rfl⟩, rfl⟩
  obtain ⟨he, hprod⟩ := qCoeff_mul_of_intCast (F := F) f g c d hc hd
  refine Submodule.subset_span ⟨f.mul g, _, fun n => ?_, hprod⟩
  rw [ModularForm.coe_mul]
  exact he n

end S_ModPForms_mul_mem_modPMod_add
end P2MW
export P2MW.S_ModPForms_mul_mem_modPMod_add (solution)
