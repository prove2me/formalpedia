-- Prove2me | solution 1 for ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5e0f6674-9e10-5da0-99bb-413b549507a2

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1

set_option autoImplicit false

open scoped MatrixGroups ModularForm in
theorem solution
    (N : ℕ) [NeZero N] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by
  classical
  obtain ⟨n, b, hb⟩ := ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast N k
  have hrat : ∀ (i : Fin n) (m : ℕ), ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 (⇑(b i) : UpperHalfPlane → ℂ)).coeff m = (r : ℂ) := by
    intro i m
    obtain ⟨r, hr⟩ := hb i m
    exact ⟨r, hr.symm⟩
  choose D r hD hint using fun i => ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion N (b i) (hrat i)
  refine ⟨n, fun i => b.repr F i / (D i : ℂ), fun i => ((D i : ℂ)) • b i, r, fun i => ?_, ?_⟩
  · rw [ModularForm.IsGLPos.coe_smul]; exact hint i
  · have hsum := b.sum_repr F
    have hcoe : (⇑F : UpperHalfPlane → ℂ) = ∑ i, b.repr F i • (⇑(b i) : UpperHalfPlane → ℂ) := by
      conv_lhs => rw [← hsum]
      rw [show (⇑(∑ i, b.repr F i • b i) : UpperHalfPlane → ℂ) = FunLike.coeAddMonoidHom (ModularForm _ k) UpperHalfPlane ℂ (∑ i, b.repr F i • b i) from rfl, map_sum]
      rfl
    rw [hcoe]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ModularForm.IsGLPos.coe_smul, smul_smul, div_mul_cancel₀ _ (Int.cast_ne_zero.mpr (hD i))]

end S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1
end P2MW
export P2MW.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1 (solution)
