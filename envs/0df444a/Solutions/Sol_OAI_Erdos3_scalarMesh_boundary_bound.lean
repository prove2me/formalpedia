-- Prove2me | solution 1 for OAI.Erdos3.scalarMesh_boundary_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:07:15.735352+00:00
-- url     : https://prove2.me/submissions/d7d62ca7-b7f3-4737-ad98-7d10bfbd1d38

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009
import Theorems.Thm_OAI_Erdos3_scalarMeshLog_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarMeshCoefficientBudget
namespace OAI

section

namespace Erdos3

theorem scalarMesh_boundary_bound {n A rho c G P T : ℝ}
    (hn : 0 ≤ n) (hA : 0 ≤ A) (hrho : 0 < rho) (hc : 0 < c)
    (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hnP : n ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hrhoG : rho⁻¹ ≤ Real.exp G) (hcP : c⁻¹ ≤ Real.exp P) :
    40 * n * A / (rho * c) ≤ Real.exp (scalarMeshLog G P T) := by
  have h40 : (40 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
  have hproduct : 40 * n * A * rho⁻¹ * c⁻¹ ≤
      Real.exp 40 * Real.exp P * Real.exp P * Real.exp G * Real.exp P := by
    gcongr
  calc
    _ = 40 * n * A * rho⁻¹ * c⁻¹ := by rw [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ _ := hproduct
    _ = Real.exp (G + 3 * P + 40) := by simp only [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (scalarMeshLog_bounds hG hP hT).2.2.2.1

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.scalarMesh_boundary_bound := @OAI.Erdos3.scalarMesh_boundary_bound
