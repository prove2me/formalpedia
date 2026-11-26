-- Prove2me | solution 1 for O3.Stage2Closure.exists_hasDerivAt_smoothRemainderDeriv_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:19.845276+00:00
-- url     : https://prove2.me/submissions/639befcd-955a-4e45-8fec-1f81a0f965c7

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_O3_Stage2BelowGeometry
import Theorems.Thm_O3_Stage2RouteA_exists_hasDerivAt_line_duality_pair_le_above_two
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open O3
open O3.Stage2Closure
open scoped BigOperators
open Stage2RouteA Stage2RouteB
namespace O3.Stage2Closure
theorem _root_.solution {q : ℝ} (hq : 2 < q)
    {d : ℕ} (u h : Point d) (t : ℝ) :
    ∃ w : ℝ, HasDerivAt (smoothRemainderDeriv q u h) w t ∧ w ≤ 0 := by
  obtain ⟨a, ha, hale⟩ :=
    Stage2RouteA.exists_hasDerivAt_line_duality_pair_le_above_two hq u h t
  have hlinear : HasDerivAt
      (fun s : ℝ ↦ (q - 1) * s * (lpNorm q h) ^ (2 : ℕ))
      ((q - 1) * (lpNorm q h) ^ (2 : ℕ)) t := by
    simpa [id_eq] using ((hasDerivAt_id t).const_mul (q - 1)).mul_const
      ((lpNorm q h) ^ (2 : ℕ))
  refine ⟨a - (q - 1) * (lpNorm q h) ^ (2 : ℕ), ?_, by linarith⟩
  exact ha.sub hlinear
end O3.Stage2Closure
