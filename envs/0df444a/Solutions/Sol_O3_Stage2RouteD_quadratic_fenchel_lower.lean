-- Prove2me | solution 1 for O3.Stage2RouteD.quadratic_fenchel_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:36.886147+00:00
-- url     : https://prove2.me/submissions/d39e425a-5cf8-4ef9-b637-18d658e29bc5

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_le_lpNorm_mul
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right


attribute [local simp] O3.Stage2RouteD.dualityMap_zero

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {p q : ℝ} (hpq : p.HolderConjugate q)
    {d : ℕ} (y w : Point d) :
    pairing w y - quadraticRegularizer q 0 w ≤ quadraticRegularizer p 0 y := by
  have hh := pairing_le_lpNorm_mul hpq.symm w y
  have hs := sq_nonneg (lpNorm q w - lpNorm p y)
  simp only [quadraticRegularizer, sub_zero] at *
  nlinarith
end O3.Stage2RouteD
