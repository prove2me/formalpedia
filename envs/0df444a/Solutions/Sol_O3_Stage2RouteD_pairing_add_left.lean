-- Prove2me | solution 1 for O3.Stage2RouteD.pairing_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:11:58.791562+00:00
-- url     : https://prove2.me/submissions/cd9d46ca-66ba-4479-bbd5-4346e990f1e4

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {d : ℕ} (x y z : Point d) :
    pairing (x + y) z = pairing x z + pairing y z := by
  simp [pairing, Finset.sum_add_distrib, add_mul]
end O3.Stage2RouteD
