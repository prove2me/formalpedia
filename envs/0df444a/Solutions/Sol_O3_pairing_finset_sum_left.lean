-- Prove2me | solution 1 for O3.pairing_finset_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:37.419329+00:00
-- url     : https://prove2.me/submissions/953955af-6752-4fc7-81a9-1ca797a9f7bc

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_pairing_add_left
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
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ} {α : Type*}
    (s : Finset α) (f : α → Vec d) (x : Vec d) :
    pairing (∑ i ∈ s, f i) x = ∑ i ∈ s, pairing (f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [pairing]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [Stage2RouteD.pairing_add_left, ih]
end O3
