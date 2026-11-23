-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.grMk_eq_grMk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:58.285808+00:00
-- url     : https://prove2.me/submissions/d9e5ef8e-75dd-41e5-add5-e91800c1112b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_grMk_eq_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution {n : ℕ} (x y : S.F n) :
    S.grMk n x = S.grMk n y ↔ (x : V) / y ∈ S.F (n + 1) := by
  rw [← div_eq_one, ← map_div, grMk_eq_one_iff]
  rfl
end GroundTheory.LocalField.StableFiltration
