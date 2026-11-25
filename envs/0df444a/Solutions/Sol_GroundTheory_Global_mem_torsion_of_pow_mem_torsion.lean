-- Prove2me | solution 1 for GroundTheory.Global.mem_torsion_of_pow_mem_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:58.661393+00:00
-- url     : https://prove2.me/submissions/23d6eb63-109c-4586-82f6-852df066f707

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Module
noncomputable section
variable {G : Type*} [CommGroup G]
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) {x : G}
    (hx : x ^ n ∈ CommGroup.torsion G) : x ∈ CommGroup.torsion G := by
  rw [CommGroup.mem_torsion] at hx ⊢
  exact (isOfFinOrder_pow.1 hx).resolve_right hn
end GroundTheory.Global
