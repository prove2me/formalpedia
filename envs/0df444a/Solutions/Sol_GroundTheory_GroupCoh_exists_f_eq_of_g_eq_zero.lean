-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_f_eq_of_g_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:15.636831+00:00
-- url     : https://prove2.me/submissions/d72194a0-61b9-404c-8051-7be2593f6300

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
include hX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.GroupCoh
theorem _root_.solution (e : X.X₂) (he : X.g.hom e = 0) : ∃ a : X.X₁, X.f.hom a = e := by
  have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hmem : e ∈ LinearMap.range X.f.hom.toLinearMap := this ▸ LinearMap.mem_ker.2 he
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩
end GroundTheory.GroupCoh
