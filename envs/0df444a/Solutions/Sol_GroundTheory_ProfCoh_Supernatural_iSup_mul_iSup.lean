-- Prove2me | solution 1 for GroundTheory.ProfCoh.Supernatural.iSup_mul_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:13.617336+00:00
-- url     : https://prove2.me/submissions/9261dba9-5ecb-4a85-92b2-07d4327c887e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_le_def
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_exp_ofNat
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.Supernatural.exp_ofNat
attribute [local simp] GroundTheory.ProfCoh.Supernatural.ofNat_one

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Supernatural
namespace GroundTheory.ProfCoh.Supernatural
theorem _root_.solution {ι : Sort*} {f g : ι → Supernatural}
    (h : ∀ i j, ∃ k, f i ≤ f k ∧ g j ≤ g k) :
    (⨆ i, f i) * (⨆ i, g i) = ⨆ i, f i * g i := by
  ext p
  simp only [exp_mul, exp_iSup]
  exact ENat.iSup_add_iSup fun i j => (h i j).imp fun k hk =>
    add_le_add (le_def.mp hk.1 p) (le_def.mp hk.2 p)
end GroundTheory.ProfCoh.Supernatural
