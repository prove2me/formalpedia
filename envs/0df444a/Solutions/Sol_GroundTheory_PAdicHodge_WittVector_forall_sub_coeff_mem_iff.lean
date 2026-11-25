-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.forall_sub_coeff_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:17.555008+00:00
-- url     : https://prove2.me/submissions/617149cb-a8b7-443e-877b-a04db5e981d9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_forall_lt_sub_coeff_mem_iff

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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (J : Ideal R) (x y : WittVector p R) :
    (∀ i, x.coeff i - y.coeff i ∈ J) ↔ ∀ i, (x - y).coeff i ∈ J := by
  constructor
  · intro h i
    exact (WittVector.forall_lt_sub_coeff_mem_iff J (i + 1) x y).1 (fun j _ => h j) i i.lt_succ_self
  · intro h i
    exact (WittVector.forall_lt_sub_coeff_mem_iff J (i + 1) x y).2 (fun j _ => h j) i i.lt_succ_self
end WittVector
end GroundTheory.PAdicHodge
