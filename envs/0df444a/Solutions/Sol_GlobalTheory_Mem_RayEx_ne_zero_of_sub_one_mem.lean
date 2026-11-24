-- Prove2me | solution 1 for GlobalTheory.Mem.RayEx.ne_zero_of_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:56.334823+00:00
-- url     : https://prove2.me/submissions/f794d279-0e48-4944-90eb-8297a5609f1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
variable {m}
namespace GlobalTheory.Mem.RayEx
theorem _root_.solution (hm : m ≠ ⊤) {a : R} (ha : a - 1 ∈ m) : a ≠ 0 := by
  rintro rfl
  apply hm
  rw [Ideal.eq_top_iff_one]
  simpa using m.neg_mem ha
end GlobalTheory.Mem.RayEx
