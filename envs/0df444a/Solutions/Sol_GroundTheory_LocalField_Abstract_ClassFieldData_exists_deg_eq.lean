-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.exists_deg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:23.727521+00:00
-- url     : https://prove2.me/submissions/daa9aab8-88e7-446d-93a5-5cfff1613ff5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (K : OpenSubgroup G) :
    ∃ φ ∈ (K : Subgroup G), D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K (Multiplicative.ofAdd 1)
  refine ⟨φ, φ.2, ?_⟩
  rw [← D.relDeg_pow, hφ, ← ofAdd_nsmul, nsmul_one]
end GroundTheory.LocalField.Abstract.ClassFieldData
