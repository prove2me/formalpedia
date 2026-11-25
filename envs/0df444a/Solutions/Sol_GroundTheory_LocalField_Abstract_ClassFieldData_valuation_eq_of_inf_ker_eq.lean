-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.valuation_eq_of_inf_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:54.90013+00:00
-- url     : https://prove2.me/submissions/456e4b90-4fe5-4d85-9688-6fea6d59263d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_of_mem


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
theorem _root_.solution {S P : OpenSubgroup G}
    (h : (S : Subgroup G) ⊓ D.deg.ker = (P : Subgroup G) ⊓ D.deg.ker) {y : A}
    (hyS : y ∈ fixedModule A (S : Subgroup G)) (hyP : y ∈ fixedModule A (P : Subgroup G)) :
    D.valuation P ⟨y, hyP⟩ = D.valuation S ⟨y, hyS⟩ := by
  set M : OpenSubgroup G := S ⊓ P
  have hMS : M ≤ S := inf_le_left
  have hMP : M ≤ P := inf_le_right
  have heS : relRamificationIndex D.deg S M = 1 :=
    isUnramified_iff.2 fun x hx => ⟨hx.1, (h.le hx).1⟩
  have heP : relRamificationIndex D.deg P M = 1 :=
    isUnramified_iff.2 fun x hx => ⟨(h.ge hx).1, hx.1⟩
  have h1 := D.valuation_of_mem hMS hyS
  have h2 := D.valuation_of_mem hMP hyP
  rw [heS, pow_one] at h1
  rw [heP, pow_one] at h2
  rw [← h1, ← h2]
end GroundTheory.LocalField.Abstract.ClassFieldData
