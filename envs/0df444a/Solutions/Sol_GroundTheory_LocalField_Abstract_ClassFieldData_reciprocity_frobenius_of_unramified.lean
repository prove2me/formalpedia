-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_frobenius_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:52:46.693395+00:00
-- url     : https://prove2.me/submissions/17bb6a1f-a592-4e7c-8922-4eff81613c34

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_relInertiaDegree_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_mk_eq_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_of_mem
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_of_mem
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_relIndex_eq_mul


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
  {D : ClassFieldData G A}
variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    {π : fixedModule A (K : Subgroup G)} (hπ : D.valuation K π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK hax (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (π : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  have hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
    rw [← D.relDeg_pow, hφ, ← ofAdd_nsmul, nsmul_one]
  set s : D.FrobeniusLift K := FrobeniusLift.ofDegOne φ.2 hdφ with hs
  have hSK := s.field_le hLK

  have he : relRamificationIndex D.deg K (s.field L hLK) = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro x hx
    exact le_frobeniusClosure ⟨hu ⟨hx.2, hx.1⟩, hx.1⟩
  have hrel : ((s.field L hLK : OpenSubgroup G) : Subgroup G).relIndex K = 1 := by
    rw [relIndex_eq_mul (d := D.deg) hSK, he, FrobeniusLift.relInertiaDegree_field hLK s]
    rfl
  have hπ' : D.valuation (s.field L hLK) ⟨π, fixedModule_anti hSK π.2⟩ = Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hSK π.2, he, pow_one]
    exact hπ
  have h := reciprocity_mk_eq_norm hLK hax s hπ'
  refine h.trans ?_
  congr 1
  ext
  rw [coe_norm_of_mem hSK π.2, hrel, pow_one]
end GroundTheory.LocalField.Abstract.ClassFieldData
