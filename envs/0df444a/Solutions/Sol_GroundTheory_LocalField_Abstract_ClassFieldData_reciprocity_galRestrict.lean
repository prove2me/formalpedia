-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_galRestrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:00.383483+00:00
-- url     : https://prove2.me/submissions/37336ab1-bfc3-47ee-9753-0e4a09c5a8dc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
import Theorems.Thm_GroundTheory_LocalField_Abstract_frobeniusClosure_mono
import Theorems.Thm_GroundTheory_LocalField_Abstract_normTateZero_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_inertiaDegree_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_frobeniusLift_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_mk_eq_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relInertiaDegree_ne_zero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_eq_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_norm


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
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] {D : ClassFieldData G A}
variable [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {K L K' L' : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (hL'K' : L' ≤ K') [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (q : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') :
    D.reciprocity hLK hax (galRestrict hK hL q) =
      normTateZero hK hL hL'K' hLK (D.reciprocity hL'K' hax q) := by
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hL'K' q
  set t := s.toBase hK with htdef
  have ht : t.deg = s.deg * relInertiaDegree D.deg K K' := rfl
  have hle : s.field L' hL'K' ≤ t.field L hLK := fun x hx => frobeniusClosure_mono hL s.elt hx
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L' hL'K')
  have hrel : relInertiaDegree D.deg (t.field L hLK) (s.field L' hL'K') = 1 := by
    have h1 := inertiaDegree_eq_mul D.surjective_deg
      (K := ((t.field L hLK : OpenSubgroup G) : Subgroup G))
      (L := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) hle
    rw [s.inertiaDegree_field hL'K', t.inertiaDegree_field hLK, ht,
      inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (K' : Subgroup G)) hK] at h1
    have hpos : 0 < s.deg * relInertiaDegree D.deg K K' * inertiaDegree D.deg K :=
      Nat.mul_pos (Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hK)))
        (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [one_mul]
    exact h1.symm.trans (Nat.mul_assoc _ _ _).symm
  set π0 := norm A ((t.field L hLK : OpenSubgroup G) : Subgroup G)
    ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G) π with hπ0def
  have hπ0 : D.valuation (t.field L hLK) π0 = Multiplicative.ofAdd 1 := by
    rw [hπ0def, D.valuation_norm hle, hrel, pow_one, hπ]
  have e1 : galRestrict hK hL ((⟨s.elt, s.mem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨t.elt, t.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := rfl
  rw [e1, D.reciprocity_mk_eq_norm hLK hax t hπ0, D.reciprocity_mk_eq_norm hL'K' hax s hπ,
    normTateZero_mk, hπ0def,
    norm_norm (M := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) (s.field_le hL'K') hK,
    norm_norm (M := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) hle (t.field_le hLK)]
end GroundTheory.LocalField.Abstract.ClassFieldData
