-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.mk_norm_eq_primeNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:23:44.084909+00:00
-- url     : https://prove2.me/submissions/c01b1abb-9ad6-4bf7-b8d8-9025147767fd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_norm_mem_range_of_mem_units
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_units


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
  (D : ClassFieldData G A)
variable {D} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {π : fixedModule A (S : Subgroup G)}
    (hπ : D.valuation S π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.primeNorm K L S := by
  set π0 := (D.exists_prime S).choose with hπ0
  have h0 : D.valuation S π0 = Multiplicative.ofAdd 1 := (D.exists_prime S).choose_spec
  have hu' : π * π0⁻¹ ∈ D.units S := by
    rw [D.mem_units, map_mul, map_inv, hπ, h0, mul_inv_cancel]
  obtain ⟨b, hb⟩ := D.norm_mem_range_of_mem_units hax hSK hLK hu hu'
  rw [primeNorm, ← hπ0, QuotientGroup.eq]
  have : (norm A (K : Subgroup G) (S : Subgroup G) π)⁻¹ * norm A (K : Subgroup G) (S : Subgroup G) π0 =
      (norm A (K : Subgroup G) (S : Subgroup G) (π * π0⁻¹))⁻¹ := by
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_comm]
  rw [this]
  exact Subgroup.inv_mem _ ⟨b, hb⟩
end GroundTheory.LocalField.Abstract.ClassFieldData
