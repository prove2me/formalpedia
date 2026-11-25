-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.exists_units_eq_smul_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:31.624852+00:00
-- url     : https://prove2.me/submissions/ea6a6acf-db81-4dbd-9768-e3943c15524d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_eq_smul_div_of_mem_augmentation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_units
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_range_valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_of_mem
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti


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
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
variable {K L : OpenSubgroup G}
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) {φ : (K : Subgroup G)}
    (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {u : fixedModule A (L : Subgroup G)}
    (hN : norm A (K : Subgroup G) (L : Subgroup G) u = 1) :
    ∃ ε ∈ D.units L, (u : A) = (φ : G) • (ε : A) / ε := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcard := (hax K L hLK (D.isCyclic_of_unramified hLK hu)).2
  have hsub := (Nat.card_eq_one_iff_unique.1 hcard).1

  have haug : (u : A) ∈ augmentation A (K : Subgroup G) (L : Subgroup G) := by
    have h := (QuotientGroup.eq_one_iff
      (N := (augmentation A (K : Subgroup G) (L : Subgroup G)).comap
        ((fixedModule A (L : Subgroup G)).subtype.comp
          (norm A (K : Subgroup G) (L : Subgroup G)).ker.subtype))
      (⟨u, hN⟩ : (norm A (K : Subgroup G) (L : Subgroup G)).ker)).1 (Subsingleton.elim _ _)
    exact h
  obtain ⟨b, hb, hub⟩ := D.exists_eq_smul_div_of_mem_augmentation hLK hu hφ haug

  have hval : D.valuation L ⟨b, hb⟩ ∈ (D.valuation K).range := by
    rw [range_valuation, ← D.range_valuation L]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := hval
  have he : relRamificationIndex D.deg K L = 1 := isUnramified_iff.2 hu
  refine ⟨⟨b, hb⟩ / ⟨c, fixedModule_anti hLK c.2⟩, ?_, ?_⟩
  · rw [D.mem_units, map_div, D.valuation_of_mem hLK c.2, he, pow_one]
    change D.valuation L ⟨b, hb⟩ / D.valuation K c = 1
    rw [hc, div_self']
  · have hφc : (φ : G) • (c : A) = c := c.2 φ φ.2
    change (u : A) = (φ : G) • ((b : A) / c) / (b / c)
    rw [smul_div', hφc, div_div_div_cancel_right, hub]
end GroundTheory.LocalField.Abstract.ClassFieldData
