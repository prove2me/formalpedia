-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.recFrob_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:51.971365+00:00
-- url     : https://prove2.me/submissions/32631b4f-48d0-4b0d-b2c3-851ac575378c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_recFrob_congr
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_recFrob_mul_ofDegOne
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_deg_eq
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (s t : D.FrobeniusLift K) :
    D.recFrob L hLK (s.mul t) = D.recFrob L hLK s * D.recFrob L hLK t := by
  obtain ⟨φ, hφK, hdφ⟩ := exists_deg_eq (D := D) K
  suffices h : ∀ (m : ℕ) (s t : D.FrobeniusLift K), t.deg = m + 1 →
      D.recFrob L hLK (s.mul t) = D.recFrob L hLK s * D.recFrob L hLK t by
    obtain ⟨m, hm⟩ : ∃ m, t.deg = m + 1 := ⟨t.deg - 1, by have := t.deg_pos; omega⟩
    exact h m s t hm
  intro m
  induction m with
  | zero =>
    intro s t ht
    have hdt : D.deg t.elt = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
      rw [t.deg_eq, ht, zero_add, one_mul]
    rw [recFrob_congr hLK (s := s.mul t) (t := s.mul (FrobeniusLift.ofDegOne t.mem hdt)) rfl,
      recFrob_congr hLK (s := t) (t := FrobeniusLift.ofDegOne t.mem hdt) rfl]
    exact recFrob_mul_ofDegOne hLK hax s t.mem hdt
  | succ k ih =>
    intro s t ht
    set φ1 := FrobeniusLift.ofDegOne (D := D) hφK hdφ with hφ1
    let t' : D.FrobeniusLift K :=
      { elt := t.elt * φ⁻¹
        mem := K.mul_mem t.mem (K.inv_mem hφK)
        deg := k + 1
        deg_pos := Nat.succ_pos k
        deg_eq := by
          rw [map_mul, map_inv, t.deg_eq, hdφ, ht, ← ofAdd_neg, ← ofAdd_add]
          push_cast
          ring_nf }
    have h1 : D.recFrob L hLK (s.mul t) = D.recFrob L hLK ((s.mul t').mul φ1) :=
      recFrob_congr hLK (by simp [FrobeniusLift.mul, t', φ1, FrobeniusLift.ofDegOne, mul_assoc])
    have h2 : D.recFrob L hLK t = D.recFrob L hLK (t'.mul φ1) :=
      recFrob_congr hLK (by simp [FrobeniusLift.mul, t', φ1, FrobeniusLift.ofDegOne])
    rw [h1, h2, recFrob_mul_ofDegOne hLK hax _ hφK hdφ, recFrob_mul_ofDegOne hLK hax _ hφK hdφ,
      ih s t' rfl, mul_assoc]
end GroundTheory.LocalField.Abstract.ClassFieldData
