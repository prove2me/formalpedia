-- Prove2me | solution 1 for GlobalTheory.GaloisPowerRoots.exists_sub_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:11.57566+00:00
-- url     : https://prove2.me/submissions/4ad3747f-b385-42b7-8bf7-b9bd22cc2221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Polynomial IsLocalRing
open scoped Pointwise
open GlobalTheory GlobalTheory.GaloisPowerRoots
namespace GlobalTheory.GaloisPowerRoots
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    [IsAlgClosed (ResidueField A)] (t : B) :
    ∃ a : A, t - algebraMap A B a ∈ maximalIdeal B := by
  haveI : IsLocalHom (algebraMap A B) := inferInstance
  have hint : (ResidueField.map (algebraMap A B)).IsIntegral := by
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    obtain ⟨p, hp, hp2⟩ := Algebra.IsIntegral.isIntegral (R := A) y
    refine ⟨p.map (residue A), hp.map _, ?_⟩
    rw [eval₂_map, ResidueField.map_comp_residue, ← hom_eval₂, hp2, map_zero]
  obtain ⟨x, hx⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral _ hint).2 (residue B t)
  obtain ⟨a, rfl⟩ := residue_surjective x
  refine ⟨a, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hx, ResidueField.map_residue, sub_self]
end GlobalTheory.GaloisPowerRoots
