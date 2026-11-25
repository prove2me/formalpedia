-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_nhds_inter_doubleCoset_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:01.011073+00:00
-- url     : https://prove2.me/submissions/f5af7c2f-b17b-4dc1-8462-7eaa6fb601d6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpenMap_doubleCoset

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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Topology Set DoubleCoset
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SigmaCompactSpace G]
variable {P Q : Subgroup G}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {y : G} (hy : y ∈ doubleCoset x (P : Set G) Q) {UP UQ : Set G} (hUP : UP ∈ 𝓝 (1 : G))
    (hUQ : UQ ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ UP ∧ ∃ q ∈ Q, q ∈ UQ ∧ z = p * y * q := by
  have hCy : doubleCoset y (P : Set G) Q = doubleCoset x (P : Set G) Q := doubleCoset_eq_of_mem hy
  rw [← hCy] at hC ⊢
  have hopen := isOpenMap_doubleCoset hP hQ y hC
  set W : Set (P × Q) := {pq | (pq.1 : G) ∈ interior UP ∧ (pq.2 : G) ∈ interior UQ}
  have hW : IsOpen W :=
    (isOpen_interior.preimage (continuous_subtype_val.comp continuous_fst)).inter
      (isOpen_interior.preimage (continuous_subtype_val.comp continuous_snd))
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (hopen W hW)
  have h1 : (1 : P × Q) ∈ W := ⟨mem_interior_iff_mem_nhds.2 hUP, mem_interior_iff_mem_nhds.2 hUQ⟩
  have hyV : y ∈ V := by
    have : (⟨y, mem_doubleCoset_self P Q y⟩ : doubleCoset y (P : Set G) Q) ∈
        Subtype.val ⁻¹' V := by
      rw [hV]
      exact ⟨1, h1, Subtype.ext (by simp)⟩
    exact this
  refine ⟨V, hVo.mem_nhds hyV, fun z hz hzC => ?_⟩
  have : (⟨z, hzC⟩ : doubleCoset y (P : Set G) Q) ∈ Subtype.val ⁻¹' V := hz
  rw [hV] at this
  obtain ⟨pq, hpq, hpqz⟩ := this
  refine ⟨pq.1, pq.1.2, interior_subset hpq.1, pq.2, pq.2.2, interior_subset hpq.2, ?_⟩
  exact (congrArg Subtype.val hpqz).symm
end GroundTheory.Automorphic.Parabolic
