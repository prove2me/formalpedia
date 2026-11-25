-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_finset_orbitPiece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:27.01145+00:00
-- url     : https://prove2.me/submissions/1dea9686-512b-4516-ba0c-104697c3b1d0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_self_mem_orbitPiece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_orbitPiece_eq_or_disjoint
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_smul_orbitPiece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuousSMul_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isOpen_orbitPiece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
variable {U C : Set X} {x₀ : X}
omit [TotallyDisconnectedSpace X] [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hOl : IsLocallyClosed (orbit H x₀)) {J A : Subgroup H}
    (hJc : IsCompact (J : Set H)) (hAo : IsOpen (A : Set H)) (hAJ : A ≤ J)
    (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {y : X} (hy : y ∈ orbit H x₀) :
    ∃ 𝒮 : Finset (Set X), 𝒮.Nonempty ∧ (∀ S ∈ 𝒮, ∃ j ∈ J, S = j • orbitPiece A y) ∧
      ∀ x, (orbitPiece J y).indicator (1 : X → ℂ) x = ∑ S ∈ 𝒮, S.indicator 1 x := by
  classical
  have hsm : ∀ j ∈ J, j • orbitPiece A y = orbitPiece A (j • y) := fun j hj =>
    smul_orbitPiece (hAn j hj) (fun a ha => by simpa using hAn j⁻¹ (J.inv_mem hj) a ha) y
  have hsub : ∀ j ∈ J, orbitPiece A (j • y) ⊆ orbitPiece J y := by
    rintro j hj _ ⟨a, ha, rfl⟩
    exact ⟨a * j, J.mul_mem (hAJ ha) hj, mul_smul a j y⟩

  let K' : Set (orbit H x₀) := (fun j : H => j • (⟨y, hy⟩ : orbit H x₀)) '' (J : Set H)
  have := continuousSMul_orbit (H := H) x₀
  have hK' : IsCompact K' := hJc.image (continuous_id.smul continuous_const)
  obtain ⟨t, htJ, htfin, hcov⟩ := hK'.elim_finite_subcover_image (b := (J : Set H))
    (c := fun j => (Subtype.val : orbit H x₀ → X) ⁻¹' orbitPiece A (j • y))
    (fun j _ => isOpen_orbitPiece hOl hAo (mem_orbit_of_mem_orbit j hy))
    (by
      rintro _ ⟨j, hj, rfl⟩
      exact mem_iUnion₂.2 ⟨j, hj, self_mem_orbitPiece A _⟩)
  have hcov' : ∀ x ∈ orbitPiece J y, ∃ j ∈ t, x ∈ orbitPiece A (j • y) := by
    rintro _ ⟨j, hj, rfl⟩
    have hx : (j • (⟨y, hy⟩ : orbit H x₀)) ∈ K' := ⟨j, hj, rfl⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hcov hx)
    exact ⟨i, hi, hxi⟩
  refine ⟨htfin.toFinset.image fun j => orbitPiece A (j • y), ?_, ?_, ?_⟩
  · obtain ⟨j, hj, -⟩ := hcov' y (self_mem_orbitPiece J y)
    exact ⟨_, Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hj)⟩
  · intro S hS
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hS
    have hjJ := htJ (htfin.mem_toFinset.1 hj)
    exact ⟨j, hjJ, (hsm j hjJ).symm⟩
  · intro x
    by_cases hx : x ∈ orbitPiece J y
    · obtain ⟨j, hj, hxj⟩ := hcov' x hx
      rw [Set.indicator_of_mem hx, Finset.sum_eq_single (orbitPiece A (j • y))]
      · rw [Set.indicator_of_mem hxj]
      · intro S hS hSne
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
        refine Set.indicator_of_notMem (fun hxi => hSne ?_) _
        rcases orbitPiece_eq_or_disjoint A (i • y) (j • y) with e | e
        · exact e
        · exact absurd hxj (Set.disjoint_left.1 e hxi)
      · intro h
        exact absurd (Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hj)) h
    · rw [Set.indicator_of_notMem hx]
      refine (Finset.sum_eq_zero fun S hS => ?_).symm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hS
      exact Set.indicator_of_notMem (fun hxi => hx (hsub i (htJ (htfin.mem_toFinset.1 hi)) hxi)) _
end GroundTheory.Automorphic.Whittaker
