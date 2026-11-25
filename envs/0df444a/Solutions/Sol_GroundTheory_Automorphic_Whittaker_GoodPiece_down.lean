-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.GoodPiece.down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:32.683093+00:00
-- url     : https://prove2.me/submissions/49e8ce07-7ebb-479c-83cb-e781ea2e6bb6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_supportedIn
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_relSpan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_finset_orbitPiece
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
namespace GoodPiece
theorem _root_.solution {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hW : relSpan χ U ≤ W)
    {J A : Subgroup H} (hJc : IsCompact (J : Set H)) (hχJ : ∀ j ∈ J, χ j = 1)
    (hAo : IsOpen (A : Set H)) (hAJ : A ≤ J)
    (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {y : X} (hy : y ∈ orbit H x₀)
    (hJ : GoodPiece (H := H) U C x₀ W (orbitPiece J y)) :
    GoodPiece (H := H) U C x₀ W (orbitPiece A y) := by
  classical
  have hOl : IsLocallyClosed (orbit H x₀) := ⟨U, C, hU, hC, hO.symm⟩
  obtain ⟨𝒮, hne, h𝒮, hsum⟩ := exists_finset_orbitPiece hOl hJc hAo hAJ hAn hy
  choose! j hjJ hjS using h𝒮
  intro gA hgA hgAO
  set T := W ⊔ (supportedIn U ⊓ vanishingOn C)
  have hG : ∑ S ∈ 𝒮, transl (j S) gA ∈ T := by
    refine hJ _ (Submodule.sum_mem _ fun S _ => transl_mem_supportedIn hUinv _ hgA)
      fun x hx => ?_
    rw [hsum x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [transl_apply, hgAO _ (mem_orbit_of_mem_orbit _ hx)]
    conv_rhs => rw [hjS S hS]
    by_cases hxS : (j S)⁻¹ • x ∈ orbitPiece A y
    · simp only [Set.indicator_of_mem hxS,
        Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hxS), Pi.one_apply]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]
  have hR : ∑ S ∈ 𝒮, (transl (j S) gA - χ (j S) • gA) ∈ T :=
    le_sup_left (b := supportedIn U ⊓ vanishingOn C)
      (hW (Submodule.sum_mem _ fun S _ => sub_mem_relSpan χ _ hgA))
  have hcard : (𝒮.card : ℂ) • gA ∈ T := by
    have e : (𝒮.card : ℂ) • gA =
        ∑ S ∈ 𝒮, transl (j S) gA - ∑ S ∈ 𝒮, (transl (j S) gA - χ (j S) • gA) := by
      rw [Finset.sum_sub_distrib, sub_sub_cancel, Finset.sum_congr rfl fun S hS => by
        rw [hχJ _ (hjJ S hS), one_smul], Finset.sum_const, Nat.cast_smul_eq_nsmul]
    rw [e]
    exact T.sub_mem hG hR
  have hc : (𝒮.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hne)
  have := T.smul_mem (𝒮.card : ℂ)⁻¹ hcard
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
end GoodPiece
end GroundTheory.Automorphic.Whittaker
