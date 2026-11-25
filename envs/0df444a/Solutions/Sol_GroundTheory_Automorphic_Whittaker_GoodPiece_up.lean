-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.GoodPiece.up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:26:31.465806+00:00
-- url     : https://prove2.me/submissions/f63ce98f-7a22-4d8f-8116-5569a2840f0b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift_orbit_piece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_of_eqOn_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_of_mem
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
omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
namespace GroundTheory.Automorphic.Whittaker
namespace GoodPiece
theorem _root_.solution {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W)
    {J A : Subgroup H} (hJc : IsCompact (J : Set H)) (hAo : IsOpen (A : Set H)) (hAJ : A ≤ J)
    (hAn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) {y : X} (hy : y ∈ orbit H x₀)
    (hA : GoodPiece (H := H) U C x₀ W (orbitPiece A y)) :
    GoodPiece (H := H) U C x₀ W (orbitPiece J y) := by
  classical
  have hOl : IsLocallyClosed (orbit H x₀) := ⟨U, C, hU, hC, hO.symm⟩
  obtain ⟨𝒮, -, h𝒮, hsum⟩ := exists_finset_orbitPiece hOl hJc hAo hAJ hAn hy
  have hAc : IsCompact (A : Set H) := hJc.of_isClosed_subset (A.isClosed_of_isOpen hAo) hAJ
  obtain ⟨gA, hgA, hgAO⟩ := exists_lift_orbit_piece hU hC hO hAc hAo hy
  have hgAT := hA gA hgA hgAO
  choose! j hjJ hjS using h𝒮
  intro g hg hgJ
  refine mem_of_eqOn_orbit hO hWU hg (f := ∑ S ∈ 𝒮, transl (j S) gA)
    (Submodule.sum_mem _ fun S _ => transl_mem_of_mem χ hWU hW _ hgAT) fun x hx => ?_
  rw [hgJ x hx, hsum x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [transl_apply, hgAO _ (mem_orbit_of_mem_orbit _ hx)]
  conv_lhs => rw [hjS S hS]
  by_cases hxS : (j S)⁻¹ • x ∈ orbitPiece A y
  · simp only [Set.indicator_of_mem hxS,
      Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hxS), Pi.one_apply]
  · rw [Set.indicator_of_notMem hxS,
      Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]
end GoodPiece
end GroundTheory.Automorphic.Whittaker
