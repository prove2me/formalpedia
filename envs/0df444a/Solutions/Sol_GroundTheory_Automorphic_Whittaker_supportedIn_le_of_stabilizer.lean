-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.supportedIn_le_of_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:53.38282+00:00
-- url     : https://prove2.me/submissions/bb30ea2d-98ae-4ce1-9180-341c3aa369e5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_supportedIn
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_relSpan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_relSpan_le_supportedIn
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_smul_orbitPiece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_lift_orbit_piece
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_of_eqOn_orbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_base
import Theorems.Thm_GroundTheory_Automorphic_exists_compactOpenSubgroup_normalized

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
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U C : Set X} (hU : IsOpen U) (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (χ : H →* ℂ)
    (hχ : ∃ L : Subgroup H, IsOpen (L : Set H) ∧ ∀ l ∈ L, χ l = 1)
    {S₀ : Subgroup H} (hS₀ : IsCompact (S₀ : Set H)) {s : H} (hs : s ∈ S₀) (hsx : s • x₀ = x₀)
    (hχs : χ s ≠ 1) :
    supportedIn U ≤ relSpan χ U ⊔ (supportedIn U ⊓ vanishingOn C) := by
  obtain ⟨L, hLo, hχL⟩ := hχ
  obtain ⟨L₀, hL₀c, hL₀L, hL₀n⟩ := exists_compactOpenSubgroup_normalized hS₀ (hLo.mem_nhds L.one_mem)
  have hx₀ : x₀ ∈ orbit H x₀ := mem_orbit_self x₀
  have hWU := relSpan_le_supportedIn χ hUinv
  obtain ⟨f₀, hf₀, hf₀O⟩ := exists_lift_orbit_piece hU hC hO hL₀c L₀.isOpen hx₀
  set T := relSpan χ U ⊔ (supportedIn U ⊓ vanishingOn C)

  have hspiece : s • orbitPiece (L₀ : Subgroup H) x₀ = orbitPiece (L₀ : Subgroup H) x₀ := by
    rw [smul_orbitPiece (fun a ha => hL₀n s hs a ha)
      (fun a ha => by simpa using hL₀n s⁻¹ (S₀.inv_mem hs) a ha), hsx]
  have h1 : transl s f₀ - f₀ ∈ T := by
    refine le_sup_right (a := relSpan χ U) (sub_mem_of_eqOn_orbit hO
      (transl_mem_supportedIn hUinv s hf₀) hf₀ fun x hx => ?_)
    rw [transl_apply, hf₀O _ (mem_orbit_of_mem_orbit _ hx), hf₀O x hx]
    conv_rhs => rw [← hspiece]
    by_cases hxS : s⁻¹ • x ∈ orbitPiece (L₀ : Subgroup H) x₀
    · simp only [Set.indicator_of_mem hxS,
        Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hxS), Pi.one_apply]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]
  have h2 : transl s f₀ - χ s • f₀ ∈ T :=
    le_sup_left (b := supportedIn U ⊓ vanishingOn C) (sub_mem_relSpan χ s hf₀)
  have h3 : (χ s - 1) • f₀ ∈ T := by
    have e : (χ s - 1) • f₀ = (transl s f₀ - f₀) - (transl s f₀ - χ s • f₀) := by
      rw [sub_smul, one_smul]
      abel
    rw [e]
    exact T.sub_mem h1 h2
  have hbase : f₀ ∈ T := by
    have := T.smul_mem (χ s - 1)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hχs), one_smul] at this
  exact supportedIn_le_of_base hU hC hO hUinv χ hWU le_rfl (L₀ : Subgroup H) hL₀c L₀.isOpen
    (fun l hl => hχL l (hL₀L hl)) f₀ hf₀O hbase
end GroundTheory.Automorphic.Whittaker
