-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:39.202799+00:00
-- url     : https://prove2.me/submissions/718f853e-6a27-4404-8346-bb574c5a2437

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_support
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset

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
omit [TotallyDisconnectedSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace H]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U C : Set X} (hC : IsClosed C) {x₀ : X}
    (hO : U ∩ C = orbit H x₀) {f : X → ℂ} (hf : f ∈ supportedIn U) :
    ∃ L : Subgroup H, IsCompact (L : Set H) ∧ IsOpen (L : Set H) ∧
      ∀ l ∈ L, ∀ x ∈ orbit H x₀, f (l • x) = f x := by
  have hOC : orbit H x₀ ⊆ C := hO ▸ inter_subset_right
  let K := C ∩ Function.support f
  have hK : IsCompact K := (isCompact_support hf.1).inter_left hC
  let Wset : Set (H × X) := {p | f (p.1 • p.2) = f p.2}
  have hWo : IsOpen Wset := by
    have hF : IsLocallyConstant fun p : H × X => (f (p.1 • p.2), f p.2) :=
      (hf.1.1.comp_continuous continuous_smul).prodMk (hf.1.1.comp_continuous continuous_snd)
    exact hF {q | q.1 = q.2}
  have hsub : ({1} : Set H) ×ˢ K ⊆ Wset := by
    rintro ⟨h, x⟩ ⟨hh, -⟩
    simp only [mem_singleton_iff] at hh
    simp [Wset, hh]
  obtain ⟨u, v, hu, -, h1u, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hWo hsub
  obtain ⟨L, hLc, hLu⟩ := exists_openSubgroup_isCompact_subset (hu.mem_nhds (h1u rfl))
  refine ⟨L, hLc, L.isOpen, fun l hl x hx => ?_⟩
  by_cases hxK : x ∈ K
  · exact huv (show (l, x) ∈ u ×ˢ v from ⟨hLu hl, hKv hxK⟩)
  · have hfx : f x = 0 := by
      by_contra h
      exact hxK ⟨hOC hx, h⟩
    rw [hfx]
    by_contra h
    have hlx : l • x ∈ K := ⟨hOC (mem_orbit_of_mem_orbit l hx), h⟩
    have := huv (show (l⁻¹, l • x) ∈ u ×ˢ v from ⟨hLu (L.inv_mem hl), hKv hlx⟩)
    simp only [Wset, Set.mem_ofPred_eq, inv_smul_smul] at this
    exact h (by rw [← this, hfx])
end GroundTheory.Automorphic.Whittaker
