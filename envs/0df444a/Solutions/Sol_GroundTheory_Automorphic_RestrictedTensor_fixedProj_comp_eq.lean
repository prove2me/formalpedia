-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.fixedProj_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:23.636278+00:00
-- url     : https://prove2.me/submissions/eabf0de3-c282-4c93-8c9d-def902493641

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_sub_fixedProj_mem_span
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
omit hρ hKc hKo
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L] (ι : L →* G)
    (hρ : IsSmooth ρ) (hρι : IsSmooth (ρ.comp ι)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {K' : Subgroup L} (hK'c : IsCompact (K' : Set L))
    (hK'o : IsOpen (K' : Set L)) (hK' : ∀ k ∈ K', ι k ∈ K) {u : V}
    (hu : ∀ h ∈ K, ∃ k ∈ K', ρ h u = ρ (ι k) u) :
    (fixedProj (ρ.comp ι) hρι hK'c hK'o u : V) = fixedProj ρ hρ hKc hKo u := by
  have hmem : (fixedProj ρ hρ hKc hKo u : V) ∈ fixedVectors (ρ.comp ι) K' :=
    fun k hk => (fixedProj ρ hρ hKc hKo u).2 _ (hK' k hk)
  have h1 := sub_fixedProj_mem_span hρ hKc hKo u
  have h2 : Submodule.span ℂ (range fun k : K => ρ k u - u) ≤ coinvariantsKer (ρ.comp ι) K' := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨k, hk, hkh⟩ := hu h hh
    simp only [SetLike.mem_coe]
    rw [hkh]
    exact sub_mem_coinvariantsKer (ρ := ρ.comp ι) hk u
  have := (fixedProj_eq_iff hρι hK'c hK'o (w := ⟨_, hmem⟩)).2 (h2 h1)
  rw [this]
end GroundTheory.Automorphic.RestrictedTensor
