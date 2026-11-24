-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeFixed.form_eK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:22.920444+00:00
-- url     : https://prove2.me/submissions/67658209-30d6-4671-bf8e-5f390202b166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeFixed
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
variable {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
  (hKc : IsCompact (K : Set G))
namespace GlobalTheory.CompanionTheory.HeckeFixed
theorem _root_.solution (l : Module.Dual ℂ V) (hl : ∀ x ∈ K, l ∘ₗ π x = l) (v : V) :
    l (eK π hπ hKc v : V) = l v := by
  have hker : coK (resK π K) ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨k, x⟩, rfl⟩
    have h := LinearMap.congr_fun (hl k k.2) x
    simp only [LinearMap.comp_apply] at h
    simp [h]
  have hs : v - (eK π hπ hKc v : V) ∈ coK (resK π K) := by
    have := Submodule.sub_projection_mem (isCompl_res hπ hKc) v
    rwa [Submodule.projection_apply] at this
  have h0 := hker hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
  exact h0.symm
end GlobalTheory.CompanionTheory.HeckeFixed
