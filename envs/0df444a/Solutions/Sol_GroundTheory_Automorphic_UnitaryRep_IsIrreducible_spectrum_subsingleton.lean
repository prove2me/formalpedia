-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsIrreducible.spectrum_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:38.47392+00:00
-- url     : https://prove2.me/submissions/224250ae-e7e0-45bc-8888-fe1d119ba992

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_nontrivial_endomorphisms
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_topologicalClosure
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_commute_of_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isInvariant_range
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_mem_intertwiners_self_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}
namespace GroundTheory.Automorphic.UnitaryRep
namespace IsIrreducible
theorem _root_.solution (hπ : π.IsIrreducible) {A : H →L[ℂ] H}
    (hA : A ∈ π.intertwiners π) (hsa : IsSelfAdjoint A) : (spectrum ℝ A).Subsingleton := by
  have := hπ.1
  have := nontrivial_endomorphisms (H := H)
  intro a ha b hb
  by_contra hab
  wlog hlt : a < b generalizing a b
  · exact this hb ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))
  set c := (a + b) / 2 with hc
  have hcb : c < b := by rw [hc]; linarith
  have hac : a < c := by rw [hc]; linarith
  let f : ℝ → ℝ := fun x => max (x - c) 0
  let g : ℝ → ℝ := fun x => max (c - x) 0
  have hfc : Continuous f := by fun_prop
  have hgc : Continuous g := by fun_prop
  have hgf : (fun x => g x * f x) = (0 : ℝ → ℝ) := by
    funext x
    rcases le_total x c with h | h
    · simp [f, max_eq_right (sub_nonpos.mpr h)]
    · simp [g, max_eq_right (sub_nonpos.mpr h)]
  have hQP : cfc g A * cfc f A = 0 := by
    rw [← cfc_mul g f A hgc.continuousOn hfc.continuousOn, hgf, cfc_zero]
  have hne : ∀ (φ : ℝ → ℝ), Continuous φ → ∀ x ∈ spectrum ℝ A, φ x ≠ 0 → cfc φ A ≠ 0 := by
    intro φ hφ x hx hφx h
    have hs : spectrum ℝ (cfc φ A) = φ '' spectrum ℝ A := cfc_map_spectrum φ A hsa hφ.continuousOn
    have hmem : φ x ∈ spectrum ℝ (cfc φ A) := hs ▸ ⟨x, hx, rfl⟩
    rw [h, spectrum.zero_eq, Set.mem_singleton_iff] at hmem
    exact hφx hmem
  have hP0 : cfc f A ≠ 0 := hne f hfc b hb (by
    simp only [f]; rw [max_eq_left (by linarith)]; linarith)
  have hQ0 : cfc g A ≠ 0 := hne g hgc a ha (by
    simp only [g]; rw [max_eq_left (by linarith)]; linarith)
  have hPmem : cfc f A ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun h => (commute_of_mem_intertwiners hA h).cfc_real f
  set V := (LinearMap.range ((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H)).topologicalClosure with hV
  have hinv : π.IsInvariant V := (isInvariant_range hPmem).topologicalClosure
  rcases hπ.2 V (Submodule.isClosed_topologicalClosure _) hinv with hbot | htop
  · apply hP0
    ext v
    have : cfc f A v ∈ V := Submodule.le_topologicalClosure _ ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    simpa using this
  · apply hQ0
    have hle : LinearMap.range ((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
        LinearMap.ker ((cfc g A : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rintro _ ⟨v, rfl⟩
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      have := congrArg (fun T : H →L[ℂ] H => T v) hQP
      simpa using this
    have hcl := Submodule.topologicalClosure_minimal _ hle (cfc g A).isClosed_ker
    rw [← hV, htop] at hcl
    ext v
    have : v ∈ LinearMap.ker ((cfc g A : H →L[ℂ] H) : H →ₗ[ℂ] H) := hcl Submodule.mem_top
    simpa using this
end IsIrreducible
end GroundTheory.Automorphic.UnitaryRep
