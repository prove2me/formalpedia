-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.nonempty_equiv_of_matrixCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:26:31.208804+00:00
-- url     : https://prove2.me/submissions/6c6dbdad-7670-4baa-a4e5-2e83e12213c4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_orbit
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply_act
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_orbitMap_single
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_orbitMap_mapDomain
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_range_orbitMap
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_linearForm_orbitMap

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
open Set
open GroundTheory.Automorphic.RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    [ρ.IsIrreducible] [σ.IsIrreducible] {v : V} {l : Module.Dual ℂ V} {w : W}
    {m : Module.Dual ℂ W} (h : ∀ g, l (ρ g v) = m (σ g w)) (hne : ∃ g, l (ρ g v) ≠ 0) :
    Nonempty (ρ.Equiv σ) := by
  obtain ⟨g₀, hg₀⟩ := hne
  have hv : v ≠ 0 := by rintro rfl; simp at hg₀
  have hm : m ≠ 0 := by rintro rfl; exact hg₀ (by rw [h]; rfl)

  have hker : LinearMap.ker (orbitMap ρ v) ≤ LinearMap.ker (orbitMap σ w) := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    refine eq_zero_of_forall_apply_act (ρ := σ) hm fun k => ?_
    rw [linearForm_orbitMap]
    have := linearForm_orbitMap ρ v l k c
    rw [hc, map_zero, map_zero] at this
    rw [this]
    exact Finsupp.sum_congr fun g _ => by rw [h]
  have hsurj : Function.Surjective (orbitMap ρ v) := by
    rw [← LinearMap.range_eq_top, range_orbitMap]
    exact eq_top_iff.2 fun x _ => mem_span_orbit hv x
  let e := LinearMap.quotKerEquivOfSurjective (orbitMap ρ v) hsurj
  let F : V →ₗ[ℂ] W := ((LinearMap.ker (orbitMap ρ v)).liftQ (orbitMap σ w) hker).comp
    e.symm.toLinearMap
  have hF : ∀ c, F (orbitMap ρ v c) = orbitMap σ w c := by
    intro c
    have : e.symm (orbitMap ρ v c) = Submodule.Quotient.mk c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hFint : ∀ g x, F (ρ g x) = σ g (F x) := by
    intro g x
    obtain ⟨c, rfl⟩ := hsurj x
    rw [← orbitMap_mapDomain, hF, hF, orbitMap_mapDomain]
  let Fi : Representation.IntertwiningMap ρ σ := ⟨F, fun g => LinearMap.ext fun x => hFint g x⟩
  have hFi0 : Fi ≠ 0 := by
    intro h0
    have h1 : F v = w := by
      have := hF (Finsupp.single 1 1)
      rwa [orbitMap_single, orbitMap_single, one_smul, one_smul, map_one,
        Module.End.one_apply, map_one, Module.End.one_apply] at this
    have h2 : F v = 0 := by
      have : Fi v = 0 := by rw [h0]; rfl
      exact this
    apply hg₀
    rw [h, ← h1, h2, map_zero, map_zero]
  rcases Representation.IsIrreducible.bijective_or_eq_zero Fi with hb | h0
  · exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective F hb)
      fun g => LinearMap.ext fun x => hFint g x⟩
  · exact absurd h0 hFi0
end GroundTheory.Automorphic.RestrictedTensor
