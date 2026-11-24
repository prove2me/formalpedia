-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.exists_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:07.565433+00:00
-- url     : https://prove2.me/submissions/8eb2ecff-8182-479d-bcbe-baf0225f6459

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.ArtinKernel
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
namespace GlobalTheory.ArtinKernel
theorem _root_.solution {ι : Type*} (δ : ι → R) (hδ : ∃ i, δ i ≠ 0) :
    ∃ lam : R →ₗ[ℂ] ℂ, (∃ i, lam (δ i) ≠ 0) ∧
      ∀ i, ∀ r ∈ IsLocalRing.maximalIdeal R, lam (r * δ i) = 0 := by
  classical
  set m := IsLocalRing.maximalIdeal R
  set N : Submodule ℂ R := Submodule.span ℂ {x | ∃ r ∈ m, ∃ i, x = r * δ i} with hN
  have hex : ∃ i, δ i ∉ N := by
    by_contra! hall
    set J : Ideal R := Ideal.span (Set.range δ) with hJ
    have hNJ : ∀ x ∈ N, x ∈ m • J := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => x ∈ m • J) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨r, hr, i, rfl⟩
        exact Submodule.smul_mem_smul hr (Ideal.subset_span ⟨i, rfl⟩)
      · exact zero_mem _
      · intro x y _ _ hx hy
        exact add_mem hx hy
      · intro c x _ hx
        exact Submodule.smul_of_tower_mem _ c hx
    have hle : J ≤ m • J := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hNJ _ (hall i)
    have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
    have hJ0 : J = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m J
      (IsNoetherian.noetherian J) hle
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
    obtain ⟨i, hi⟩ := hδ
    apply hi
    have : δ i ∈ J := Ideal.subset_span ⟨i, rfl⟩
    rw [hJ0] at this
    exact (Submodule.mem_bot R).mp this
  obtain ⟨i, hi⟩ := hex
  obtain ⟨lam, hlam, hker⟩ := Submodule.exists_le_ker_of_notMem hi
  refine ⟨lam, ⟨i, hlam⟩, fun j r hr => ?_⟩
  exact hker (Submodule.subset_span ⟨r, hr, j, rfl⟩)
end GlobalTheory.ArtinKernel
