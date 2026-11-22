-- Prove2me | solution 1 for LocallyConvexDuality.bipolar_eq_closure_absConvexHull
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:57:33.831379+00:00
-- url     : https://prove2.me/submissions/51a6c81f-e5cb-4681-b4c0-dbb9e9bd9fe8

import Mathlib

open scoped ComplexOrder

set_option autoImplicit false

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (A : Set E) :
    B.flip.polar (B.polar A) =
      closure (X := WeakBilin B) (absConvexHull 𝕜 (insert (0 : E) A)) := by
  -- `C` is the weakly closed absolutely convex hull of `A ∪ {0}`
  let C : Set (WeakBilin B) := closure (X := WeakBilin B) (absConvexHull 𝕜 (insert (0 : E) A))
  have hsub : insert (0 : E) A ⊆ C :=
    subset_absConvexHull.trans (subset_closure (X := WeakBilin B))
  apply Set.Subset.antisymm
  · -- `A°° ⊆ C`: separate a point outside `C` from `C` by a weakly continuous functional
    intro x hx
    by_contra hxC
    let : Module ℝ (WeakBilin B) := Module.restrictScalars ℝ 𝕜 _
    have : IsScalarTower ℝ 𝕜 (WeakBilin B) := IsScalarTower.restrictScalars ℝ 𝕜 _
    have : LocallyConvexSpace ℝ (WeakBilin B) :=
      B.weakBilin_withSeminorms.toLocallyConvexSpace
    have hC : AbsConvex 𝕜 C := AbsConvex.closure (E := WeakBilin B) absConvex_absConvexHull
    obtain ⟨f, r, hfr, hrx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
      (E := WeakBilin B) (s := C) (x := x) (hC.2.lift ℝ) isClosed_closure hxC
    -- every weakly continuous functional is `B · y` for some `y : F`
    obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective B f
    have hfy : ∀ z : WeakBilin B, f z = B z y := fun z => by rw [← hy]; rfl
    -- rotate the value of the pairing to the nonnegative real axis (`C` is balanced)
    have hnorm : ∀ z : WeakBilin B, z ∈ C → ‖B z y‖ < r := by
      intro z hz
      obtain ⟨c, hc, hcz⟩ := RCLike.exists_norm_eq_mul_self (B z y)
      have hmem : c • z ∈ C := balanced_iff_smul_mem.mp hC.1 hc.le hz
      have h : RCLike.re (f (c • z)) < r := hfr (c • z) hmem
      have h2 : f (c • z) = ((‖B z y‖ : ℝ) : 𝕜) := by
        rw [map_smul, hfy, smul_eq_mul, ← hcz]
      rw [h2, RCLike.ofReal_re] at h
      exact h
    have hr : 0 < r := (norm_nonneg _).trans_lt (hnorm 0 (hsub (Set.mem_insert _ _)))
    have hscale : ∀ z : E, ‖B z ((r : 𝕜)⁻¹ • y)‖ = ‖B z y‖ / r := by
      intro z
      rw [map_smul, smul_eq_mul, norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hr,
        div_eq_inv_mul]
    -- `r⁻¹ • y` lies in the polar of `A`
    have hy' : (r : 𝕜)⁻¹ • y ∈ B.polar A := by
      intro z hz
      rw [hscale, div_le_iff₀ hr, one_mul]
      exact (hnorm z (hsub (Set.mem_insert_of_mem _ hz))).le
    have hbound : ‖B x ((r : 𝕜)⁻¹ • y)‖ ≤ 1 := hx _ hy'
    rw [hscale, div_le_iff₀ hr, one_mul] at hbound
    have hrx' : r < RCLike.re (B x y) := lt_of_lt_of_eq hrx (congrArg RCLike.re (hfy x))
    exact absurd hbound (not_le.mpr (hrx'.trans_le (RCLike.re_le_norm _)))
  · -- `C ⊆ A°°`: the bipolar is weakly closed, absolutely convex and contains `A ∪ {0}`
    exact closure_minimal (X := WeakBilin B)
      (absConvexHull_min (Set.insert_subset (B.flip.zero_mem_polar _) (B.subset_bipolar A))
        (LinearMap.polar_AbsConvex _)) (B.flip.polar_isClosed (B.polar A))
