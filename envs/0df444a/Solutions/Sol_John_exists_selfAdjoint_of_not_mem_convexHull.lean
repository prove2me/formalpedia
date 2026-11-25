-- Prove2me | solution 1 for John.exists_selfAdjoint_of_not_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:09:23.516252+00:00
-- url     : https://prove2.me/submissions/7ca5f097-8458-4b71-b988-e200f18e7cfa

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John
public import Theorems.Thm_John_isCompact_contact
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_John_continuous_rankOneSA
public import Theorems.Thm_John_trace_rankOneSA_comp
public import Theorems.Thm_ContinuousLinearMap_exists_trace_repr
public import Theorems.Thm_ContinuousLinearMap_trace_adjoint
public import Theorems.Thm_IsCompact_convexHull

attribute [local simp] John.rankOneSA_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution (hk : 0 < k)
    {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hmem : ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
      ∉ convexHull ℝ (rankOneSA '' Contact q)) :
    ∃ (H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (δ : ℝ), 0 < δ ∧
      IsSelfAdjoint H ∧
      LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
        (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0 ∧
      ∀ u ∈ Contact q, re ⟪u, H u⟫_𝕜 ≤ -δ := by
  classical
  have : FiniteDimensional ℝ
      (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :=
    Module.Finite.trans 𝕜 (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k))
  -- the convex hull of the contact projections is compact, hence closed
  have hcompact : IsCompact (convexHull ℝ (rankOneSA '' Contact q)) :=
    ((isCompact_contact q).image continuous_rankOneSA).convexHull
  -- separate the point from the closed convex hull
  obtain ⟨f, β, hfs, hfx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    (convex_convexHull ℝ _) hcompact.isClosed hmem
  -- represent the separating functional by trace duality
  obtain ⟨G, hG⟩ := ContinuousLinearMap.exists_trace_repr (𝕜 := 𝕜) f.toLinearMap
  have hfu : ∀ u : EuclideanSpace 𝕜 (Fin k), f (rankOneSA u) = ⟪u, G u⟫_𝕜 := fun u => by
    have h := hG (rankOneSA u)
    rwa [trace_rankOneSA_comp] at h
  have hfid : f (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
      = LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
          (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) := by
    have h := hG (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    rwa [ContinuousLinearMap.coe_id, LinearMap.id_comp] at h
  -- the self-adjoint part of `G`, normalized to trace zero
  set H₀ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    ((((1 : ℝ) / 2 : ℝ)) : 𝕜) • (G + ContinuousLinearMap.adjoint G) with hH₀
  set τ : ℝ := re (LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
    (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))) / k with hτ
  set H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    H₀ - ((τ : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) with hH
  -- pointwise form of `H`
  have hHapp : ∀ w, H w = ((((1 : ℝ) / 2 : ℝ)) : 𝕜) • (G w + ContinuousLinearMap.adjoint G w)
      - ((τ : ℝ) : 𝕜) • w := fun w => by
    simp only [hH, hH₀, sub_apply, smul_apply,
      add_apply, ContinuousLinearMap.id_apply]
  -- `H` is self-adjoint: its quadratic form is symmetric
  have hHsa : IsSelfAdjoint H := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    show ⟪H x, y⟫_𝕜 = ⟪x, H y⟫_𝕜
    rw [hHapp x, hHapp y]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, RCLike.conj_ofReal,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    ring
  -- traces
  have htrH₀ : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H₀ : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
      = ((re (LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
          (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))) : ℝ) : 𝕜) := by
    rw [hH₀, ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_add,
      map_smul, map_add, ContinuousLinearMap.trace_adjoint, RCLike.add_conj, smul_eq_mul]
    push_cast
    ring
  have htrH : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0 := by
    have hkK : ((k : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    rw [hH, ContinuousLinearMap.toLinearMap_sub, map_sub, htrH₀, ContinuousLinearMap.toLinearMap_smul,
      map_smul, ContinuousLinearMap.coe_id, LinearMap.trace_id, finrank_euclideanSpace_fin,
      hτ, smul_eq_mul]
    push_cast
    field_simp
    ring
  -- the gap
  set δ : ℝ := re (f ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))) - β
    with hδdef
  have hδpos : 0 < δ := sub_pos.mpr hfx
  -- the quadratic form of the self-adjoint part is that of `G`
  have hquad : ∀ w : EuclideanSpace 𝕜 (Fin k),
      re ⟪w, ((((1 : ℝ) / 2 : ℝ)) : 𝕜) • (G w + ContinuousLinearMap.adjoint G w)⟫_𝕜
        = re ⟪w, G w⟫_𝕜 := fun w => by
    have h2 : re ⟪w, ContinuousLinearMap.adjoint G w⟫_𝕜 = re ⟪w, G w⟫_𝕜 := by
      rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm w (G w), RCLike.conj_re]
    rw [inner_smul_right, RCLike.re_ofReal_mul, inner_add_right, map_add, h2]
    ring
  have hτre : re (f ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))) = τ := by
    rw [ContinuousLinearMap.map_smul_of_tower, RCLike.smul_re, hfid, hτ]
    ring
  refine ⟨H, δ, hδpos, hHsa, htrH, fun u hu => ?_⟩
  -- the contact bound
  have h1 : re (f (rankOneSA u)) < β :=
    hfs _ (subset_convexHull ℝ _ (Set.mem_image_of_mem _ hu))
  rw [hfu u] at h1
  have h2 : re ⟪u, H u⟫_𝕜 = re ⟪u, G u⟫_𝕜 - τ := by
    rw [hHapp u, inner_sub_right, map_sub, hquad u, inner_smul_right,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq, hu.1]
    ring
  rw [h2, hδdef, hτre]
  linarith
end John
