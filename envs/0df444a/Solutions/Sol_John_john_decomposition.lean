-- Prove2me | solution 1 for John.john_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:12:52.611175+00:00
-- url     : https://prove2.me/submissions/2e31689a-c030-4888-8f6e-56a0f2bd912c

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
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_John_mem_contact_of_apply_eq_one
public import Theorems.Thm_John_exists_selfAdjoint_of_not_mem_convexHull
public import Theorems.Thm_John_no_neg_direction_of_maxVolume
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
theorem _root_.solution (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hq : Continuous q) (hq1 : ∀ u, q u ≤ ‖u‖)
    (hmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1) :
    ∃ (N : ℕ) (u : Fin N → EuclideanSpace 𝕜 (Fin k)) (c : Fin N → ℝ),
      (∀ i, u i ∈ Contact q) ∧ (∀ i, 0 ≤ c i) ∧ (∑ i, c i = (k : ℝ)) ∧
      (∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- the space is trivial: the empty decomposition works
    subst hk0
    refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by simp, fun x => ?_⟩
    have hx : x = 0 := by
      ext i
      exact i.elim0
    simp [hx]
  -- `k⁻¹ • id` is a convex combination of contact projections
  have hmem : ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
      ∈ convexHull ℝ (rankOneSA '' Contact q) := by
    by_contra hmem
    obtain ⟨H, δ, hδ, hHsa, htr, hneg⟩ := exists_selfAdjoint_of_not_mem_convexHull hk hmem
    exact no_neg_direction_of_maxVolume hk hq hq1 hmax hHsa htr hδ
      fun u hu hqu => hneg u (mem_contact_of_apply_eq_one hq1 hu hqu)
  obtain ⟨ι, hfin, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hmem
  let : Fintype ι := hfin
  choose v hv hvz using fun i => hz i
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  have hkR : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  refine ⟨Fintype.card ι, fun j => v (e j), fun j => (k : ℝ) * w (e j),
    fun j => hv (e j), fun j => mul_nonneg (Nat.cast_nonneg k) (hw0 (e j)), ?_, ?_⟩
  · -- the weights sum to `k`
    rw [Equiv.sum_comp e (fun i => (k : ℝ) * w i), ← Finset.mul_sum, hw1, mul_one]
  · -- the decomposition of identity, evaluated at `x`
    intro x
    have hx := DFunLike.congr_fun hsum x
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.id_apply] at hx
    have hzi : ∀ i, z i x = ⟪v i, x⟫_𝕜 • v i := fun i => by
      rw [← hvz i, rankOneSA_apply]
    have hx2 : ∑ i, ((((k : ℝ) * w i : ℝ) : 𝕜) * ⟪v i, x⟫_𝕜) • v i = x := by
      have h3 : ∑ i, (k : ℝ) • w i • z i x = x := by
        have h4 : (k : ℝ) • ∑ i, w i • z i x = (k : ℝ) • ((k : ℝ)⁻¹ • x) := by rw [hx]
        rwa [smul_smul, mul_inv_cancel₀ hkR, one_smul, Finset.smul_sum] at h4
      calc ∑ i, ((((k : ℝ) * w i : ℝ) : 𝕜) * ⟪v i, x⟫_𝕜) • v i
          = ∑ i, (k : ℝ) • w i • z i x := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hzi i, smul_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul]
        _ = x := h3
    calc ∑ j, ((((k : ℝ) * w (e j) : ℝ) : 𝕜) * ⟪v (e j), x⟫_𝕜) • v (e j)
        = ∑ i, ((((k : ℝ) * w i : ℝ) : 𝕜) * ⟪v i, x⟫_𝕜) • v i :=
          Equiv.sum_comp e (fun i => ((((k : ℝ) * w i : ℝ) : 𝕜) * ⟪v i, x⟫_𝕜) • v i)
      _ = x := hx2
end John
