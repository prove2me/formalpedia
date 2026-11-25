-- Prove2me | solution 1 for John.mem_contact_of_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:07:47.813281+00:00
-- url     : https://prove2.me/submissions/2e4d9ac7-70ed-410d-98b4-478b9eef96e0

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
public import Theorems.Thm_Seminorm_exists_inner_le_of_apply


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hq1 : ∀ x, q x ≤ ‖x‖) {u : EuclideanSpace 𝕜 (Fin k)} (hu : ‖u‖ = 1) (hqu : q u = 1) :
    u ∈ Contact q := by
  obtain ⟨v, hvle, hvu⟩ := q.exists_inner_le_of_apply u
  rw [hqu] at hvu
  have hv1 : ‖v‖ ≤ 1 := by
    have h := (hvle v).trans (hq1 v)
    rw [inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  have hveq : v = u := by
    have hsub : ‖u - v‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq (𝕜 := 𝕜), hu, hvu]
      nlinarith [hv1, norm_nonneg v]
    have h0 : ‖u - v‖ = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hsub (sq_nonneg _))
    exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm
  refine ⟨hu, fun x => ?_⟩
  have h := hvle x
  rwa [hveq] at h
end John
