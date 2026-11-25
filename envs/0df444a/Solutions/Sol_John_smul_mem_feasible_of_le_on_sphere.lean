-- Prove2me | solution 1 for John.smul_mem_feasible_of_le_on_sphere
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:33.746679+00:00
-- url     : https://prove2.me/submissions/64551ee0-2fe2-42b9-a6ef-99379ae1fbbf

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
theorem _root_.solution {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    {T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)} {s : ℝ} (hs : 0 < s)
    (hT : ∀ u, ‖u‖ = 1 → q (T u) ≤ s) : ((s⁻¹ : ℝ) : 𝕜) • T ∈ Feasible q := by
  intro x
  rw [smul_apply, map_smul_eq_mul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hs)]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set u : EuclideanSpace 𝕜 (Fin k) := ((‖x‖⁻¹ : ℝ) : 𝕜) • x with hudef
    have hun : ‖u‖ = 1 := by
      rw [hudef, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hxn),
        inv_mul_cancel₀ hxn.ne']
    have hxu : x = ((‖x‖ : ℝ) : 𝕜) • u := by
      rw [hudef, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hxn.ne',
        RCLike.ofReal_one, one_smul]
    have hTx : q (T x) = ‖x‖ * q (T u) := by
      conv_lhs => rw [hxu]
      rw [map_smul, map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hxn]
    rw [hTx]
    calc s⁻¹ * (‖x‖ * q (T u)) ≤ s⁻¹ * (‖x‖ * s) := by
          have h3 : ‖x‖ * q (T u) ≤ ‖x‖ * s :=
            mul_le_mul_of_nonneg_left (hT u hun) hxn.le
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = s⁻¹ * s * ‖x‖ := by ring
      _ = ‖x‖ := by rw [inv_mul_cancel₀ hs.ne', one_mul]
end John
