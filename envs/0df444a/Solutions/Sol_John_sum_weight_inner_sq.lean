-- Prove2me | solution 1 for John.sum_weight_inner_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:21:59.255103+00:00
-- url     : https://prove2.me/submissions/bce660e7-721d-4dff-aa15-04ddc6e55623

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

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}
namespace John
theorem _root_.solution {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) (z : EuclideanSpace 𝕜 (Fin k)) :
    ∑ i, c i * ‖⟪u i, z⟫_𝕜‖ ^ 2 = ‖z‖ ^ 2 := by
  have h : re ⟪(∑ i, ((c i : 𝕜) * ⟪u i, z⟫_𝕜) • u i), z⟫_𝕜 = re ⟪z, z⟫_𝕜 := by
    rw [hdec z]
  rw [sum_inner, map_sum, inner_self_eq_norm_sq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, RCLike.ofReal_re]
end John
