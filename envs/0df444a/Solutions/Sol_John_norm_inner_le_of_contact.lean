-- Prove2me | solution 1 for John.norm_inner_le_of_contact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:21:54.84973+00:00
-- url     : https://prove2.me/submissions/7a4a0839-851c-4b9a-8536-5941713766db

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
theorem _root_.solution {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    {u : EuclideanSpace 𝕜 (Fin k)} (hu : u ∈ Contact q) (x : EuclideanSpace 𝕜 (Fin k)) :
    ‖⟪x, u⟫_𝕜‖ ≤ q x := by
  rcases eq_or_ne (⟪x, u⟫_𝕜) 0 with h | h
  · rw [h, norm_zero]; exact apply_nonneg q x
  · set c := ⟪x, u⟫_𝕜 with hcdef
    have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hkey : re ⟪(c / (‖c‖ : 𝕜)) • x, u⟫_𝕜 = ‖c‖ := by
      rw [inner_smul_left, map_div₀, RCLike.conj_ofReal, div_mul_eq_mul_div,
        RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_div, RCLike.ofReal_re,
        pow_two, mul_div_assoc, div_self hcnorm, mul_one]
    have hle := hu.2 ((c / (‖c‖ : 𝕜)) • x)
    rw [hkey, map_smul_eq_mul, norm_div, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg c), div_self hcnorm, one_mul] at hle
    exact hle
end John
