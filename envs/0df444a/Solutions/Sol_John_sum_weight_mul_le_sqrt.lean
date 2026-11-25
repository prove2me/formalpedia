-- Prove2me | solution 1 for John.sum_weight_mul_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:07:44.890794+00:00
-- url     : https://prove2.me/submissions/0dd5b9b2-8b34-4da9-a6be-9933247f1adc

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
theorem _root_.solution {N : ℕ} (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (t : Fin N → ℝ) :
    ∑ i, c i * t i ≤ Real.sqrt (∑ i, c i) * Real.sqrt (∑ i, c i * t i ^ 2) := by
  have hcsum : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  have hquad : 0 ≤ ∑ i, c i * t i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  -- Cauchy–Schwarz for the two vectors `√cᵢ` and `√cᵢ · tᵢ`.
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (c i)) (fun i => Real.sqrt (c i) * t i)
  have e1 : ∀ i, Real.sqrt (c i) * (Real.sqrt (c i) * t i) = c i * t i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hc i)]
  have e2 : ∀ i, (Real.sqrt (c i)) ^ 2 = c i := fun i => Real.sq_sqrt (hc i)
  have e3 : ∀ i, (Real.sqrt (c i) * t i) ^ 2 = c i * t i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hc i)]
  simp only [e1, e2, e3] at h
  -- `(∑ cᵢtᵢ)² ≤ (∑ cᵢ)(∑ cᵢtᵢ²)`, so the claim follows by taking square roots.
  calc ∑ i, c i * t i ≤ |∑ i, c i * t i| := le_abs_self _
    _ = Real.sqrt ((∑ i, c i * t i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, c i) * ∑ i, c i * t i ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (∑ i, c i) * Real.sqrt (∑ i, c i * t i ^ 2) := Real.sqrt_mul hcsum _
end John
