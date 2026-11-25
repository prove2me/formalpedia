-- Prove2me | solution 1 for John.continuous_rankOneSA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:07:52.404421+00:00
-- url     : https://prove2.me/submissions/bb976dd9-8b2b-4a7c-9db6-1f1697da350e

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
theorem _root_.solution :
    Continuous fun u : EuclideanSpace 𝕜 (Fin k) => rankOneSA (𝕜 := 𝕜) u := by
  show Continuous fun u : EuclideanSpace 𝕜 (Fin k) => (innerSL 𝕜 u).smulRight u
  have h : Continuous fun u : EuclideanSpace 𝕜 (Fin k) =>
      ContinuousLinearMap.smulRightL 𝕜 (EuclideanSpace 𝕜 (Fin k))
        (EuclideanSpace 𝕜 (Fin k)) (innerSL 𝕜 u) :=
    (ContinuousLinearMap.smulRightL 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (EuclideanSpace 𝕜 (Fin k))).continuous.comp (innerSL 𝕜).continuous
  simpa using h.clm_apply continuous_id
end John
