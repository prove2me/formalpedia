-- Prove2me | solution 1 for John.rankOneSA_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:25.510804+00:00
-- url     : https://prove2.me/submissions/195d741f-317f-438b-90da-9f8955f7b039

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
theorem _root_.solution (u x : EuclideanSpace 𝕜 (Fin k)) :
    rankOneSA u x = ⟪u, x⟫_𝕜 • u := rfl
end John
