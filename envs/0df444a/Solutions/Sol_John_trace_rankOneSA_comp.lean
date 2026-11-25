-- Prove2me | solution 1 for John.trace_rankOneSA_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:08:04.748963+00:00
-- url     : https://prove2.me/submissions/4b4f30f3-d71b-4871-81ac-bdc366880296

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
theorem _root_.solution (u : EuclideanSpace 𝕜 (Fin k))
    (G : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      ((rankOneSA u : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) ∘ₗ
        (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))) = ⟪u, G u⟫_𝕜 := by
  have hcomp : (rankOneSA u : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) ∘ₗ
      (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
      = LinearMap.smulRight
          (((innerSL 𝕜 u).comp G : EuclideanSpace 𝕜 (Fin k) →L[𝕜] 𝕜) :
            EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] 𝕜) u := by
    ext x
    simp [rankOneSA_apply]
  rw [hcomp, LinearMap.trace_smulRight]
  simp
end John
