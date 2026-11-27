-- Prove2me | solution 1 for GlobalTheory.WithAction.toBase_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:59.147384+00:00
-- url     : https://prove2.me/submissions/daedcd80-c3f9-47f8-88ab-549aa1528537

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe w v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.WithAction
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [AddCommGroup N]
  (ρ : A →+* AddMonoid.End M) (σ : A →+* AddMonoid.End N)
variable (R : Type*) [CommRing R] [Algebra R A]
namespace GlobalTheory.WithAction
theorem _root_.solution (f : M ≃+ N) (h : ∀ a x, f (ρ a x) = σ a (f x)) (x : WithAction ρ) :
    toBase σ (linearEquiv ρ σ R f h x) = f (toBase ρ x) := rfl
end GlobalTheory.WithAction
