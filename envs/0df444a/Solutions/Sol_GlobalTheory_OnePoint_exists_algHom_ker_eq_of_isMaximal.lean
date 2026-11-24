-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_algHom_ker_eq_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:06.712028+00:00
-- url     : https://prove2.me/submissions/66f07c04-7049-493b-9a53-3d6c56eaa1c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (Ω : Type w) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (m : Ideal A) [m.IsMaximal] : ∃ φ : A →ₐ[K] Ω, RingHom.ker φ = m := by
  let := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let ψ : (A ⧸ m) →ₐ[K] Ω := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ K m), ?_⟩
  ext a
  simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero]
  exact Ideal.Quotient.eq_zero_iff_mem
end GlobalTheory.OnePoint
