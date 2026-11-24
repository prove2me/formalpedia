-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_forall_algHom_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:37:01.665616+00:00
-- url     : https://prove2.me/submissions/b46df86f-0a9d-41b3-ac1e-c7995e32f022

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type*} [CommRing A] [Algebra ℂ A] [_root_.IsReduced A]
    [Algebra.FiniteType ℂ A] (a : A) (h : ∀ e : A →ₐ[ℂ] ℂ, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ ℂ m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2
end GlobalTheory
