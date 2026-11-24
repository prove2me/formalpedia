-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.eq_zero_of_forall_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:49.71931+00:00
-- url     : https://prove2.me/submissions/3c7ecc4e-df3d-4a00-b794-ebfb72fecc41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [_root_.IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hb : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ k m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2
end GlobalTheory.ZH.ConePrime
