-- Prove2me | solution 1 for GlobalTheory.DegKer.finrank_eq_pow_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:06:01.07937+00:00
-- url     : https://prove2.me/submissions/e3285853-5342-4e64-a240-522c537116f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_ZV_ActsBy_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer
namespace GlobalTheory.DegKer
theorem _root_.solution (R S Ω : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    [FaithfulSMul R Ω] (p : ℕ) [ExpChar R p] :
    Nat.card (S →ₐ[R] Ω) ≠ 0 ∧ ∃ e : ℕ, Module.finrank R S = p ^ e * Nat.card (S →ₐ[R] Ω) := by
  let F := FractionRing R
  let E := FractionRing S
  letI : Algebra F E := FractionRing.liftAlgebra R E
  letI : Algebra F Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R F E := FractionRing.isScalarTower_liftAlgebra R E
  haveI : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : FiniteDimensional F E := inferInstance
  haveI : ExpChar F p := expChar_of_injective_algebraMap (IsFractionRing.injective R F) p
  obtain ⟨e, he⟩ := finInsepDegree_eq_pow F E p
  have hc : Nat.card (E →ₐ[F] Ω) = Nat.card (S →ₐ[R] Ω) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun σ => (σ.restrictScalars R).comp (IsScalarTower.toAlgHom R S E)) ⟨?_, ?_⟩)
    · intro σ τ h
      apply AlgHom.coe_ringHom_injective
      exact IsFractionRing.ringHom_ext (A := S) fun x => DFunLike.congr_fun h x
    · intro g
      have hg : Function.Injective g := by
        rw [injective_iff_map_eq_zero]
        have : RingHom.ker g = ⊥ := by
          refine Ideal.eq_bot_of_comap_eq_bot (R := R) (eq_bot_iff.mpr fun x hx => ?_)
          have hx' : g (algebraMap R S x) = 0 := hx
          rw [AlgHom.commutes] at hx'
          exact (FaithfulSMul.algebraMap_injective R Ω) (by simpa using hx')
        intro a ha
        have : a ∈ RingHom.ker g := ha
        simp_all
      let σ : E →ₐ[R] Ω := IsFractionRing.liftAlgHom hg
      refine ⟨{ σ.toRingHom with commutes' := fun x => ?_ }, ?_⟩
      · have : σ.toRingHom.comp (algebraMap F E) = algebraMap F Ω :=
          IsFractionRing.ringHom_ext (A := R) fun x => by
            simp [← IsScalarTower.algebraMap_apply]
        exact DFunLike.congr_fun this x
      · ext x
        simp [σ]
  rw [← hc, ← Field.finSepDegree_eq_of_isAlgClosed F E Ω]
  refine ⟨NeZero.ne _, e, ?_⟩
  rw [← he, mul_comm, Field.finSepDegree_mul_finInsepDegree,
    Algebra.IsAlgebraic.finrank_of_isFractionRing R F S E]
end GlobalTheory.DegKer
