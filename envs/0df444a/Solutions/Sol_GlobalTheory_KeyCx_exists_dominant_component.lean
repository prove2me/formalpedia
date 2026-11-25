-- Prove2me | solution 1 for GlobalTheory.KeyCx.exists_dominant_component
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:53.622671+00:00
-- url     : https://prove2.me/submissions/09e9ba8e-e8d1-4af1-b65d-965d0de2aa50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsDominantComponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyCx
open TensorProduct
namespace GlobalTheory.KeyCx
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (g : R →+* ℂ), ∃ (E : Type) (_ : CommRing E) (_ : IsDomain E) (_ : Algebra ℂ E) (ρ : R →+* E) (e : E →ₐ[ℂ] ℂ), Algebra.FiniteType ℂ E ∧ Function.Injective ρ ∧ e.toRingHom.comp ρ = g := by
  intro R _ _ _ g
  letI : Algebra R (ℂ ⊗[ℤ] R) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat R (ℂ ⊗[ℤ] R) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight ℤ R ℂ).symm.toLinearEquiv
  let e₀ : (ℂ ⊗[ℤ] R) →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) g.toIntAlgHom (fun _ _ => Commute.all _ _)
  have he : ∀ r : R, e₀ (algebraMap R (ℂ ⊗[ℤ] R) r) = g r := by
    intro r
    change e₀ (1 ⊗ₜ r) = g r
    simp [e₀]
  let Q : Ideal (ℂ ⊗[ℤ] R) := RingHom.ker e₀.toRingHom
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hqQ, hq, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal R)) (q := Q.under R) Q bot_le
  refine ⟨(ℂ ⊗[ℤ] R) ⧸ q, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk q).comp (algebraMap R _),
    Ideal.Quotient.liftₐ q e₀ (fun a ha => hqQ ha), inferInstance, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : r ∈ q.under R :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    rw [← hlo.over] at h1
    exact h1
  · ext r
    exact he r
end GlobalTheory.KeyCx
