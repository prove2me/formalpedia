-- Prove2me | solution 1 for GlobalTheory.FormalChart.ext_of_isHausdorff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:48.978703+00:00
-- url     : https://prove2.me/submissions/5b68c785-98c8-46c4-a64c-c2a5cbd4fb23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LePreimageOfClosedPoint
import Theorems.Thm_GlobalTheory_eq_of_forall_sub_mem_ideal_pow
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
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.FormalChart
variable {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B] {g : ℕ}
namespace GlobalTheory.FormalChart
theorem _root_.solution (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra O A] (J : Ideal A) [IsHausdorff J A] (φ₁ φ₂ : B →ₐ[O] A)
    (h : ∀ b, φ₁ b - φ₂ b ∈ J)
    (hs : ∀ j : Fin g, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  let ρ : MvPolynomial (Fin g) O →ₐ[O] A := φ₁.comp π
  have hρ2 : φ₂.comp π = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin g) O] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin g) O] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  have hJ : ⨅ i, J ^ i = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => by
      rw [sub_zero]
      exact Ideal.mem_iInf.1 hx n
  have : ψ₁ = ψ₂ := Algebra.FormallyUnramified.ext_of_iInf J hJ fun b => Ideal.Quotient.eq.2 (h b)
  ext x
  exact AlgHom.congr_fun this x
end GlobalTheory.FormalChart
