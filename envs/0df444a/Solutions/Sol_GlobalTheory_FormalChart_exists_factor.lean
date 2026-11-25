-- Prove2me | solution 1 for GlobalTheory.FormalChart.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:45.139714+00:00
-- url     : https://prove2.me/submissions/362424a8-d41a-41bb-b340-433b1515a41b

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
import Theorems.Thm_GlobalTheory_FormalChart_ext_of_isHausdorff
import Theorems.Thm_GlobalTheory_algHom_sub_constantCoeff_mem
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mvEvalAdic_X



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
    (e : B →ₐ[O] O) (φ : B →ₐ[O] MvPowerSeries (Fin g) O)
    (h₁ : ∀ b, MvPowerSeries.constantCoeff (φ b) = e b)
    (h₂ : ∀ j, φ (π (MvPolynomial.X j) - algebraMap O B (e (π (MvPolynomial.X j)))) = MvPowerSeries.X j)
    {T : Type} [CommRing T] [Algebra O T] (J : Ideal T) [IsAdicComplete J T] (ψ : B →ₐ[O] T)
    (hψ : ∀ b, ψ b - algebraMap O T (e b) ∈ J) :
    ∃ v : MvPowerSeries (Fin g) O →ₐ[O] T, (∀ i, v (MvPowerSeries.X i) ∈ J) ∧ v.comp φ = ψ := by
  let v := GlobalTheory.mvEvalAdic O J (fun j => ψ (π (MvPolynomial.X j)) - algebraMap O T (e (π (MvPolynomial.X j))))
    (fun j => hψ _)
  have hv : ∀ j, v (MvPowerSeries.X j) =
      ψ (π (MvPolynomial.X j)) - algebraMap O T (e (π (MvPolynomial.X j))) := fun j =>
    GlobalTheory.mvEvalAdic_X _ _ _ j
  have hv' : ∀ j, v (MvPowerSeries.X j) ∈ J := fun j => hv j ▸ hψ _
  refine ⟨v, hv', ext_of_isHausdorff π hπ J _ _ (fun b => ?_) (fun j => ?_)⟩
  · have := GlobalTheory.algHom_sub_constantCoeff_mem v hv' (φ b)
    rw [h₁] at this
    have h3 := sub_mem this (hψ b)
    rwa [sub_sub_sub_cancel_right] at h3
  · have := hv j
    rw [← h₂, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at this
    exact this
end GlobalTheory.FormalChart
