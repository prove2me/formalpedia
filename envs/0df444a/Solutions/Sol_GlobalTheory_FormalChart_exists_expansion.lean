-- Prove2me | solution 1 for GlobalTheory.FormalChart.exists_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:48.201552+00:00
-- url     : https://prove2.me/submissions/64202bec-a02f-4da5-8ec7-7a0b5b60fcaf

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
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



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
    (e : B →ₐ[O] O) :
    ∃ φ : B →ₐ[O] MvPowerSeries (Fin g) O, (∀ b, MvPowerSeries.constantCoeff (φ b) = e b) ∧
      ∀ j, φ (π (MvPolynomial.X j) - algebraMap O B (e (π (MvPolynomial.X j)))) = MvPowerSeries.X j := by
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  let A := MvPowerSeries (Fin g) O
  let ρ : MvPolynomial (Fin g) O →ₐ[O] A :=
    MvPolynomial.aeval (fun j => algebraMap O A (e (π (MvPolynomial.X j))) + MvPowerSeries.X j)
  letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range MvPowerSeries.X)
  have hf₀ : ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).comp π =
      (Ideal.Quotient.mkₐ O J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X, Algebra.ofId_apply]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin g) O] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  obtain ⟨φ', hφ'⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := J) f₀
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  let φ : B →ₐ[O] A := { φ'.toRingHom with
    commutes' := fun r => by
      show φ' (algebraMap O B r) = _
      rw [← π.commutes, hc, ρ.commutes] }
  have hφ : ∀ b, φ b = φ' b := fun _ => rfl
  have hJ : J ≤ RingHom.ker (MvPowerSeries.constantCoeff) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact MvPowerSeries.constantCoeff_X i
  refine ⟨φ, fun b => ?_, fun j => ?_⟩
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (algebraMap O A (e b)) :=
      AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    have e2 := hJ e1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at e2
    exact e2.trans (MvPowerSeries.constantCoeff_C _)
  · rw [map_sub, AlgHom.commutes, hφ, hc]
    simp [ρ]
end GlobalTheory.FormalChart
