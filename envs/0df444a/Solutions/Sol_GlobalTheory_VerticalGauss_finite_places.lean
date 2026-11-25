-- Prove2me | solution 1 for GlobalTheory.VerticalGauss.finite_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:56:45.850964+00:00
-- url     : https://prove2.me/submissions/84185bb2-2742-49a0-9bd2-8356dedb97f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteVerticalGaussValuations
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_placesOver_iff_loc
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_dedekindRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.VerticalGauss
open IsLocalRing IsDedekindDomain
namespace GlobalTheory.VerticalGauss
theorem _root_.solution {R Ω : Type} [CommRing R] [IsDomain R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower R (FractionRing R) Ω]
    [FiniteDimensional (FractionRing R) Ω]
    (P : Ideal R) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)] :
    {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧
      ∀ x : R, 0 ≤ v (algebraMap R Ω x) ∧ (0 < v (algebraMap R Ω x) ↔ x ∈ P)}.Finite := by
  set O := Localization.AtPrime P
  set F := FractionRing R
  letI : Algebra O Ω := ((algebraMap F Ω).comp (algebraMap O F)).toAlgebra
  haveI : IsScalarTower O F Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R O Ω := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply O F Ω, ← IsScalarTower.algebraMap_apply R O F,
      ← IsScalarTower.algebraMap_apply R F Ω])
  haveI : CharZero F := RingHom.charZero (algebraMap F Ω)
  obtain ⟨hD, _, _, _, hmax, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F Ω
  haveI : IsFractionRing (integralClosure O Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension F Ω
  haveI := hmax.to_subtype
  haveI : Finite (HeightOneSpectrum (integralClosure O Ω)) := by
    refine Finite.of_injective (fun v => (⟨v.asIdeal, v.isMaximal⟩ :
      {I : Ideal (integralClosure O Ω) | I.IsMaximal})) ?_
    intro v v' h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)
  obtain ⟨e, -⟩ := ValPl.placesOver_bij O F Ω
  have hfin : (ValPl.PlacesOver O Ω).Finite := Set.finite_coe_iff.1 (Finite.of_equiv _ e)
  refine hfin.subset ?_
  rintro v ⟨h1, h2⟩
  exact ⟨h1, (ValPl.placesOver_iff_loc P v).1 h2⟩
end GlobalTheory.VerticalGauss
