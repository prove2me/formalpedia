-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.isSmoothAt_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:48.415971+00:00
-- url     : https://prove2.me/submissions/df9fafea-6ace-4b70-832c-d9ea869ec119

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
import Theorems.Thm_GlobalTheory_isRegularRing_of_smooth


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero
namespace GlobalTheory.SS.DefectZero
theorem _root_.solution (R C B : Type) [CommRing R] [IsRegularRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra.FinitePresentation R C] [Algebra R B] (ψ : C →ₐ[R] B)
    (hs : Function.Surjective ψ) (x : Ideal B) [x.IsPrime] (x' : Ideal C) [x'.IsPrime]
    (hx : x' = x.comap ψ.toRingHom) [Algebra.IsSmoothAt R x'] (q : Ideal C) [q.IsPrime]
    (hq : q ≤ x') (h : ∀ c, ψ c = 0 → ∃ u ∉ q, u * c = 0) : Algebra.IsSmoothAt R x := by
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R x'
  have hS : IsRegularRing (Localization.Away f) := GlobalTheory.isRegularRing_of_smooth R _
  have disj : Disjoint (Submonoid.powers f : Set C) (x' : Set C) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let qS := x'.map (algebraMap C (Localization.Away f))
  have : qS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime qS) x' := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f)
      (Localization.AtPrime qS) qS
    exact (IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› disj).symm
  have := isRegularRing_iff.mp hS qS
  have : IsRegularLocalRing (Localization.AtPrime x') :=
    IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv x'.primeCompl
      (Localization.AtPrime qS) (Localization.AtPrime x')).toRingEquiv
  have := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain (Localization.AtPrime x')
  let l := Localization.localAlgHom x' x ψ hx
  have hl : Function.Bijective l := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_,
      (RingHom.surjectiveOnStalks_of_surjective (f := ψ.toRingHom) hs).localRingHom_surjective _ _ hx⟩
    obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq x'.primeCompl y
    change Localization.localRingHom x' x ψ.toRingHom hx _ = 0 at hy
    rw [Localization.localRingHom_mk',
      IsLocalization.mk'_eq_zero_iff] at hy
    obtain ⟨⟨t, ht⟩, hy⟩ := hy
    obtain ⟨t, rfl⟩ := hs t
    obtain ⟨u, hu, hut⟩ := h (t * y) (by rw [map_mul]; exact hy)
    have h1 := congrArg (algebraMap C (Localization.AtPrime x')) hut
    rw [map_mul, map_zero, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · obtain ⟨⟨v, hv⟩, hvu⟩ := (IsLocalization.map_eq_zero_iff x'.primeCompl _ _).mp h1
      rcases ‹q.IsPrime›.mem_or_mem_of_mul_eq_zero hvu with h2 | h2
      · exact (hv (hq h2)).elim
      · exact (hu h2).elim
    · obtain ⟨v, hvu⟩ := (IsLocalization.map_eq_zero_iff x'.primeCompl _ _).mp h1
      rw [IsLocalization.mk'_eq_zero_iff]
      exact ⟨v * ⟨t, fun h => ht (hx.le h)⟩, (mul_assoc _ _ _).trans hvu⟩
  exact .of_equiv (AlgEquiv.ofBijective l hl)
end GlobalTheory.SS.DefectZero
