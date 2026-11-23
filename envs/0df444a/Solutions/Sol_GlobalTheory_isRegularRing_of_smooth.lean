-- Prove2me | solution 1 for GlobalTheory.isRegularRing_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:47.202888+00:00
-- url     : https://prove2.me/submissions/b6280167-406e-4dc6-b06c-81544bdc9453

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Theorems.Thm_GlobalTheory_isRegularRing_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B],
      IsRegularRing B := by
  intro V B _ _ _ _ _
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing V B
  refine isRegularRing_iff.mpr fun Q _ => ?_
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := V) (p := Q)
  have hT : IsRegularRing (Localization.Away f) :=
    isRegularRing_of_etale (MvPolynomial (Fin n) V) (Localization.Away f)
  have disj : Disjoint (Submonoid.powers f : Set B) (Q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let Q' := Q.map (algebraMap B (Localization.Away f))
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime Q') Q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f)
      (Localization.AtPrime Q') Q'
    exact (IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› disj).symm
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q') (Localization.AtPrime Q)).toRingEquiv
end GlobalTheory
