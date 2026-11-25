-- Prove2me | solution 1 for GlobalTheory.VeryDenseFibres.eq_top_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:27.93247+00:00
-- url     : https://prove2.me/submissions/d6a7b3b1-2bc9-4b3a-ab9d-d7199f597e77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionAndGeometricallyConnect

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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.VeryDenseFibres
namespace GlobalTheory.VeryDenseFibres
theorem _root_.solution {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R)
    [UniversallyClosed s] (P : Set (Ideal R))
    (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p) (U : Z.Opens)
    (hU : ∀ z : Z, (s z).asIdeal ∈ P → z ∈ U) : U = ⊤ := by
  rw [← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  obtain ⟨p, hp, hp', hle⟩ := hP (s x).asIdeal (PrimeSpectrum.isPrime _)
  have hs : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨y, hy, hy'⟩ := hs.mem_closed hc ⟨x, hx, rfl⟩
  exact hy (hU y (by rw [hy']; exact hp))
end GlobalTheory.VeryDenseFibres
