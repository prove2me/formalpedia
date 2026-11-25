-- Prove2me | solution 1 for GlobalTheory.SmoothDedekind.le_ringKrullDim_quotient_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:14:45.434331+00:00
-- url     : https://prove2.me/submissions/a8983f86-1de3-4155-82ec-7d26df3e1b45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe

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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing
namespace GlobalTheory.SmoothDedekind
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {d : WithBot ℕ∞} (hd : ∀ q ∈ minimalPrimes S, d ≤ ringKrullDim (S ⧸ q)) :
    ∀ p ∈ minimalPrimes R, d ≤ ringKrullDim (R ⧸ p) := by
  intro p hp
  have := hp.1.1
  have h : p.map (e : R →+* S) ∈ minimalPrimes S := by
    refine ⟨⟨Ideal.map_isPrime_of_equiv e, bot_le⟩, fun q hq hle ↦ ?_⟩
    have := hq.1
    rw [Ideal.map_le_iff_le_comap]
    refine hp.2 ⟨Ideal.comap_isPrime _ q, bot_le⟩ ?_
    refine (Ideal.comap_mono hle).trans ?_
    rw [Ideal.comap_map_of_bijective (e : R →+* S) e.bijective]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv p _ e rfl)]
  exact hd _ h
end GlobalTheory.SmoothDedekind
