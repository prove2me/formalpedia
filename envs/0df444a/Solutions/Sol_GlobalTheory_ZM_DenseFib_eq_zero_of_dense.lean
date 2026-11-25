-- Prove2me | solution 1 for GlobalTheory.ZM.DenseFib.eq_zero_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:16:46.843042+00:00
-- url     : https://prove2.me/submissions/c56d89bb-0fa7-4dd7-897d-1d3b41b79a5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemIdealOfOfDense
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DenseFib
namespace GlobalTheory.ZM.DenseFib
theorem _root_.solution {A : Type} [CommRing A] [_root_.IsReduced A] (D : Set (Sp A)) (hD : Dense D) (a : A)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : A →+* K), Set.range (spMap κ) ⊆ D → κ a = 0) :
    a = 0 := by
  by_contra ha
  have hne : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)).Nonempty := by
    by_contra hn
    refine ha (IsNilpotent.eq_zero ((PrimeSpectrum.basicOpen_eq_bot_iff a).1 ?_))
    exact eq_bot_iff.2 fun z hz => (hn ⟨z, hz⟩).elim
  obtain ⟨q, hqa, hqD⟩ := hD.inter_open_nonempty _ (PrimeSpectrum.basicOpen a).isOpen hne
  let q' : PrimeSpectrum A := q
  let K := AlgebraicClosure q'.asIdeal.ResidueField
  let κ : A →+* K := (algebraMap q'.asIdeal.ResidueField K).comp (algebraMap A _)
  have hker : ∀ z, κ z = 0 ↔ z ∈ q'.asIdeal := fun z => by
    simp only [κ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap q'.asIdeal.ResidueField K).injective]
    exact Ideal.algebraMap_residueField_eq_zero
  have h0 := h K κ (by
    rintro _ ⟨p, rfl⟩
    have : spMap κ p = q := by
      apply PrimeSpectrum.ext
      ext z
      have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := p.isPrime)
      change κ z ∈ p.asIdeal ↔ z ∈ q'.asIdeal
      rw [hp, ← hker]; rfl
    rwa [this])
  exact hqa ((hker a).1 h0)
end GlobalTheory.ZM.DenseFib
