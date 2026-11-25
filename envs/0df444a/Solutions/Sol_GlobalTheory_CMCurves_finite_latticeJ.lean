-- Prove2me | solution 1 for GlobalTheory.CMCurves.finite_latticeJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:57.18459+00:00
-- url     : https://prove2.me/submissions/6c3982a0-52c0-45fb-809e-99fd735e9ac4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Theorems.Thm_GlobalTheory_CMCurves_latticeJ_eq_of_class_eq
import Theorems.Thm_GlobalTheory_CMLattice_exists_ideal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
open GlobalTheory
open GlobalTheory.CMCurves
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.CMCurves
theorem _root_.solution (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    (latticeJ '' {L | ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice}).Finite := by
  classical
  set S := latticeJ '' {L : PeriodPair | ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice}
  have key : ∀ j : S, ∃ (𝔞 : (Ideal (𝓞 K))⁰) (L : PeriodPair) (c : ℂ), c ≠ 0 ∧
      latticeJ L = j ∧ ∀ z, z ∈ L.lattice ↔ ∃ a ∈ (𝔞 : Ideal (𝓞 K)), z = c * σ (a : K) := by
    rintro ⟨_, L, hL, rfl⟩
    obtain ⟨𝔞, c, h𝔞, hc, h⟩ := CMLattice.exists_ideal σ hσ L hL
    exact ⟨⟨𝔞, mem_nonZeroDivisors_of_ne_zero (by rwa [Ideal.zero_eq_bot])⟩, L, c, hc, rfl, h⟩
  choose f L c hc hLj hL using key
  have inj : Function.Injective (fun j : S => ClassGroup.mk0 (f j)) := by
    intro j j' hjj
    apply Subtype.ext
    rw [← hLj j, ← hLj j']
    exact latticeJ_eq_of_class_eq σ (hc j') (hc j) (hL j') (hL j) hjj.symm
  have : Finite S := Finite.of_injective _ inj
  exact Set.toFinite S
end GlobalTheory.CMCurves
