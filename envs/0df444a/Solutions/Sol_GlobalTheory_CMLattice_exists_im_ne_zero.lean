-- Prove2me | solution 1 for GlobalTheory.CMLattice.exists_im_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:36.001227+00:00
-- url     : https://prove2.me/submissions/acb17e19-bf4b-4407-be92-1407d5d5b201

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.CMLattice
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.CMLattice
theorem _root_.solution (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ a : 𝓞 K, (σ (a : K)).im ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hσ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have key : ∀ y : 𝓞 K, starRingEnd ℂ (σ (algebraMap (𝓞 K) K y)) = σ (algebraMap (𝓞 K) K y) :=
    fun y => Complex.conj_eq_iff_im.2 (hcon y)
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, map_div₀, map_div₀, key, key]
end GlobalTheory.CMLattice
