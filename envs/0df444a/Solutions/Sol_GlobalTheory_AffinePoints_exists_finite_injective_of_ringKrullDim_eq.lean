-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_finite_injective_of_ringKrullDim_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:30.968012+00:00
-- url     : https://prove2.me/submissions/fd5ea6cd-7a4f-426f-b624-f694cea9034d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution [Algebra.FiniteType K A]
    (hd : ringKrullDim A = d) :
    ∃ g : MvPolynomial (Fin d) K →ₐ[K] A, Function.Injective g ∧ g.Finite := by
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hd
    exact WithBot.bot_ne_natCast _ hd
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  letI := g.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
  rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) K) A,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at hd
  obtain rfl : s = d := by simpa using hd
  exact ⟨g, hg, hfin⟩
end GlobalTheory.AffinePoints
