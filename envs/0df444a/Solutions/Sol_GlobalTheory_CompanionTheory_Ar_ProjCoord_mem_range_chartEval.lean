-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.mem_range_chartEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:18.796472+00:00
-- url     : https://prove2.me/submissions/1cbc2562-2dd0-4cc2-80df-dbcd77e4fff9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_aeval_mul_of_isHomogeneous
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_chartEval_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (x : κ → Ω) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ (chartEval (o := o) x c hc).range ↔ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X_mem (o := o) c) z
    have ha' : a.IsHomogeneous n := by simpa using ha
    rw [chartEval_mk, Algebra.adjoin_range_eq_range_aeval]
    refine ⟨a, ?_⟩
    have := aeval_mul_of_isHomogeneous x (x c)⁻¹ ha'
    simp only [div_eq_inv_mul, ← inv_pow]
    exact this
  · intro h
    induction h using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact ⟨Away.mk _ (X_mem c) 1 (X j) (X_mem j), (chartEval_mk x c hc 1 _ _).trans (by simp)⟩
    | algebraMap r =>
      exact ⟨Away.mk _ (X_mem c) 0 (C r) (isHomogeneous_C κ r), (chartEval_mk x c hc 0 _ _).trans (by simp)⟩
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
end GlobalTheory.CompanionTheory.Ar.ProjCoord
