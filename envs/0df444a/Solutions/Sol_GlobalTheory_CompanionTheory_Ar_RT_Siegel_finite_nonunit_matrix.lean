-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.Siegel.finite_nonunit_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:35:28.292928+00:00
-- url     : https://prove2.me/submissions/da7bc2d5-c892-4b4a-add1-a529ba0f4569

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_Siegel_finite_nonunit
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_finite_nonunit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.SiegelChar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.Siegel
namespace GlobalTheory.CompanionTheory.Ar.RT.Siegel
theorem _root_.solution {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [IsArtinianRing E]
    {β : Type} [Fintype β] [DecidableEq β] (A B D : Matrix β β E) (τ : E) (h : IsUnit (A + τ • B + (τ * τ) • D)) :
    {t : F | ¬ IsUnit (A + algebraMap F E t • B + (algebraMap F E t * algebraMap F E t) • D)}.Finite := by
  have key : ∀ z : E, ((A.map Polynomial.C + (Polynomial.X : Polynomial E) • B.map Polynomial.C +
      ((Polynomial.X : Polynomial E) * Polynomial.X) • D.map Polynomial.C).det).eval z =
      (A + z • B + (z * z) • D).det := by
    intro z
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  simp only [Matrix.isUnit_iff_isUnit_det, ← key] at h ⊢
  exact finite_nonunit _ τ h
end GlobalTheory.CompanionTheory.Ar.RT.Siegel
