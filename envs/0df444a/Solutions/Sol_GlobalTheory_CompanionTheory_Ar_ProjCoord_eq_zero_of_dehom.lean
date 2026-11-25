-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.eq_zero_of_dehom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:10.87784+00:00
-- url     : https://prove2.me/submissions/7ceabab2-50ae-483f-8602-1cbd78b87e85

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_aeval_mul_of_isHomogeneous

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
theorem _root_.solution [IsDomain o] {ι : Type} {n : ℕ} {g : MvPolynomial (Option ι) o}
    (hg : g.IsHomogeneous n)
    (h : aeval (fun j : Option ι => (j.elim 1 X : MvPolynomial ι o)) g = 0) : g = 0 := by
  let K := FractionRing (MvPolynomial (Option ι) o)
  let y : Option ι → K := fun j => algebraMap (MvPolynomial (Option ι) o) K (X j)
  have hy : y none ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2 (X_ne_zero _)
  have h1 := congrArg (aeval (R := o) fun j : ι => (y none)⁻¹ * y (some j)) h
  rw [map_zero, ← AlgHom.comp_apply, comp_aeval] at h1
  have h2 : (fun j : Option ι => aeval (R := o) (fun j : ι => (y none)⁻¹ * y (some j))
      (j.elim 1 X : MvPolynomial ι o)) = fun j => (y none)⁻¹ * y j := by
    funext j
    cases j with
    | none => exact (map_one _).trans (inv_mul_cancel₀ hy).symm
    | some j => simp
  rw [h2, aeval_mul_of_isHomogeneous y _ hg, mul_eq_zero, or_iff_right (pow_ne_zero _ (inv_ne_zero hy))] at h1
  have h3 := aeval_algebraMap_apply (R := o) K (fun j : Option ι => (X j : MvPolynomial (Option ι) o)) g
  rw [aeval_X_left_apply] at h3
  exact (map_eq_zero_iff _ (IsFractionRing.injective _ K)).1 (h3.symm.trans h1)
end GlobalTheory.CompanionTheory.Ar.ProjCoord
