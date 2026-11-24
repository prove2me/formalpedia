-- Prove2me | solution 1 for GlobalTheory.SS.PowCmp.not_isUnit_cstR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:04.693348+00:00
-- url     : https://prove2.me/submissions/68986cd4-288d-4030-b016-b6239643503e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PowCmp
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
namespace GlobalTheory.SS.PowCmp
theorem _root_.solution [IsLocalRing R] (M : Model R A) (U : M.Y.left.Opens) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty)
    {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit (cstR M U π) := by
  intro hu
  obtain ⟨y, hy, hs⟩ := h
  have h1 : M.Y.left.basicOpen (cstR M U π) = U := M.Y.left.basicOpen_of_isUnit hu
  have h2 : M.Y.left.basicOpen (cstR M U π) = U ⊓ M.Y.hom ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π) :=
    Scheme.basicOpen_appLE M.Y.hom U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
  rw [h1, basicOpen_eq_of_affine (R := CommRingCat.of R) π] at h2
  have h4 := (h2.le hy).2
  have h6 : M.Y.hom y = IsLocalRing.closedPoint R := hs
  have h7 : π ∉ PrimeSpectrum.asIdeal (M.Y.hom y) := h4
  rw [h6] at h7
  exact h7 hπ
end GlobalTheory.SS.PowCmp
