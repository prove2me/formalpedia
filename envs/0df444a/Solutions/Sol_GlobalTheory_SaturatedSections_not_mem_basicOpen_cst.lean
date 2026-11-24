-- Prove2me | solution 1 for GlobalTheory.SaturatedSections.not_mem_basicOpen_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:33:00.427087+00:00
-- url     : https://prove2.me/submissions/f701467f-a037-4bb5-bd27-267b9628c8d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueCombOfIndependentSpecialFibre
import Theorems.Thm_GlobalTheory_SaturatedSections_cst_eq

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
open GlobalTheory GlobalTheory.SaturatedSections
namespace GlobalTheory.SaturatedSections
theorem _root_.solution {W : Type} [CommRing W] [IsLocalRing W] {H : Scheme.{0}}
    (p : H ⟶ Sp W) (V : H.Opens) {r : W} (hr : r ∈ IsLocalRing.maximalIdeal W) (x : H)
    (hx : p x = IsLocalRing.closedPoint W) : x ∉ H.basicOpen (cst p V r) := by
  rw [← cst_eq, Out.resTop, Scheme.basicOpen_res, Out.scal, ← Scheme.preimage_basicOpen_top,
    basicOpen_eq_of_affine]
  rintro ⟨-, h⟩
  have h' : p x ∈ PrimeSpectrum.basicOpen r := h
  rw [hx] at h'
  exact h' hr
end GlobalTheory.SaturatedSections
