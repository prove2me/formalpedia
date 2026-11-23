-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers.herm_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:57.842584+00:00
-- url     : https://prove2.me/submissions/f5aa158c-aeb4-4f6c-80d3-3f98b940f789

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HermitianTensorPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (v w : Fin g → ℂ) :
    herm Hm w v = starRingEnd ℂ (herm Hm v w) := by
  simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : starRingEnd ℂ (Hm a b) = Hm b a := h.apply b a
  rw [this]; ring
end GlobalTheory.IndefiniteRowSideFullHecke.HermitianTensorPowers
