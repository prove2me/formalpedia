-- Prove2me | solution 1 for GlobalTheory.MulFinite.pow_aux
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:46.808038+00:00
-- url     : https://prove2.me/submissions/b60a9bb3-89a1-48b9-8234-1b5bead589ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial
namespace GlobalTheory.MulFinite
theorem _root_.solution {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e N : ℕ) :
    ((g ^ N).val * x) ^ e * ((g ^ e * t)⁻¹).val ^ N = x ^ e * (t⁻¹).val ^ N := by
  have h : ((g ^ N) ^ e * ((g ^ e * t)⁻¹) ^ N) = (t⁻¹) ^ N := by
    rw [mul_inv, mul_pow, ← _root_.mul_assoc, inv_pow, ← pow_mul, ← pow_mul, _root_.mul_comm e N,
      mul_inv_cancel, _root_.one_mul]
  have h' : (g ^ N).val ^ e * ((g ^ e * t)⁻¹).val ^ N = (t⁻¹).val ^ N := congrArg Units.val h
  rw [mul_pow, ← h']; ring
end GlobalTheory.MulFinite
