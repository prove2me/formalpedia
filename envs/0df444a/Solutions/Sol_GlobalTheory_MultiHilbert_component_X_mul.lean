-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.component_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:50.694752+00:00
-- url     : https://prove2.me/submissions/42c17d7b-2082-4d50-90ac-ccb59553e8b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution (i : σ) (n : M) (G : MvPolynomial σ K) :
    weightedHomogeneousComponent w (n + w i) (X i * G) =
      X i * weightedHomogeneousComponent w n G := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_X_mul', coeff_X_mul',
    coeff_weightedHomogeneousComponent]
  by_cases hi : i ∈ d.support
  · have hd : d = (d - Finsupp.single i 1) + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
    have hw : Finsupp.weight w d = Finsupp.weight w (d - Finsupp.single i 1) + w i := by
      conv_lhs => rw [hd]
      rw [map_add, Finsupp.weight_single, one_smul]
    simp only [hi, if_true, hw, add_left_inj]
  · simp only [hi, if_false, ite_self]
end GlobalTheory.MultiHilbert
