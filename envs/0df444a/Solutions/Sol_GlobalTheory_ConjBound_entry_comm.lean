-- Prove2me | solution 1 for GlobalTheory.ConjBound.entry_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:02.651805+00:00
-- url     : https://prove2.me/submissions/654838d4-609c-4b92-8d05-0cb986ae11a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImAdjointOfSpan
import Theorems.Thm_GlobalTheory_ConjBound_hermForm_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ConjBound
open GlobalTheory.EigenNorm
variable {g : ℕ}
namespace GlobalTheory.ConjBound
theorem _root_.solution (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ)
    (h : ∀ z w, (hermForm Hm (t * z) w).im = (hermForm Hm z (star t * w)).im) (i j : Fin g) :
    t i * Hm i j = Hm i j * t j := by
  have key : ∀ s : ℂ, (s * (t i * Hm i j)).im = (s * (Hm i j * t j)).im := fun s => by
    have := h (Pi.single i s) (Pi.single j 1)
    rw [hermForm_eq_sum, hermForm_eq_sum] at this
    simp only [Pi.mul_apply, Pi.single_apply, Pi.star_apply, mul_ite, mul_zero, _root_.mul_one, ite_mul, zero_mul,
      apply_ite (starRingEnd ℂ), map_zero, map_one, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RCLike.star_def, Complex.conj_conj] at this
    convert this using 2 <;> ring
  have h1 := key 1
  have h2 := key Complex.I
  rw [_root_.one_mul, _root_.one_mul] at h1
  rw [Complex.I_mul_im, Complex.I_mul_im] at h2
  exact Complex.ext h2 h1
end GlobalTheory.ConjBound
