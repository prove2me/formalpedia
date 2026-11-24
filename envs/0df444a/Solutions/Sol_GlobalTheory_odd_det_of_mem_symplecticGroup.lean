-- Prove2me | solution 1 for GlobalTheory.odd_det_of_mem_symplecticGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:18.752716+00:00
-- url     : https://prove2.me/submissions/c5f53e36-cc30-4adc-86c6-8a4cd59e45bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_symplectic_fromBlocks_relations
import Theorems.Thm_GlobalTheory_fromBlocks_map_intCast_mem_symplecticGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}
namespace GlobalTheory
theorem _root_.solution (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ)
    (hb : ∀ i j, 2 ∣ b i j) : Odd d.det := by
  have h2 := (symplectic_fromBlocks_relations
    (fromBlocks_map_intCast_mem_symplecticGroup (ZMod 2) h)).2.1
  have hb0 : b.map ((↑) : ℤ → ZMod 2) = 0 := by
    ext i j
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (hb i j)
  rw [hb0, Matrix.mul_zero, sub_zero] at h2
  have h3 := (isUnit_det_of_left_inverse h2).ne_zero
  rw [← Int.cast_det, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  exact h3
end GlobalTheory
