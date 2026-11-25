-- Prove2me | solution 1 for GlobalTheory.TateDecomp.finite_Ks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:09.898881+00:00
-- url     : https://prove2.me/submissions/abd290b8-4c62-4338-9e39-91530346e8ac

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution (K : FinExt l) (j : ℕ) : FiniteDimensional ℚ_[l] (Ks K j) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hf : {x : Om l | x ^ (l ^ j) = 1}.Finite := by
    refine (Polynomial.nthRootsFinset (l ^ j) (1 : Om l)).finite_toSet.subset fun x hx => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset
      (pow_pos (Fact.out : l.Prime).pos _) _).2 hx)
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ j) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _
end GlobalTheory.TateDecomp
