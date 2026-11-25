-- Prove2me | solution 1 for GlobalTheory.TateDecomp.isCompact_intC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:05:47.274354+00:00
-- url     : https://prove2.me/submissions/1374cf0c-dc4d-4255-98f6-99d3e69423a5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_norm_io

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
theorem _root_.solution (F : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] F] :
    IsCompact (intC F) := by
  let M : Submodule ℚ_[l] (Om l) := Subalgebra.toSubmodule F.toSubalgebra
  haveI : FiniteDimensional ℚ_[l] M := ‹FiniteDimensional ℚ_[l] F›
  haveI : ProperSpace M := FiniteDimensional.proper ℚ_[l] M
  have hc : Continuous fun x : M => ((x : Om l) : PadicComplex l) :=
    (UniformSpace.Completion.continuous_coe _).comp continuous_subtype_val
  have : intC F = (fun x : M => ((x : Om l) : PadicComplex l)) '' Metric.closedBall 0 1 := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact (norm_io x).symm.le.trans h
    · rintro ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff] at hx
      exact ⟨⟨x, x.2, rfl⟩, (norm_io (x : Om l)).le.trans hx⟩
  rw [this]
  exact (isCompact_closedBall _ _).image hc
end GlobalTheory.TateDecomp
