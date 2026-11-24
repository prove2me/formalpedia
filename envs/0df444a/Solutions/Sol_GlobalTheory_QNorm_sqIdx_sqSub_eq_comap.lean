-- Prove2me | solution 1 for GlobalTheory.QNorm.sqIdx_sqSub_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:48.764888+00:00
-- url     : https://prove2.me/submissions/58793a5e-383d-4d26-a9f7-f58f25e08452

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexSquaresLeTwoMulOfSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexHigherUnitsSuccLeCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSquaresLeTwoMulUnitsSquaresStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLe
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_QNorm_mem_sqSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F L : Type} [Field F] [Field L] (φ : F →+* L) :
    sqSub φ = (sqs (⊤ : Subgroup Lˣ)).comap (Units.map (φ : F →* L)) := by
  ext x
  rw [mem_sqSub, Subgroup.mem_comap]
  constructor
  · rintro ⟨r, hr⟩
    have hx : φ (x : F) ≠ 0 := by simp
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hr)
    refine ⟨Units.mk0 r hr0, Subgroup.mem_top _, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨r, -, hr⟩
    refine ⟨(r : L), ?_⟩
    have := congrArg (fun u : Lˣ => (u : L)) hr
    simpa [sq] using this.symm
end GlobalTheory.QNorm
