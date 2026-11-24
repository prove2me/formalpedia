-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.isClosed_val_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:27.900266+00:00
-- url     : https://prove2.me/submissions/8f9d3e5c-d24e-426f-86ae-e669b20c2bec

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.IwContract
theorem _root_.solution (ϖ : Fˣ) (k : ℕ) :
    IsClosed {y : F | valuation F y ≤ valuation F (ϖ : F) ^ k} := by
  have hr : valuation F (ϖ : F) ^ k ≠ 0 := pow_ne_zero _ ((valuation F).ne_zero_iff.mpr ϖ.ne_zero)
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨Units.mk0 _ hr, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hz
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [(valuation F).map_add_eq_of_lt_left (hz.trans hx)]
  exact hx
end GlobalTheory.CompanionTheory.IwContract
