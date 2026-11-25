-- Prove2me | solution 1 for GlobalTheory.SW.EisTrans.exists_mem_HnGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:45.274539+00:00
-- url     : https://prove2.me/submissions/a870228d-b671-4106-ac00-9cc2fb114c3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Theorems.Thm_GlobalTheory_PosSemidefShiftByScalar_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisTrans
variable {N : ℕ}
namespace GlobalTheory.SW.EisTrans
theorem _root_.solution {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {Z : CM Ψ N N}
    (hZ : Z ∈ Hn Ψ N) : ∃ δ : ℝ, 0 < δ ∧ Z ∈ HnGe Ψ N δ := by
  first
  | exact @_root_.GlobalTheory.PosSemidefShiftByScalar.main
  | exact _root_.GlobalTheory.PosSemidefShiftByScalar.main
  | (apply _root_.GlobalTheory.PosSemidefShiftByScalar.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PosSemidefShiftByScalar.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PosSemidefShiftByScalar.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PosSemidefShiftByScalar.main ..)
end GlobalTheory.SW.EisTrans
