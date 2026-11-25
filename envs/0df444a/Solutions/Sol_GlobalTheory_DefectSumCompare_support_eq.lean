-- Prove2me | solution 1 for GlobalTheory.DefectSumCompare.support_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:27.18741+00:00
-- url     : https://prove2.me/submissions/09bec8bf-32be-4b16-b10f-3f36d9e5259f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
import Theorems.Thm_GlobalTheory_DefectSumCompare_finrank_mul_defect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open GlobalTheory GlobalTheory.DefectSumCompare
variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]
namespace GlobalTheory.DefectSumCompare
theorem _root_.solution (hσ : Nonempty (E →+* K)) (n' : ℕ+) (a : ℕ) :
    Function.support (defect_vw E (K := K) n' a) =
      Function.support (beOf E (K := K) ((n' : ℕ) ^ Module.finrank ℚ E) a) := by
  ext la
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp only [Function.mem_support, ← finrank_mul_defect hσ, ne_eq, mul_eq_zero, hn, false_or,
    Nat.cast_eq_zero]
end GlobalTheory.DefectSumCompare
