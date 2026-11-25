-- Prove2me | solution 1 for GlobalTheory.DefectSumCompare.defect_vw_eq_defectAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:07:16.102531+00:00
-- url     : https://prove2.me/submissions/5b295dbb-3a7d-4b78-bef0-9bf9e1578d74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
import Theorems.Thm_GlobalTheory_DefectSumCompare_finrank_mul_defectAt
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConjugateDefects_defectAt_vw_le


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
theorem _root_.solution (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    defect_vw E n' a la = defectAt_vw σ n' a la := by
  refine le_antisymm (Finset.sup_le fun τ _ => le_of_eq ?_) (defectAt_vw_le σ n' a la)
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have := (finrank_mul_defectAt τ n' a la).trans (finrank_mul_defectAt σ n' a la).symm
  exact_mod_cast mul_left_cancel₀ hn this
end GlobalTheory.DefectSumCompare
