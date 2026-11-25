-- Prove2me | solution 1 for GlobalTheory.DefectSumCompare.finrank_mul_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:17:24.010951+00:00
-- url     : https://prove2.me/submissions/2ada2cf3-53b0-4d34-bd44-90f74e5f9a39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
import Theorems.Thm_GlobalTheory_DefectSumCompare_finrank_mul_defectAt
import Theorems.Thm_GlobalTheory_DefectSumCompare_defect_vw_eq_defectAt

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
theorem _root_.solution (hσ : Nonempty (E →+* K)) (n' : ℕ+) (a : ℕ)
    (la : HeightOneSpectrum (𝓞 K)) :
    (Module.finrank ℚ E : ℝ) * defect_vw E n' a la =
      beOf E ((n' : ℕ) ^ Module.finrank ℚ E) a la := by
  obtain ⟨σ⟩ := hσ
  rw [defect_vw_eq_defectAt σ, finrank_mul_defectAt]
end GlobalTheory.DefectSumCompare
