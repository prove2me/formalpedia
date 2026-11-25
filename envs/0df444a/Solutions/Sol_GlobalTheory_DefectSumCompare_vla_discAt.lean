-- Prove2me | solution 1 for GlobalTheory.DefectSumCompare.vla_discAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:49:25.855145+00:00
-- url     : https://prove2.me/submissions/77626923-4ed8-4d8e-a8c2-95e7f9f98a80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
import Theorems.Thm_GlobalTheory_DefectSumCompare_ord_vw_eq_vla
import Theorems.Thm_GlobalTheory_DefectSumCompare_conjDifferent_pow
import Theorems.Thm_GlobalTheory_DefectSumCompare_vla_pow
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConjugateDefects_conjDifferent_ne_bot


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
theorem _root_.solution (σ : E →+* K) (la : HeightOneSpectrum (𝓞 K)) :
    vla la (discAt E K) = Module.finrank ℚ E * ord_vw la (conjDifferent σ) := by
  rw [← conjDifferent_pow σ, vla_pow la (conjDifferent_ne_bot σ), ord_vw_eq_vla la (conjDifferent_ne_bot σ)]
end GlobalTheory.DefectSumCompare
