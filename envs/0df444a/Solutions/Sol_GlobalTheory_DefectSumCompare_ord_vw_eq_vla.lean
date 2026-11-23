-- Prove2me | solution 1 for GlobalTheory.DefectSumCompare.ord_vw_eq_vla
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:17.080207+00:00
-- url     : https://prove2.me/submissions/c85508e2-1e2c-46cc-a753-efbd8b48f2a2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound

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
namespace GlobalTheory.DefectSumCompare
theorem _root_.solution {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ord_vw la I = vla la I := by
  classical
  unfold ord_vw vla
  rw [Ideal.count_associates_factors_eq hI la.isPrime la.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]
end GlobalTheory.DefectSumCompare
