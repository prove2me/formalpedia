-- Prove2me | solution 1 for GlobalTheory.DefectSumCompare.finrank_mul_defectAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:55:46.382875+00:00
-- url     : https://prove2.me/submissions/fa905fef-eaa3-4a89-9c24-8bdcb273e646

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
import Theorems.Thm_GlobalTheory_DefectSumCompare_ord_vw_eq_vla
import Theorems.Thm_GlobalTheory_DefectSumCompare_vla_pow
import Theorems.Thm_GlobalTheory_DefectSumCompare_vla_discAt
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConjugateDefects_span_natCast_ne_bot


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
    (Module.finrank ℚ E : ℝ) * defectAt_vw σ n' a la =
      beOf E ((n' : ℕ) ^ Module.finrank ℚ E) a la := by
  have h : mOf E ((n' : ℕ) ^ Module.finrank ℚ E) la = Module.finrank ℚ E *
      max (ord_vw la (conjDifferent σ)) (ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)})) := by
    unfold mOf
    rw [vla_discAt σ, Nat.cast_pow, ← Ideal.span_singleton_pow, vla_pow la (span_natCast_ne_bot n'),
      ord_vw_eq_vla la (span_natCast_ne_bot n'), Nat.mul_max_mul_left]
  unfold beOf defectAt_vw
  rw [h]
  push_cast
  ring
end GlobalTheory.DefectSumCompare
