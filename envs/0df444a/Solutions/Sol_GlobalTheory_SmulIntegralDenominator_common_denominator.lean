-- Prove2me | solution 1 for GlobalTheory.SmulIntegralDenominator.common_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:03.917044+00:00
-- url     : https://prove2.me/submissions/8408a3cd-e1e7-4f73-99dc-cacf6ad2d358

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsSmulIntegral
import Theorems.Thm_GlobalTheory_SmulIntegralDenominator_exists_smul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory GlobalTheory.SmulIntegralDenominator
namespace GlobalTheory.SmulIntegralDenominator
theorem _root_.solution {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R] (L : Formalism.MainNotions.S.Loc.LocE K R)
    {ι : Type} [Fintype ι] (f : ι → R) :
    ∃ e ∈ Valuation.integer (ValuativeRel.valuation K), e ≠ (0 : K) ∧
      ∀ i : ι, ∃ o ∈ L.O, f i = algebraMap K R e⁻¹ * o := by
  classical
  haveI : Module.Finite K R := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  choose e he0 he using fun i => exists_smul_integral (K := K) (f i)
  have hP : (∏ i, e i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => he0 i
  have hP' : ((∏ i, e i : 𝒪[K]) : K) ≠ 0 := fun h => hP (Subtype.ext h)
  refine ⟨((∏ i, e i : 𝒪[K]) : K), (∏ i, e i).2, hP', fun i => ?_⟩
  refine ⟨(∏ i, e i) • f i, ?_, ?_⟩
  · rw [L.O_def, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
    exact (he i).smul _
  · rw [Subring.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hP', map_one,
      one_mul]
end GlobalTheory.SmulIntegralDenominator
