-- Prove2me | solution 1 for GlobalTheory.IdealResProd.mem_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:45:50.170922+00:00
-- url     : https://prove2.me/submissions/e7779cc9-0795-4b77-b6a1-e59168884ee5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsNormEqFinprod
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.IdealResProd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.IdealResProd
theorem _root_.solution (A : LocAt F E sig p) (L : LocE A.Fp A.Ep) {c : A.Fp} (hc : c ≠ 0) (x : A.Fp) :
    algebraMap A.Fp A.Ep x ∈ Submodule.span L.O {algebraMap A.Fp A.Ep c} ↔
      valuation A.Fp x ≤ valuation A.Fp c := by
  have hun : IsUnit (algebraMap A.Fp A.Ep c) := (IsUnit.mk0 _ hc).map _
  have hx : algebraMap A.Fp A.Ep x = algebraMap A.Fp A.Ep (x / c) * algebraMap A.Fp A.Ep c := by
    rw [← map_mul, div_mul_cancel₀ _ hc]
  have h1 : valuation A.Fp x ≤ valuation A.Fp c ↔ x / c ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hc))]
  rw [h1, ← GlobalTheory.UnramOrder.algebraMap_mem_iff L, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨o, ho⟩
    rw [hx] at ho
    have : (o : A.Ep) = algebraMap A.Fp A.Ep (x / c) := hun.mul_right_cancel ho
    rw [← this]; exact o.2
  · intro h
    exact ⟨⟨_, h⟩, hx.symm⟩
end GlobalTheory.IdealResProd
