-- Prove2me | solution 1 for GlobalTheory.PowMulMemOrder.exists_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:59.131998+00:00
-- url     : https://prove2.me/submissions/7bea4b44-a2ff-404d-a5cd-f623cb66b20f

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisFurther
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.PowMulMemOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.PowMulMemOrder
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨⟨m, hm0⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) c hc
  have hmne : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hmne hϖ
  obtain ⟨u, hu⟩ := hk
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 : IsIntegral 𝒪[F] ((u : 𝒪[F]) • ((⟨m, hm0⟩ : nonZeroDivisors 𝒪[F]) • c)) := hm.smul _
  convert h2 using 1
  simp only [Submonoid.smul_def, smul_smul, ← hu]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]
  rw [mul_comm (u : 𝒪[F]) m, hu]
  rfl
end GlobalTheory.PowMulMemOrder
