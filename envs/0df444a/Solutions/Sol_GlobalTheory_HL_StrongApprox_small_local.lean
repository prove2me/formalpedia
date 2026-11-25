-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.small_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:42:51.985712+00:00
-- url     : https://prove2.me/submissions/b2325d2c-ca53-4575-9d42-d947560a0f38

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_int_of
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (T : LocAt F E sig p) (w : T.Fp) (hw : w ≠ 0) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a)) ≤ valuation T.Fp w := by
  haveI := T.lf
  have hw0 : valuation T.Fp w ≠ 0 := by simpa using hw
  have hn : {z : T.Fp | valuation T.Fp (z - w) < valuation T.Fp w} ∈ nhds w :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hw0, fun z hz => hz⟩
  obtain ⟨k, hk⟩ := T.dense.mem_nhds hn
  have hk' : valuation T.Fp (T.ιF k - w) < valuation T.Fp w := hk
  have hkv : valuation T.Fp (T.ιF k) = valuation T.Fp w := by
    have e : T.ιF k = w + (T.ιF k - w) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ hk']
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) k
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap (𝓞 F) F s ≠ 0 := by simpa using hs0
  refine ⟨a, fun ha => ?_, ?_⟩
  · rw [ha, map_zero, zero_div, map_zero, map_zero] at hkv
    exact hw0 hkv.symm
  · have e : T.ιF (algebraMap (𝓞 F) F a) =
        T.ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F s) * T.ιF (algebraMap (𝓞 F) F s) := by
      rw [← map_mul, div_mul_cancel₀ _ hsK]
    rw [e, Valuation.map_mul, hkv]
    exact mul_le_of_le_one_right' (int_of T s)
end GlobalTheory.HL.StrongApprox
