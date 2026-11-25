-- Prove2me | solution 1 for GlobalTheory.HL.isIntegral_of_forall_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:13.806075+00:00
-- url     : https://prove2.me/submissions/8dc6049f-cd21-4728-867f-a5eb65212969

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletions
import Theorems.Thm_GlobalTheory_HL_GlueInt_sig_sig
import Theorems.Thm_GlobalTheory_HL_GlueInt_fix_mem
import Theorems.Thm_GlobalTheory_HL_GlueInt_int_of_loc
import Theorems.Thm_GlobalTheory_HL_GlueInt_sig_mem
import Theorems.Thm_GlobalTheory_HL_GlueInt_isIntegral_of_quadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.GlueInt
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (y : E), (∀ p, (A.loc p).ιE y ∈ (A.L p).O) →
    IsIntegral ℤ y := by
  intro F E _ _ _ _ _ sig A y hy
  obtain ⟨a, ha⟩ := fix_mem A (y + sig y) (by rw [map_add, sig_sig A, add_comm])
  obtain ⟨b, hb⟩ := fix_mem A (y * sig y) (by rw [map_mul, sig_sig A, mul_comm])
  obtain ⟨a0, rfl⟩ := int_of_loc A a fun p => by
    rw [ha, map_add]; exact (A.L p).O.add_mem (hy p) (sig_mem A y p (hy p))
  obtain ⟨b0, rfl⟩ := int_of_loc A b fun p => by
    rw [hb, map_mul]; exact (A.L p).O.mul_mem (hy p) (sig_mem A y p (hy p))
  refine isIntegral_of_quadratic y _ _ ((RingOfIntegers.isIntegral_coe a0).map (algebraMap F E).toIntAlgHom)
    ((RingOfIntegers.isIntegral_coe b0).map (algebraMap F E).toIntAlgHom) ?_
  change y ^ 2 - algebraMap F E (algebraMap (𝓞 F) F a0) * y + algebraMap F E (algebraMap (𝓞 F) F b0) = 0
  rw [ha, hb]
  ring
end GlobalTheory.HL
