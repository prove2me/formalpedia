-- Prove2me | solution 1 for GlobalTheory.HL.GlueInt.fix_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:14.732289+00:00
-- url     : https://prove2.me/submissions/dba3a009-f0c3-4c54-9d19-0b6cb311ab82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfIntegralAllQuadraticCompletions
import Theorems.Thm_GlobalTheory_HL_GlueInt_sig_ne_id
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlueInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.GlueInt
theorem _root_.solution (A : Places F E sig) (s : E) (hs : sig s = s) : ∃ t : F, algebraMap F E t = s := by
  by_contra hno
  push_neg at hno
  apply sig_ne_id A
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp at hab
      exact ⟨hab, rfl⟩
    · exfalso
      have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
      have hab' : algebraMap F E a + algebraMap F E b * s = 0 := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hab; exact hab
      apply hno (-a / b)
      rw [map_div₀, map_neg, div_eq_iff hb']
      linear_combination (-1 : E) * hab'
  have hspan : Submodule.span F (Set.range ![(1 : E), s]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, A.quad]
    simp
  have hid : sig.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range hspan fun i => by
      fin_cases i <;> simp [hs]
  exact fun y => LinearMap.congr_fun hid y
end GlobalTheory.HL.GlueInt
