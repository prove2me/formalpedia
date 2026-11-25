-- Prove2me | solution 1 for GlobalTheory.LGrp.hasSatake_GL_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:49.492999+00:00
-- url     : https://prove2.me/submissions/f5d9bcc5-9999-4b8e-aafe-f94e0bad10ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Theorems.Thm_GlobalTheory_LGrp_mem_fixed
import Theorems.Thm_GlobalTheory_LGrp_charRep_irreducible
import Theorems.Thm_GlobalTheory_LGrp_unrTorus_apply
import Theorems.Thm_GlobalTheory_LGrp_unrChar_isUnram
import Theorems.Thm_GlobalTheory_LGrp_isSubquot_char_of_top
import Theorems.Thm_GlobalTheory_LGrp_isSmooth_unram_det
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory Matrix
open scoped NNReal TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open GlobalTheory.PRep
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LGrp
theorem _root_.solution (z : ℂˣ) :
    HasSatakeGL (charRep ((unrChar (vZ k) z).comp (Matrix.GeneralLinearGroup.det (n := Fin 1)))) {z} := by
  have hs := isSmooth_unram_det (n := Fin 1) (unrChar_isUnram (k := k) z)
  refine ⟨⟨fun _ => z, by simp, ⟨hs, charRep_irreducible _⟩, isSubquot_char_of_top _ ?_ _ _ ?_ ?_ hs⟩, ?_⟩
  · refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨h, e⟩ := (LeviDatum.mem_U _).1 hg
    refine Subgroup.mem_bot.2 (Units.ext (Matrix.ext fun i j => ?_))
    obtain rfl : i = j := Subsingleton.elim _ _
    exact (congrArg (fun t : Fin 1 → kˣ => (t i : k)) e).trans (by simp)
  · intro g i j h
    exact absurd h (by rw [Subsingleton.elim i j]; exact lt_irrefl _)
  · intro q
    rw [unrTorus_apply, Fin.prod_univ_one, MonoidHom.comp_apply]
    congr 1
    exact Units.ext (Matrix.det_fin_one _)
  · intro h
    have : (1 : ℂ) ∈ fixed (charRep ((unrChar (vZ k) z).comp (Matrix.GeneralLinearGroup.det (n := Fin 1))))
        (SplitWeil.KO k (Fin 1)) := by
      rw [mem_fixed]
      rintro _ ⟨g, rfl⟩
      rw [charRep_apply, MonoidHom.comp_apply, unrChar_isUnram z _ ?_]
      · simp
      · have := (Valuation.integer.integers (valuation k)).valuation_unit (Matrix.GeneralLinearGroup.det g)
        simpa [Matrix.det_fin_one] using this
    rw [h] at this
    simp at this
end GlobalTheory.LGrp
