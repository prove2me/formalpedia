-- Prove2me | solution 1 for GlobalTheory.RowLev.intAdIncl_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:25.891663+00:00
-- url     : https://prove2.me/submissions/72a4b777-9f11-45f0-b2bb-da727c58bac4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
import Theorems.Thm_GlobalTheory_RowLev_intAdIncl_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.RowLev
theorem _root_.solution {x : intAd F} (hx : x ∈ Ideal.jacobson (⊥ : Ideal (intAd F))) :
    intAdIncl F E x ∈ Ideal.jacobson (⊥ : Ideal (IntAf F E)) := by
  unfold Ideal.jacobson at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  rintro M ⟨-, hM⟩
  have := hM
  exact hx _ ⟨bot_le, Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ intAdIncl_isIntegral M⟩
end GlobalTheory.RowLev
