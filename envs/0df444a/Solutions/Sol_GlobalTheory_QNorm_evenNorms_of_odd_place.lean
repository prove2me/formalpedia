-- Prove2me | solution 1 for GlobalTheory.QNorm.evenNorms_of_odd_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:58:49.119878+00:00
-- url     : https://prove2.me/submissions/634f22fb-ec39-4e4a-8ae2-28b9d5fb75c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenNormsOfUnitNonsquare
import Theorems.Thm_GlobalTheory_QNorm_evenNorms_of_unit_nonsquare
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Valued.v (2 : v.adicCompletion F) = 1 →
    ∀ δ : v.adicCompletion F, Valued.v δ = 1 → ¬ IsSquare δ → EvenNorms Valued.v δ := by
  intro F _ _ v h2 δ hδ hn
  refine evenNorms_of_unit_nonsquare _ (fun x hx => ?_) δ hδ hn
  apply GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v x
  have : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
  rw [this, map_mul, h2, one_mul]
  exact hx
end GlobalTheory.QNorm
