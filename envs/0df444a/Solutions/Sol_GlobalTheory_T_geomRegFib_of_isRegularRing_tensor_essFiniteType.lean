-- Prove2me | solution 1 for GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:19.348127+00:00
-- url     : https://prove2.me/submissions/e972116d-7b20-4a60-8afb-f4d5e95a121b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeomRegFibOfIsRegularRingTensorEssFiniteType
import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeomRegFibOfIsRegularRingTensorEssFiniteTypeStatement
import Theorems.Thm_GlobalTheory_geomRegFib_of_isRegularRing_essFiniteType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) → FinalTheorems.GeomRegFib R B := by
  first | exact @GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | exact GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | (intros; apply GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType <;> assumption)
end _root_.GlobalTheory.T
