-- Prove2me | solution 1 for GlobalTheory.LGrp.HasValueAt.multiset_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:56:22.561861+00:00
-- url     : https://prove2.me/submissions/963d1e15-f795-4928-a25f-ac357166daad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open Polynomial
namespace GlobalTheory.LGrp
namespace HasValueAt
theorem _root_.solution {ι : Type} (S : Multiset ι) {R : ι → RatFunc ℂ} {x : ℂ} {v : ι → ℂ}
    (h : ∀ i ∈ S, HasValueAt (R i) x (v i)) : HasValueAt (S.map R).prod x (S.map v).prod := by
  induction S using Multiset.induction_on with
  | empty => simpa using hasValueAt_one x
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))
end HasValueAt
end GlobalTheory.LGrp
