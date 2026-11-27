-- Prove2me | solution 1 for GlobalTheory.WeightScale.isUnimodularSol_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:36:42.241601+00:00
-- url     : https://prove2.me/submissions/07024a3f-be8d-4d03-bcf9-28d19ae690a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsUnimodularSolTriple
import Theorems.Thm_GlobalTheory_WeightScale_equation_triple
import Theorems.Thm_GlobalTheory_WeightScale_span_le_span_triple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.WeightScale
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GlobalTheory.WeightScale
theorem _root_.solution {u : A} (hu : IsUnit u) {V : WeierstrassCurve A}
    (hV : curve u V = V) {P : Fin 3 → A} (h : IsUnimodularSol V P) :
    IsUnimodularSol V (triple u P) :=
  ⟨hV ▸ equation_triple u h.equation,
    top_le_iff.mp (h.span_eq_top.ge.trans (span_le_span_triple hu P))⟩
end GlobalTheory.WeightScale
