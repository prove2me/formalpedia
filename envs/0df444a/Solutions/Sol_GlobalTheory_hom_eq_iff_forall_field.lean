-- Prove2me | solution 1 for GlobalTheory.hom_eq_iff_forall_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:36:59.612472+00:00
-- url     : https://prove2.me/submissions/f69de15d-b0b2-4a74-9d1b-ba6bc2fefb25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
variable {T Y S : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution [IsReduced T] (s : Y ⟶ S) [IsSeparated s] {f g : T ⟶ Y}
    (h : f ≫ s = g ≫ s) :
    f = g ↔ ∀ (k : Type u) [Field k] (x : Spec (.of k) ⟶ T), x ≫ f = x ≫ g :=
  ⟨fun e _ _ _ => e ▸ rfl, fun H => ext_of_fromSpecResidueField_eq f g s Set.univ dense_univ
    (fun x _ => H (T.residueField x) (T.fromSpecResidueField x)) h⟩
end GlobalTheory
