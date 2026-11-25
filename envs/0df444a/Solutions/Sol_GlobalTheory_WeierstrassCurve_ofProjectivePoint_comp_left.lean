-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.ofProjectivePoint_comp_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:58:53.556781+00:00
-- url     : https://prove2.me/submissions/cc901494-c89e-42aa-a328-d9cfadf8fd01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


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
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K]
variable {k K}
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (f : k →ₐ[R] K) {P : Fin 3 → k}
    (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P))
    (h' : (W.baseChange K).toProjective.NonsingularLift (Quotient.mk _ (f ∘ P))) :
    (ofProjectivePoint W K ⟨h'⟩).left =
      Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (ofProjectivePoint W k ⟨h⟩).left :=
  (SpecMap_pt W P (.of_nonsingular h) f).symm
end GlobalTheory.WeierstrassCurve
