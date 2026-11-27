-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.hom_schemeOver_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:52.843993+00:00
-- url     : https://prove2.me/submissions/9eab0a25-7907-431d-9c8a-ece862c79d70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_over_hom_eq_iff_forall_field_algebra

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
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {T : Over (Spec (.of R))} [IsReduced T.left]
    {f g : T ⟶ schemeOver W} :
    f = g ↔ ∀ (k : Type u) [Field k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g :=
  have : IsSeparated (schemeOver W).hom := inferInstanceAs (IsSeparated (toSpec W))
  over_hom_eq_iff_forall_field_algebra
end GlobalTheory.WeierstrassCurve
