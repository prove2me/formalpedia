-- Prove2me | solution 1 for GlobalTheory.FibrePowerProper.isProper_prod_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:51.261296+00:00
-- url     : https://prove2.me/submissions/63808d88-cfe1-4d41-9f7a-04e4a5c6f4ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibrePowerProper
namespace GlobalTheory.FibrePowerProper
theorem _root_.solution {T : Scheme.{0}} (X Y : Over T) (hX : IsProper X.hom)
    (hY : IsProper Y.hom) : IsProper (X ⨯ Y).hom := by
  have h1 : (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫ pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Over.w (prod.fst : X ⨯ Y ⟶ X)).symm
  have hfst : IsProper (pullback.fst X.hom Y.hom) := by haveI := hY; infer_instance
  rw [h1]
  infer_instance
end GlobalTheory.FibrePowerProper
