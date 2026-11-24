-- Prove2me | solution 1 for GlobalTheory.LevQuot.isOpenImmersion_graph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:43:52.786182+00:00
-- url     : https://prove2.me/submissions/9db2d819-0450-4f15-8432-bf2bf63b64b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}
namespace GlobalTheory.LevQuot
theorem _root_.solution (r : X ⟶ Y) [Etale r] (f : X ⟶ X) (h : 𝟙 X ≫ r = f ≫ r) :
    IsOpenImmersion (pullback.lift (𝟙 X) f h) := by
  have hpost : (@IsOpenImmersion : MorphismProperty Scheme.{0}).HasOfPostcompProperty
      (@Etale : MorphismProperty Scheme.{0}) := by
    refine MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr ?_
    intro A B u hu
    have : Etale u := hu
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal u))
  have hsec : IsOpenImmersion (pullback.lift (𝟙 X) f h ≫ pullback.fst r r) := by
    rw [pullback.lift_fst]
    infer_instance
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @Etale) _ (pullback.fst r r)
    (inferInstance : Etale (pullback.fst r r)) hsec
end GlobalTheory.LevQuot
