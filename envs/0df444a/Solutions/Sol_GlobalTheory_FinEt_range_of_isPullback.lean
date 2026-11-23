-- Prove2me | solution 1 for GlobalTheory.FinEt.range_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:11.414997+00:00
-- url     : https://prove2.me/submissions/0b7bd95a-ac4b-44b5-854a-171e5405de8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
namespace GlobalTheory.FinEt
theorem _root_.solution {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]
end GlobalTheory.FinEt
