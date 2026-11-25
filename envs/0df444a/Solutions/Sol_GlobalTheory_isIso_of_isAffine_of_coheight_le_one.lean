-- Prove2me | solution 1 for GlobalTheory.isIso_of_isAffine_of_coheight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:43:54.802677+00:00
-- url     : https://prove2.me/submissions/ad80c72a-6db2-477e-ad73-dd48b9bce8e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfIsAffineOpenOfRingKrullDimLeOne
import Theorems.Thm_GlobalTheory_bijective_app_of_coheight_le_one
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] [IsAffine X] [IsAffine Y] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) : IsIso f := by
  have h : IsIso (f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_of_coheight_le_one f hf ⊤)
  have : IsIso (Spec.map f.appTop) := inferInstance
  have e : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  rw [e]
  infer_instance
end GlobalTheory
