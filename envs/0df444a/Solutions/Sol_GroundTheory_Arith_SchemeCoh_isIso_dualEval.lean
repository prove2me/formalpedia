-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isIso_dualEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:19:00.604664+00:00
-- url     : https://prove2.me/submissions/7629e501-53c4-4ba9-9cef-a11e14d5e619

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_refl
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_DualSec_dualBasis_app_self
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_DualSec_isBasisOn_dualBasis
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_of_alt
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_tmul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_W_tensorToSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_one
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isIso_of_isBasisOn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorToSheaf_tensorLift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {M : X.Modules} (hM : IsInvertibleSheaf M) : IsIso (dualEval M) := by
  apply isIso_of_isBasisOn
  intro x
  obtain ⟨U, hx, s, hs⟩ := hM x
  let t : ((preMod X).obj (dualSheaf M)).obj (op U) := (dualIsoHom M).app (op U) (DualSec.dualBasis hs)
  have ht : IsBasisOn ((preMod X).obj (dualSheaf M)) U t :=
    (DualSec.isBasisOn_dualBasis hs).map_of_alt (dualIsoHom M) (MorphismProperty.of_isIso _ _)
  let ts : ((preMod X).obj (dualSheaf M) ⊗ (preMod X).obj M).obj (op U) := t ⊗ₜ s
  refine ⟨U, hx, (tensorToSheaf (dualSheaf M) M).app (op U) ts,
    (ht.tmul hs).map_of_alt _ (W_tensorToSheaf _ M), ?_⟩
  have e1 : ((preMod X).map (dualEval M)).app (op U) ((tensorToSheaf (dualSheaf M) M).app (op U) ts) =
      ((tensorToSheaf (dualSheaf M) M ≫ (preMod X).map (dualEval M)).app (op U)) ts := rfl
  have e2 : (evalPre M).app (op U) ts = (DualSec.dualBasis hs).app U le_rfl s := rfl
  rw [e1, dualEval, tensorToSheaf_tensorLift, e2]
  have h1 := DualSec.dualBasis_app_self hs U le_rfl
  rw [resM_refl] at h1
  rw [h1]
  exact isBasisOn_one U
end GroundTheory.Arith.SchemeCoh
