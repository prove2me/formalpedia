-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.tensorBasisMap_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:15:48.521455+00:00
-- url     : https://prove2.me/submissions/c5069e1f-656d-4040-b917-6d3c674fac01

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_IsQuasicoherentTensorOfInvertible
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorBasisMap_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_resM
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_resM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
universe u
noncomputable section
variable {X : Scheme.{u}}
variable {M M' L : X.Modules} {U V : X.Opens} {s : ((preMod X).obj L).obj (op U)}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (h : V ≤ U) {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, V)) :
    resF (M ⊗ L) hWV (tensorBasisMap M L s h m) =
      tensorBasisMap M L s (hWV.trans h) (resF M hWV m) := by
  rw [tensorBasisMap_apply, tensorBasisMap_apply]
  have := (app_resM (tensorToSheaf M L) hWV
    ((show ((preMod X).obj M).obj (op V) from m) ⊗ₜ resM ((preMod X).obj L) h s :
      ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V))).symm
  refine this.trans ?_
  congr 1
  change resM _ hWV m ⊗ₜ resM _ hWV (resM _ h s) = _
  rw [resM_resM]
  rfl
end GroundTheory.Arith.SchemeCoh
