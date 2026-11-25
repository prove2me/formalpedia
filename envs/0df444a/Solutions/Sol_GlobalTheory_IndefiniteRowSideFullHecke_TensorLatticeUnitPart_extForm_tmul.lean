-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart.extForm_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:08.076874+00:00
-- url     : https://prove2.me/submissions/007eaff9-be0c-42ec-8bae-7c1987a76a88

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TensorLatticeUnitPart_extBil_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
theorem _root_.solution (b : M →ₗ[O] M' →ₗ[O] O) (r r' : R) (x : M) (y : M') :
    extForm R b (r ⊗ₜ[O] x) (r' ⊗ₜ[O] y) = b x y • (r * r') := by
  simp [extForm, extBil_tmul]
end GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
