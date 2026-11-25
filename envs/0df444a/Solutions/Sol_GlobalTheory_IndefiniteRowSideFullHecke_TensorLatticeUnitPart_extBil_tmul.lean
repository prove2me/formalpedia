-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart.extBil_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:30.888054+00:00
-- url     : https://prove2.me/submissions/f46c674d-8860-4cbc-b3ae-129002b6e531

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart

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
theorem _root_.solution (b : M →ₗ[O] M' →ₗ[O] M'') (r r' : R) (x : M) (y : M') :
    extBil R b (r ⊗ₜ[O] x) (r' ⊗ₜ[O] y) = (r * r') ⊗ₜ[O] b x y := by
  simp [extBil]
end GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
