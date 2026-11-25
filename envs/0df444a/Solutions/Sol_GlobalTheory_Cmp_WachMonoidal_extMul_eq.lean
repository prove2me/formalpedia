-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.extMul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:34:17.5905+00:00
-- url     : https://prove2.me/submissions/48abd08c-415b-4738-93df-9355b727dfd1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TensorLatticeUnitPart_extBil_tmul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitDualParts_extMul_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']
namespace GlobalTheory.Cmp.WachMonoidal
theorem _root_.solution (b : M →ₗ[O] M' →ₗ[O] M'') (u : R ⊗[O] M) (w : R ⊗[O] M') :
    UnitDualParts.extMul R (TensorProduct.lift b) u w = TensorLatticeUnitPart.extBil R b u w := by
  induction u using TensorProduct.induction_on with
  | zero => simp [UnitDualParts.extMul, TensorLatticeUnitPart.extBil]
  | add x y hx hy =>
    simp only [UnitDualParts.extMul, TensorLatticeUnitPart.extBil, add_tmul, map_add] at hx hy ⊢
    rw [hx, hy]
  | tmul r a =>
    induction w using TensorProduct.induction_on with
    | zero => simp [UnitDualParts.extMul, TensorLatticeUnitPart.extBil]
    | add x y hx hy =>
      simp only [UnitDualParts.extMul, TensorLatticeUnitPart.extBil, tmul_add, map_add] at hx hy ⊢
      rw [hx, hy]
    | tmul r' a' => rw [UnitDualParts.extMul_tmul, TensorLatticeUnitPart.extBil_tmul, TensorProduct.lift.tmul]
end GlobalTheory.Cmp.WachMonoidal
