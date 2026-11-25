-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.extPair_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:49.209498+00:00
-- url     : https://prove2.me/submissions/357ca254-e096-46dc-ad7f-f6e556ec6b87

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal
import Theorems.Thm_GlobalTheory_Cmp_WachMonoidal_extMul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']
namespace GlobalTheory.Cmp.WachMonoidal
theorem _root_.solution (b : M →ₗ[O] M' →ₗ[O] O) (u : R ⊗[O] M) (w : R ⊗[O] M') :
    UnitDualParts.extPair R b u w = TensorLatticeUnitPart.extForm R b u w := by
  rw [UnitDualParts.extPair, TensorLatticeUnitPart.extForm, extMul_eq]
end GlobalTheory.Cmp.WachMonoidal
