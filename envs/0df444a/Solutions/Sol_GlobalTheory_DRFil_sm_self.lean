-- Prove2me | solution 1 for GlobalTheory.DRFil.sm_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:52.12583+00:00
-- url     : https://prove2.me/submissions/592a590b-381a-4cd6-bf17-33ca50db39a7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {Qp : Type} [Field Qp] (F : Type) [CommRing F] [Algebra Qp F]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
variable {F}
namespace GlobalTheory.DRFil
theorem _root_.solution (r s : LL ⊗[Qp] F) : sm Qp F LL LL r s = r * s := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs, add_mul]
  | tmul c b =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add r s hr hs => simp only [map_add, hr, hs, mul_add]
    | tmul v b' => simp
end GlobalTheory.DRFil
