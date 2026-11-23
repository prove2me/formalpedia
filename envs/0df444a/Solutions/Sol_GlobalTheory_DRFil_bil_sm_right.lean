-- Prove2me | solution 1 for GlobalTheory.DRFil.bil_sm_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:04.139815+00:00
-- url     : https://prove2.me/submissions/65efe46e-c195-4680-a922-b334fbd79eba

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
theorem _root_.solution (β : V →ₗ[LL] V' →ₗ[LL] V'') (r : LL ⊗[Qp] F) (x : V ⊗[Qp] F) (y : V' ⊗[Qp] F) :
    bil Qp F β x (sm Qp F LL V' r y) = sm Qp F LL V'' r (bil Qp F β x y) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
    | tmul v b' =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add r s hr hs => simp only [map_add, hr, hs]
      | tmul w b'' => simp [mul_left_comm]
end GlobalTheory.DRFil
