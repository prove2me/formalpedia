-- Prove2me | solution 1 for GlobalTheory.DRFil.sm_tmul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:35.801318+00:00
-- url     : https://prove2.me/submissions/a43b9708-d3c6-4bf9-823b-0ba50e65c1c4

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
theorem _root_.solution (c : LL) (b : F) (x : V ⊗[Qp] F) :
    sm Qp F LL V (c ⊗ₜ[Qp] b) x = c • mulR Qp F LL V b x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b' => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
end GlobalTheory.DRFil
