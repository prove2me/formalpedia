-- Prove2me | solution 1 for GlobalTheory.DRFil.eq_sum_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:03.233195+00:00
-- url     : https://prove2.me/submissions/665346e9-11f6-41be-9813-f8c25339d3d1

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
theorem _root_.solution {ι : Type} [Fintype ι] (bV : Basis ι LL V) (x : V ⊗[Qp] F) :
    x = ∑ i, sm Qp F LL V (ext Qp F (bV.coord i) x) (bV i ⊗ₜ[Qp] (1 : F)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | tmul v b =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, sm_tmul, mul_one,
      Basis.coord_apply, ← TensorProduct.sum_tmul]
    rw [bV.sum_repr]
end GlobalTheory.DRFil
