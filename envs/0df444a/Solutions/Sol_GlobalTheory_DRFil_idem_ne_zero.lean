-- Prove2me | solution 1 for GlobalTheory.DRFil.idem_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:28.696689+00:00
-- url     : https://prove2.me/submissions/44ef2564-8475-44bd-855b-73cbc87aa432

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
variable {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL]
variable [FiniteDimensional Qp K] [CharZero Qp] (F : Type) [CommRing F] [Algebra Qp F] [Algebra K F]
  [IsScalarTower Qp K F]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
variable {F}
namespace GlobalTheory.DRFil
theorem _root_.solution [Nontrivial F] (τ : K →ₐ[Qp] LL) : idem F τ ≠ 0 := by
  intro h
  have hi : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := LL)
      (IsScalarTower.toAlgHom Qp K F).toLinearMap (algebraMap K F).injective
  have h0 : (exists_idem τ).choose = 0 := hi (by rw [map_zero]; exact h)
  have := (exists_idem τ).choose_spec.1
  rw [h0, map_zero] at this
  exact zero_ne_one this
end GlobalTheory.DRFil
