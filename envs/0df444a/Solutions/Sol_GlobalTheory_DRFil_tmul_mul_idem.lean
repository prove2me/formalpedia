-- Prove2me | solution 1 for GlobalTheory.DRFil.tmul_mul_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:29.262835+00:00
-- url     : https://prove2.me/submissions/957ccd2f-8829-4711-b764-50d40e01e75b

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
namespace GlobalTheory.DRFil
theorem _root_.solution (τ : K →ₐ[Qp] LL) (c : K) :
    ((1 : LL) ⊗ₜ[Qp] algebraMap K F c) * idem F τ = τ c • idem F τ := by
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F))
    ((exists_idem τ).choose_spec.2 c)
  rw [map_mul, Algebra.smul_def, map_mul] at h
  rw [Algebra.smul_def]
  simpa [idem] using h
end GlobalTheory.DRFil
