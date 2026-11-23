-- Prove2me | solution 1 for GlobalTheory.DRFil.exists_smul_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:32.967888+00:00
-- url     : https://prove2.me/submissions/3dbb9e95-3ac5-4121-b8ed-afa2ccf96fc6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_tmul_mul_idem

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
theorem _root_.solution (τ : K →ₐ[Qp] LL) (n : ℕ) (a : Fin n → LL) (c : Fin n → K) :
    idem F τ * ∑ i, a i ⊗ₜ[Qp] algebraMap K F (c i) = (∑ i, a i * τ (c i)) • idem F τ := by
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : a i ⊗ₜ[Qp] algebraMap K F (c i) = a i • ((1 : LL) ⊗ₜ[Qp] algebraMap K F (c i)) := by
    simp [TensorProduct.smul_tmul']
  rw [this, mul_smul_comm, mul_comm, tmul_mul_idem, smul_smul]
end GlobalTheory.DRFil
