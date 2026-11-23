-- Prove2me | solution 1 for GlobalTheory.DRFil.mulR_sm_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:21.384815+00:00
-- url     : https://prove2.me/submissions/179215e5-55f5-445a-bd24-726c81fc8182

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_sm_one_tmul
import Theorems.Thm_GlobalTheory_DRFil_sm_mul
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
theorem _root_.solution (τ : K →ₐ[Qp] LL) (c : K) (x : V ⊗[Qp] F) :
    mulR Qp F LL V (algebraMap K F c) (sm Qp F LL V (idem F τ) x) = τ c • sm Qp F LL V (idem F τ) x := by
  rw [← sm_one_tmul, ← sm_mul, tmul_mul_idem, map_smul, LinearMap.smul_apply]
end GlobalTheory.DRFil
