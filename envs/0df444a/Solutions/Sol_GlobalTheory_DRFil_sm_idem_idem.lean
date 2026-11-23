-- Prove2me | solution 1 for GlobalTheory.DRFil.sm_idem_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:37.2764+00:00
-- url     : https://prove2.me/submissions/dbf6df70-2b8a-4939-a791-43bb9c7cffa3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_mulR_sm_idem
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_of_eigen

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
theorem _root_.solution (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] F) :
    sm Qp F LL V (idem F τ) (sm Qp F LL V (idem F τ) x) = sm Qp F LL V (idem F τ) x :=
  sm_idem_of_eigen τ _ fun c => mulR_sm_idem τ c x
end GlobalTheory.DRFil
