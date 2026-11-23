-- Prove2me | solution 1 for GlobalTheory.DRFil.sm_idem_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:28.869831+00:00
-- url     : https://prove2.me/submissions/7b139b87-2d41-4a43-87af-766fd94bea1b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_sm_tmul_left
import Theorems.Thm_GlobalTheory_DRFil_idem_repr

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
theorem _root_.solution (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] F)
    (hx : ∀ c : K, mulR Qp F LL V (algebraMap K F c) x = τ c • x) : sm Qp F LL V (idem F τ) x = x := by
  obtain ⟨n, a, c, h, h1⟩ := idem_repr F τ
  rw [h, map_sum, LinearMap.sum_apply]
  simp only [sm_tmul_left, hx, smul_smul, ← Finset.sum_smul, h1, one_smul]
end GlobalTheory.DRFil
