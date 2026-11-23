-- Prove2me | solution 1 for GlobalTheory.DRFil.idem_repr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:59:34.808742+00:00
-- url     : https://prove2.me/submissions/7309e900-13bb-43f7-8f41-ae633ffc6492

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
theorem _root_.solution (τ : K →ₐ[Qp] LL) : ∃ (n : ℕ) (a : Fin n → LL) (c : Fin n → K),
    idem F τ = ∑ i, a i ⊗ₜ[Qp] algebraMap K F (c i) ∧ ∑ i, a i * τ (c i) = 1 := by
  obtain ⟨n, a, c, h⟩ := TensorProduct.exists_sum_tmul_eq (exists_idem τ).choose
  refine ⟨n, a, c, ?_, ?_⟩
  · rw [idem, h]
    simp [map_sum]
  · have := (exists_idem τ).choose_spec.1
    rw [h] at this
    simpa [map_sum] using this
end GlobalTheory.DRFil
