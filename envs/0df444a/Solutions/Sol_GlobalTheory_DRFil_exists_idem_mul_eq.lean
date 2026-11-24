-- Prove2me | solution 1 for GlobalTheory.DRFil.exists_idem_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:09:21.25763+00:00
-- url     : https://prove2.me/submissions/d5f61162-98e2-4ede-95ff-fd2bfc401113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOfLinearIndependentDdRE
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul


section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil
namespace GlobalTheory.DRFil
private theorem idem_mul_tmul_one_eq_idem_mul_one_tmul {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {F : Type} [CommRing F] [Algebra Qp F] [Algebra K F] [IsScalarTower Qp K F]
    (τ : K →ₐ[Qp] LL) (c : K) :
    idem F τ * (τ c ⊗ₜ[Qp] (1 : F)) = idem F τ * ((1 : LL) ⊗ₜ[Qp] algebraMap K F c) := by
  unfold idem
  generalize_proofs
  rename_i hex
  obtain ⟨-, hspec⟩ := hex.choose_spec
  have h1 := congrArg (Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F))
    (hspec c)
  rw [map_mul, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at h1
  simp only [AlgHom.id_apply, map_one, IsScalarTower.coe_toAlgHom'] at h1
  rw [mul_comm]
  exact h1.symm.trans (mul_comm _ _)
end GlobalTheory.DRFil
end

set_option autoImplicit false
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil
open GlobalTheory GlobalTheory.DRFil
namespace GlobalTheory.DRFil
theorem _root_.solution {Qp K : Type} [Field Qp] [Field K] [Algebra Qp K]
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {F : Type} [CommRing F] [Algebra Qp F] [Algebra K F] [IsScalarTower Qp K F]
    (τ : K →ₐ[Qp] LL) {κ : Type} [Fintype κ] (l : κ → LL)
    (hl : ∀ a : LL, ∃ c : κ → K, a = ∑ j, τ (c j) * l j) (r : LL ⊗[Qp] F) :
    ∃ b : κ → F, idem F τ * r = idem F τ * ∑ j, l j ⊗ₜ[Qp] b j := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a f =>
    obtain ⟨c, hc⟩ := hl a
    refine ⟨fun j => algebraMap K F (c j) * f, ?_⟩
    rw [hc, TensorProduct.sum_tmul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc idem F τ * ((τ (c j) * l j) ⊗ₜ[Qp] f)
        = idem F τ * (τ (c j) ⊗ₜ[Qp] (1 : F)) * (l j ⊗ₜ[Qp] f) := by
          rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      _ = idem F τ * ((1 : LL) ⊗ₜ[Qp] algebraMap K F (c j)) * (l j ⊗ₜ[Qp] f) := by
          rw [idem_mul_tmul_one_eq_idem_mul_one_tmul]
      _ = idem F τ * (l j ⊗ₜ[Qp] (algebraMap K F (c j) * f)) := by
          rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy =>
    obtain ⟨bx, hbx⟩ := hx
    obtain ⟨by', hby⟩ := hy
    refine ⟨fun j => bx j + by' j, ?_⟩
    simp only [TensorProduct.tmul_add, Finset.sum_add_distrib, mul_add, hbx, hby]
end GlobalTheory.DRFil
