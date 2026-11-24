-- Prove2me | solution 1 for GlobalTheory.SymmTensor.mem_adjoin_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:24.618953+00:00
-- url     : https://prove2.me/submissions/0c3a1d6c-ec35-49ed-91f8-5995b4082b68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm
import Theorems.Thm_GlobalTheory_SymmTensor_sym_mem
import Theorems.Thm_GlobalTheory_SymmTensor_tens_unit_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SymmTensor
variable {n d : ℕ}
namespace GlobalTheory.SymmTensor
theorem _root_.solution (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ)
    (hT : ∀ π, T * permMat n d π = permMat n d π * T) :
    T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  have h1 : ∀ (π : Equiv.Perm (Fin d)) I K, T (I ∘ π) (K ∘ π) = T I K := fun π I K => by
    have := congrFun (congrFun (hT π) (I ∘ π)) K
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
      π.surjective.injective_comp_right.eq_iff] at this
    simpa using this
  have h2 : ∑ I, ∑ K, T I K • sym (fun p => Matrix.single (I p) (K p) (1 : ℂ)) = ((d.factorial : ℕ) : ℂ) • T := by
    ext I' K'
    simp only [sym, Matrix.sum_apply, Matrix.smul_apply, tens_unit_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    simp [h1, Fintype.card_perm]
  have h3 : ((d.factorial : ℕ) : ℂ) • T ∈ A :=
    h2 ▸ A.sum_mem fun I _ => A.sum_mem fun K _ => A.smul_mem (sym_mem _) _
  have h5 : ((d.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have := A.smul_mem h3 ((d.factorial : ℕ) : ℂ)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this
end GlobalTheory.SymmTensor
