-- Prove2me | solution 1 for GlobalTheory.TransferCommutator.transfer_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:03.516541+00:00
-- url     : https://prove2.me/submissions/6596109e-4083-44b7-a1da-21c6faf0eb6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSmulEqZeroOfCrossed
import Theorems.Thm_GlobalTheory_TransferCommutator_exists_smul_eq_zero_of_crossed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TransferCommutator
namespace GlobalTheory.TransferCommutator
theorem _root_.solution (G : Type) [Group G] [Finite G] (B : Type) [CommGroup B] (φ : commutator G →* B) :
    MonoidHom.transfer φ = 1 := by
  classical
  let Q := Abelianization G
  have hfin : Finite Q := inferInstanceAs (Finite (G ⧸ commutator G))
  let : Fintype Q := (commutator G).fintypeQuotientOfFiniteIndex
  let R := MonoidAlgebra ℤ Q
  let T : (commutator G).LeftTransversal := default
  let α : Q → G := fun q => (T.2.leftQuotientEquiv q : G)
  have hα : ∀ q, Abelianization.of (α q) = q := fun q => T.2.leftQuotientEquiv.symm_apply_apply q
  have hmem : ∀ g q, (α q)⁻¹ * g * α ((Abelianization.of g)⁻¹ * q) ∈ commutator G := fun g q => by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    simp [hα]
  let b : G → Q → Additive B := fun g q => Additive.ofMul (φ ⟨_, hmem g q⟩)
  have hb : ∀ g h q, b (g * h) q = b g q + b h ((Abelianization.of g)⁻¹ * q) := fun g h q => by
    simp only [b]
    rw [← ofMul_mul, ← map_mul]
    congr 2
    ext
    simp [mul_assoc]
  let s : Q →* R := MonoidAlgebra.of ℤ Q
  let ε : R →ₐ[ℤ] ℤ := MonoidAlgebra.lift ℤ ℤ Q 1
  let d : G → (R ⊗[ℤ] Additive B) × R := fun g => (∑ q, s q ⊗ₜ b g q, s (Abelianization.of g) - 1)
  obtain ⟨μ, hμ, h0⟩ := exists_smul_eq_zero_of_crossed (ε : R →+* ℤ) (fun g => s (Abelianization.of g))
    (fun g => MonoidAlgebra.lift_of _ _) d fun g h => by
      refine Prod.ext ?_ ?_
      · simp only [d, Prod.fst_add, Prod.smul_fst, hb, TensorProduct.tmul_add, Finset.sum_add_distrib,
          Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]
        congr 1
        exact (Fintype.sum_equiv (Equiv.mulLeft (Abelianization.of g)) _ _ fun q => by simp).symm
      · simp only [d, Prod.snd_add, Prod.smul_snd, map_mul, smul_eq_mul]; ring
  have hinv : ∀ q, μ * s q = μ := fun q => by
    have := congrArg Prod.snd (h0 (α q))
    simp only [d, Prod.smul_snd, hα, smul_eq_mul, mul_sub, mul_one, Prod.snd_zero] at this
    exact sub_eq_zero.1 this
  have hc : ∀ q, μ.coeff q = μ.coeff 1 := fun q => by
    have := MonoidAlgebra.coeff_mul_single_apply μ 1 q⁻¹ 1
    rw [show μ * MonoidAlgebra.single q⁻¹ 1 = μ from hinv q⁻¹] at this
    rw [inv_inv, one_mul, mul_one] at this
    exact this.symm
  have hε : ε μ = (Nat.card Q : ℤ) * μ.coeff 1 := by
    simp only [ε]
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [hc]
  have hu : (μ.coeff 1).natAbs = 1 := by
    rw [show (ε : R →+* ℤ) μ = _ from hε, Int.natAbs_mul, Int.natAbs_natCast] at hμ
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) (hμ.trans (mul_one _).symm)
  let c : R →ₗ[ℤ] ℤ := Finsupp.lapply (1 : Q) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℤ (S := ℤ) (M := Q)).toLinearMap
  ext g
  have h1 := congrArg Prod.fst (h0 g)
  simp only [d, Prod.smul_fst, Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, hinv, Prod.fst_zero,
    ← TensorProduct.tmul_sum] at h1
  have h2 := congrArg (fun x => TensorProduct.lid ℤ _ (c.rTensor _ x)) h1
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h2
  have h3 : ∑ q, b g q = 0 := by
    rcases Int.natAbs_eq_iff.1 hu with h | h
    · rw [show c μ = _ from h] at h2; simpa using h2
    · rw [show c μ = _ from h] at h2; simpa using h2
  rw [MonoidHom.transfer_def φ T, MonoidHom.one_apply]
  have h4 : ∏ q, (b g q).toMul = 1 := by rw [← toMul_sum, h3, toMul_zero]
  refine Eq.trans (Finset.prod_congr rfl fun q _ => congrArg φ (Subtype.ext ?_)) h4
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_assoc]
  rfl
end GlobalTheory.TransferCommutator
