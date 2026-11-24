-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.isUnit_det_of_productMap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:43.941546+00:00
-- url     : https://prove2.me/submissions/5944c565-cbbd-455a-a8a4-cee1c1bad054

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
import Theorems.Thm_GlobalTheory_annihilator_diagonal_form_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.pairing_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
open scoped TensorProduct
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
open IsLocalRing
namespace GlobalTheory.DiscrJacobian
namespace _root_.GlobalTheory.DiscrJacobian
theorem _root_.solution [IsLocalRing R]
    [Algebra (ResidueField R) C]
    [IsScalarTower R (ResidueField R) C] {d : ℕ} (b : Module.Basis (Fin d) R B)
    (n : Ideal B) (N : ℕ) (hN : n ^ N ≤ (maximalIdeal R).map (algebraMap R B))
    (ev : B →ₐ[R] ResidueField R) (hev : ∀ w ∈ n, ev w = 0)
    (hgen : ∀ w : B, ∃ c : R, w - algebraMap R B c ∈ n) (ρ : B →ₐ[R] C)
    (De : B ⊗[R] B) (M : Matrix (Fin d) (Fin d) R)
    (hDe : De = ∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j))
    (h : ∀ x : B, De * (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0)
    (H : Algebra.TensorProduct.productMap ρ
      ((IsScalarTower.toAlgHom R (ResidueField R) C).comp ev) De ≠ 0) :
    IsUnit M.det := by
  classical
  subst hDe
  haveI : Module.Finite R B := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  obtain ⟨i0, hi0⟩ : ∃ i, ev (∑ j, M i j • b j) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply H
    have hrow : ∀ i, ∑ j, M i j • (ρ (b i) *
        (IsScalarTower.toAlgHom R (ResidueField R) C) (ev (b j))) =
        ρ (b i) * (IsScalarTower.toAlgHom R (ResidueField R) C) (ev (∑ j, M i j • b j)) := by
      intro i
      simp [map_sum, Finset.mul_sum, mul_smul_comm]
    simp only [map_sum, map_smul, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      hrow, hcon, map_zero, mul_zero, Finset.sum_const_zero]
  set w := ∑ j, M i0 j • b j with hw
  have hwunit : IsUnit w := by
    obtain ⟨c, hc⟩ := hgen w
    have hevc : ev (algebraMap R B c) ≠ 0 := by
      have := hev _ hc
      rw [map_sub, sub_eq_zero] at this
      rwa [← this]
    have hcu : IsUnit c := by
      rw [AlgHom.commutes] at hevc
      by_contra hnu
      exact hevc ((IsLocalRing.residue_eq_zero_iff c).mpr ((IsLocalRing.mem_maximalIdeal c).mpr hnu))
    by_contra hnw
    obtain ⟨P, hP, hwP⟩ := Ideal.exists_le_maximal (Ideal.span {w})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hPc : P.comap (algebraMap R B) = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
    have hmP : (maximalIdeal R).map (algebraMap R B) ≤ P := by
      rw [Ideal.map_le_iff_le_comap, hPc]
    have hν : w - algebraMap R B c ∈ P :=
      hP.isPrime.mem_of_pow_mem N (hmP (hN (Ideal.pow_mem_pow hc N)))
    have hcP : algebraMap R B c ∈ P := by
      have := P.sub_mem (hwP (Ideal.mem_span_singleton_self w)) hν
      simpa using this
    have : c ∈ maximalIdeal R := by rw [← hPc]; exact hcP
    exact (IsLocalRing.mem_maximalIdeal c).mp this hcu
  obtain ⟨w', hw'⟩ := hwunit.exists_right_inv
  have hsurj : Function.Surjective (fun v : Fin d → R => Matrix.vecMul v M) := by
    intro t
    set u := w' * ∑ j, t j • b j with hu
    refine ⟨fun i => b.coord i0 (b i * u), ?_⟩
    have hs := _root_.GlobalTheory.annihilator_diagonal_form_swap (⇑b) M h (b.coord i0) u
    have hr : ∑ i, ∑ j, (M i j * b.coord i0 (b i)) • (b j * u) = ∑ j, t j • b j := by
      have : w * u = ∑ j, t j • b j := by rw [hu, ← mul_assoc, hw', one_mul]
      rw [← this, hw, Finset.sum_mul]
      simp [Module.Basis.coord_apply, Finsupp.single_apply, smul_mul_assoc]
    apply b.equivFun.symm.injective
    simp only [Module.Basis.equivFun_symm_apply]
    rw [← hr, ← hs]
    simp only [Matrix.vecMul, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp [mul_comm]
  exact (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
