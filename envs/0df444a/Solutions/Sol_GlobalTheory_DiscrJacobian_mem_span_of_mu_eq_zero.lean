-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.mem_span_of_mu_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:45.82405+00:00
-- url     : https://prove2.me/submissions/6451a622-94a3-4812-bc6b-820abc1cadae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]
open scoped TensorProduct
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]
namespace GlobalTheory.DiscrJacobian
namespace _root_.GlobalTheory.DiscrJacobian
theorem _root_.solution {ι : Type} [Fintype ι] [Module.Finite R B]
    [Module.FinitePresentation S B] (x : ι → S)
    (hx : ∀ j, x j ∈ (⊥ : Ideal S).jacobson)
    (hgen : ∀ s : S, ∃ (c : R) (u : ι → S), s = algebraMap R S c + ∑ j, x j * u j)
    (z : S ⊗[R] B) (hz : _root_.GlobalTheory.DiscrJacobian.mu R S B z = 0) :
    z ∈ Ideal.span (Set.range fun j => x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j)) := by
  classical
  set J := Ideal.span (Set.range fun j => x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j))
    with hJ
  set K : Ideal (S ⊗[R] B) := RingHom.ker (_root_.GlobalTheory.DiscrJacobian.mu R S B) with hK
  set I : Ideal (S ⊗[R] B) := Ideal.map (algebraMap S (S ⊗[R] B)) (Ideal.span (Set.range x))
    with hI
  let δ : S → S ⊗[R] B := fun s => s ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B s
  have hδK : ∀ s, δ s ∈ K := by
    intro s; simp [K, δ, RingHom.mem_ker]
  have hδJ : ∀ j, δ (x j) ∈ J := fun j => Ideal.subset_span ⟨j, rfl⟩
  have hxI : ∀ j, x j ⊗ₜ[R] (1 : B) ∈ I := fun j =>
    Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  have hadd : ∀ a b, δ (a + b) = δ a + δ b := by
    intro a b; simp only [δ, map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
  have hmul : ∀ a b, δ (a * b) =
      δ a * (b ⊗ₜ[R] (1 : B)) + (a ⊗ₜ[R] (1 : B)) * δ b - δ a * δ b := by
    intro a b
    simp only [δ, map_mul, sub_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    abel
  have hδ : ∀ s, δ s ∈ J ⊔ I * K := by
    intro s
    obtain ⟨c, u, rfl⟩ := hgen s
    have hc : δ (algebraMap R S c) = 0 := by
      show _ - _ = 0
      rw [sub_eq_zero, ← IsScalarTower.algebraMap_apply R S B, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have hsum : ∀ t : Finset ι, δ (∑ j ∈ t, x j * u j) = ∑ j ∈ t, δ (x j * u j) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp [δ]
      | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
    rw [hadd, hc, zero_add, hsum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [hmul]
    refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (hδJ j))
    · exact Ideal.mem_sup_right (Ideal.mul_mem_mul (hxI j) (hδK (u j)))
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (hδJ j))
  have hle : K ≤ J ⊔ I * K := by
    intro z hz
    have key : ∀ t : S ⊗[R] B, t - (1 : S) ⊗ₜ[R] _root_.GlobalTheory.DiscrJacobian.mu R S B t ∈ J ⊔ I * K := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
        rw [map_add, TensorProduct.tmul_add]
        convert Ideal.add_mem _ ha hb using 1
        abel
      | tmul s w =>
        have : s ⊗ₜ[R] w - (1 : S) ⊗ₜ[R] _root_.GlobalTheory.DiscrJacobian.mu R S B (s ⊗ₜ[R] w) = δ s * ((1 : S) ⊗ₜ[R] w) := by
          simp [δ, sub_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_right _ _ (hδ s)
    have := key z
    rwa [show _root_.GlobalTheory.DiscrJacobian.mu R S B z = 0 from hz, TensorProduct.tmul_zero, sub_zero] at this
  have hKfg : K.FG := by
    obtain ⟨t, ht⟩ := Module.FinitePresentation.fg_ker (_root_.GlobalTheory.DiscrJacobian.mu R S B).toLinearMap
      (fun w => ⟨1 ⊗ₜ w, by simp⟩)
    refine ⟨t, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le]
      intro a ha
      have := ht ▸ Submodule.subset_span ha
      simpa [K, RingHom.mem_ker] using this
    · intro a ha
      have : a ∈ Submodule.span S (t : Set (S ⊗[R] B)) := by
        rw [ht]; simpa [K, RingHom.mem_ker] using ha
      exact Submodule.span_le_restrictScalars S (S ⊗[R] B) _ this
  have hIjac : I ≤ (⊥ : Ideal (S ⊗[R] B)).jacobson := by
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    haveI : Algebra.IsIntegral S (S ⊗[R] B) := Algebra.IsIntegral.of_finite _ _
    unfold Ideal.jacobson
    rw [Ideal.mem_sInf]
    intro M hM
    haveI : M.IsMaximal := hM.2
    have hMc : (M.comap (algebraMap S (S ⊗[R] B))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have h2 := hx j
    unfold Ideal.jacobson at h2
    exact Ideal.mem_sInf.mp h2 ⟨bot_le, hMc⟩
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hKfg hIjac (by simpa [smul_eq_mul] using hle) hz
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
