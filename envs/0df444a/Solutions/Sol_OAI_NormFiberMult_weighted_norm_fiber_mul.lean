-- Prove2me | solution 1 for OAI.NormFiberMult.weighted_norm_fiber_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:16:01.691578+00:00
-- url     : https://prove2.me/submissions/cfcbb19e-fbd4-4deb-ac09-72f5c31c199c

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_NormFiberCRT_ideal_eq_factors
import Theorems.Thm_OAI_NormFiberCRT_ideal_factor_norms
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
namespace NormSplitArithmetic
end NormSplitArithmetic
namespace NormFiberCRT
end NormFiberCRT
namespace NormFiberMult
private theorem ideal_sup_span_norm_left (I J : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m)
    (hJ : Ideal.absNorm J = n) :
    I * J ⊔ Ideal.span {(m : O)} = I := by
  let A : Ideal O := Ideal.span {(m : O)}
  have hmI : A ≤ I := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    simpa only [hI] using Ideal.absNorm_mem I
  have hnJ : (n : O) ∈ J := by
    simpa only [hJ] using Ideal.absNorm_mem J
  have hnspan : Ideal.span {(n : O)} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr hnJ
  have hcast : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
  have hAB : A ⊔ Ideal.span {(n : O)} = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (m : O) (n : O)).mpr hcast)
  have hJA : J ⊔ A = ⊤ := by
    apply top_unique
    calc
      ⊤ = A ⊔ Ideal.span {(n : O)} := hAB.symm
      _ ≤ J ⊔ A := sup_le le_sup_right (hnspan.trans le_sup_left)
  apply le_antisymm
  · exact sup_le Ideal.mul_le_left hmI
  · calc
      I = I * (J ⊔ A) := by rw [hJA]; simp
      _ = I * J ⊔ I * A := by rw [Ideal.mul_sup]
      _ ≤ I * J ⊔ A := sup_le le_sup_left
        (Ideal.mul_le_right.trans le_sup_right)
private theorem ideal_sup_span_norm_right (I J : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m)
    (hJ : Ideal.absNorm J = n) :
    I * J ⊔ Ideal.span {(n : O)} = J := by
  simpa only [mul_comm] using
    ideal_sup_span_norm_left J I n m hcop.symm hJ hI
end NormFiberMult
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open Filter Asymptotics
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.NormFiberMult
namespace OAI.NormFiberMult
theorem _root_.solution (weight : Ideal O → ℂ)
    (hweight : ∀ I J : Ideal O,
      (Ideal.absNorm I).Coprime (Ideal.absNorm J) →
      weight (I * J) = weight I * weight J)
    (m n : ℕ) (hcop : m.Coprime n) :
    (∑ K ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) (m * n)).toFinset,
       weight K) =
    (∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) m).toFinset,
       weight I) *
    (∑ J ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset,
       weight J) := by
  let F (k : ℕ) : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_eq (S := O) k).toFinset
  have hmem (k : ℕ) (I : Ideal O) : I ∈ F k ↔ Ideal.absNorm I = k := by
    simp [F]
  change (∑ K ∈ F (m * n), weight K) =
    (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J)
  calc
    (∑ K ∈ F (m * n), weight K) =
        ∑ p ∈ (F m).product (F n), weight (p.1 * p.2) := by
      refine Finset.sum_bij'
        (fun K _ => (K ⊔ Ideal.span {(m : O)},
                     K ⊔ Ideal.span {(n : O)}))
        (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
      · intro K hK
        have hKnorm : Ideal.absNorm K = m * n := (hmem _ _).mp hK
        obtain ⟨hm, hn⟩ := NormFiberCRT.ideal_factor_norms K m n hcop hKnorm
        simp [Finset.mem_product, hmem, hm, hn]
      · intro p hp
        have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
        have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
        exact (hmem _ _).mpr (by rw [map_mul, hm, hn])
      · intro K hK
        exact (NormFiberCRT.ideal_eq_factors K m n hcop ((hmem _ _).mp hK)).symm
      · intro p hp
        have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
        have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
        apply Prod.ext
        · exact ideal_sup_span_norm_left p.1 p.2 m n hcop hm hn
        · exact ideal_sup_span_norm_right p.1 p.2 m n hcop hm hn
      · intro K hK
        exact congrArg weight
          (NormFiberCRT.ideal_eq_factors K m n hcop ((hmem _ _).mp hK))
    _ = ∑ p ∈ (F m).product (F n), weight p.1 * weight p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
      have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
      exact hweight p.1 p.2 (by simpa [hm, hn] using hcop)
    _ = (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J) := by
      calc
        (∑ p ∈ (F m).product (F n), weight p.1 * weight p.2) =
            ∑ I ∈ F m, ∑ J ∈ F n, weight I * weight J := by
          exact Finset.sum_product' (F m) (F n) (fun I J => weight I * weight J)
        _ = (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
end OAI.NormFiberMult
