-- Prove2me | solution 1 for OAI.Erdos3.exists_schmidt_dilated_mean_transfer_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:32:20.247989+00:00
-- url     : https://prove2.me/submissions/7b57f3ea-0587-4a24-b0d3-177e770d4c04

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B085
import Theorems.Thm_OAI_Erdos3_exists_schmidt_gaussian_mean_transfer_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ latticeGaussianMass Λ t x := tsum_nonneg (fun _ => (Real.exp_pos _).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricIntervalDilation
namespace OAI

section

namespace Erdos3

theorem symmetricInterval_sum_dilation (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (a : ℤ) (ha : a ≠ 0) (H N : ℕ) (hsize : |(a : ℝ)| * H ≤ N) :
    (∑ n ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), f (a * n)) ≤
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n := by
  classical
  have hsizeZ : |a| * (H : ℤ) ≤ (N : ℤ) := by exact_mod_cast hsize
  have hinj : Function.Injective (fun n : ℤ => a * n) := fun _ _ h => mul_left_cancel₀ ha h
  have hsub : (Finset.Icc (-(H : ℤ)) (H : ℤ)).image (fun n => a * n) ⊆
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    have hmabs : |m| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hm)
    apply Finset.mem_Icc.mpr
    apply abs_le.mp
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hmabs (abs_nonneg a)).trans hsizeZ
  rw [← Finset.sum_image (fun _ _ _ _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianNormalizer_nonneg (Λ : Submodule ℤ E) (t : ℝ) :
    0 ≤ latticeGaussianNormalizer Λ t :=
  mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) ENNReal.toReal_nonneg

theorem normalizedLatticeGaussian_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ normalizedLatticeGaussian Λ t x :=
  mul_nonneg (latticeGaussianNormalizer_nonneg Λ t) (latticeGaussianMass_nonneg Λ t x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtGaussianMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianMean_nonneg (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) :
    0 ≤ latticeGaussianMean Λ t k α N := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun _ _ => normalizedLatticeGaussian_nonneg Λ t _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrimitiveNormalDilation
namespace OAI

section

namespace Erdos3

theorem integerDistance_le_abs_sub_integer (x : ℝ) (p : ℤ) :
    CircleFourier.integerDistance (x : CircleFourier.Circle) ≤ |x - p| := by
  rw [CircleFourier.integerDistance_coe]
  exact round_le x p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem primitiveNormal_dilation_identity (α ξ ζ : E) (m p : ℤ) (q j : ℕ)
    (hξ : ξ = (m : ℝ) • ζ) :
    inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) -
        (((q : ℤ) * m) ^ j * p : ℤ) =
      ((((q : ℤ) * m : ℤ) : ℝ) ^ j) * ((q : ℝ) * inner ℝ ξ α - p) := by
  rw [hξ, inner_smul_right, real_inner_smul_left, pow_succ]
  push_cast
  ring

theorem primitiveNormal_dilation_error (α ξ ζ : E) (m p : ℤ) (q j : ℕ)
    (hξ : ξ = (m : ℝ) • ζ) {η : ℝ}
    (happrox : |(q : ℝ) * inner ℝ ξ α - p| ≤ η) :
    CircleFourier.integerDistance
        ((inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) : ℝ) : CircleFourier.Circle) ≤
      |(((q : ℤ) * m : ℤ) : ℝ)| ^ j * η := by
  calc
    _ ≤ |inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) -
        (((q : ℤ) * m) ^ j * p : ℤ)| := integerDistance_le_abs_sub_integer _ _
    _ = |(((q : ℤ) * m : ℤ) : ℝ)| ^ j * |(q : ℝ) * inner ℝ ξ α - p| := by
      rw [primitiveNormal_dilation_identity α ξ ζ m p q j hξ, abs_mul, abs_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left happrox (pow_nonneg (abs_nonneg _) _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeGaussianDilation
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianMean_dilation (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E)
    (a : ℤ) (ha : a ≠ 0) (H N : ℕ) (hsize : |(a : ℝ)| * H ≤ N) :
    (2 * (H : ℝ) + 1) * latticeGaussianMean Λ t k ((a : ℝ) ^ k • α) H ≤
      (2 * (N : ℝ) + 1) * latticeGaussianMean Λ t k α N := by
  have h := symmetricInterval_sum_dilation
    (fun n => normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α))
    (fun n => normalizedLatticeGaussian_nonneg Λ t _) a ha H N hsize
  have hid (n : ℤ) : ((a * n : ℤ) : ℝ) ^ k • α =
      (n : ℝ) ^ k • ((a : ℝ) ^ k • α) := by
    rw [Int.cast_mul, mul_pow, smul_smul, mul_comm]
  simp only [hid] at h
  unfold latticeGaussianMean
  simp only [symmetricInterval_card, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [mul_div_cancel₀ _ (by positivity : 2 * (H : ℝ) + 1 ≠ 0),
    mul_div_cancel₀ _ (by positivity : 2 * (N : ℝ) + 1 ≠ 0)]
  exact h

theorem latticeGaussianMean_dilation_loss (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E)
    (a : ℤ) (ha : a ≠ 0) (H N : ℕ) {K : ℝ}
    (hsize : |(a : ℝ)| * H ≤ N) (hK : 1 ≤ K) (hlength : (N : ℝ) ≤ 2 * K * H) :
    latticeGaussianMean Λ t k ((a : ℝ) ^ k • α) H ≤
      2 * K * latticeGaussianMean Λ t k α N := by
  have h := latticeGaussianMean_dilation Λ t k α a ha H N hsize
  have hratio : 2 * (N : ℝ) + 1 ≤ 2 * K * (2 * H + 1) := by nlinarith
  have hnonneg := latticeGaussianMean_nonneg Λ t k α N
  have hh : 0 < 2 * (H : ℝ) + 1 := by positivity
  have hupper := mul_le_mul_of_nonneg_right hratio hnonneg
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtIntervalBudget
namespace OAI

section

namespace Erdos3

theorem schmidt_monomial_interval_budget (j : ℕ) {H N Q B S ε : ℝ}
    (hH : 0 ≤ H) (hN : 0 < N) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hHQ : H * Q ≤ N) (hHBS : H * B * S ≤ ε * N) :
    H ^ (j + 1) * Q ^ j * (B / N ^ (j + 1)) * S ≤ ε := by
  have hp := pow_le_pow_left₀ (mul_nonneg hH hQ) hHQ j
  have hmul := mul_le_mul hp hHBS (by positivity : 0 ≤ H * B * S)
    (pow_nonneg hN.le j)
  have hid : H ^ (j + 1) * Q ^ j * (B / N ^ (j + 1)) * S =
      ((H * Q) ^ j * (H * B * S)) / N ^ (j + 1) := by
    rw [mul_pow, pow_succ H]
    ring
  rw [hid]
  apply (div_le_iff₀ (pow_pos hN _)).mpr
  calc
    _ ≤ N ^ j * (ε * N) := hmul
    _ = ε * N ^ (j + 1) := by rw [pow_succ]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem schmidt_primitive_dilation_room (α ξ ζ : E) (m p : ℤ) (q j H N : ℕ)
    (hξ : ξ = (m : ℝ) • ζ) (hζ : ζ ≠ 0) (hN : 0 < N)
    {t Q B S ε : ℝ} (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hs : Real.sqrt t ≤ ‖ζ‖ * S)
    (ha : |(((q : ℤ) * m : ℤ) : ℝ)| ≤ Q)
    (happrox : |(q : ℝ) * inner ℝ ξ α - p| ≤ B / (2 * (N : ℝ) + 1) ^ (j + 1))
    (hHQ : (H : ℝ) * Q ≤ N) (hHBS : (H : ℝ) * B * S ≤ ε * N) :
    Real.sqrt t * ((H : ℝ) ^ (j + 1) *
      (CircleFourier.integerDistance
        ((inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) : ℝ) : CircleFourier.Circle) /
        ‖ζ‖)) ≤ ε := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have happrox' : |(q : ℝ) * inner ℝ ξ α - p| ≤ B / (N : ℝ) ^ (j + 1) := by
    apply happrox.trans
    exact div_le_div_of_nonneg_left hB (pow_pos hNR _) (pow_le_pow_left₀ hNR.le (by linarith) _)
  have herr := primitiveNormal_dilation_error α ξ ζ m p q j hξ happrox'
  have hs' : Real.sqrt t / ‖ζ‖ ≤ S := (div_le_iff₀ hnorm).mpr (by nlinarith [hs])
  have hpow := pow_le_pow_left₀ (abs_nonneg (((q : ℤ) * m : ℤ) : ℝ)) ha j
  have herr' := herr.trans (mul_le_mul_of_nonneg_right hpow (div_nonneg hB (pow_nonneg hNR.le _)))
  calc
    _ = ((H : ℝ) ^ (j + 1) * CircleFourier.integerDistance
        ((inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) : ℝ) : CircleFourier.Circle)) *
        (Real.sqrt t / ‖ζ‖) := by ring
    _ ≤ ((H : ℝ) ^ (j + 1) * (Q ^ j * (B / (N : ℝ) ^ (j + 1)))) * S := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left herr' (by positivity)
      · exact hs'
      · exact div_nonneg (Real.sqrt_nonneg _) hnorm.le
      · positivity
    _ = (H : ℝ) ^ (j + 1) * Q ^ j * (B / (N : ℝ) ^ (j + 1)) * S := by ring
    _ ≤ ε := schmidt_monomial_interval_budget j (Nat.cast_nonneg _) hNR hQ hB hS hHQ hHBS

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_schmidt_dilated_mean_transfer_s2_oai
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (α ξ ζ w : E) (m p : ℤ) (q j H N : ℕ)
    (hm : m ≠ 0) (hq : 0 < q) (hξ : ξ = (m : ℝ) • ζ)
    (hζ : ζ ≠ 0) (hζdual : ζ ∈ euclideanDualLattice Λ) (hwΛ : w ∈ Λ) (hw : inner ℝ ζ w = 1)
    (hN : 0 < N) {t Q B S ε L K : ℝ}
    (ht : 0 < t) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hS : 0 ≤ S) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hbudget : (Module.finrank ℝ (normalFunctional ζ).ker : ℝ) * ε ≤ 1)
    (hs : Real.sqrt t ≤ ‖ζ‖ * S) (hnorm : ‖ζ‖ ≤ Real.sqrt t * L)
    (ha : |(((q : ℤ) * m : ℤ) : ℝ)| ≤ Q)
    (happrox : |(q : ℝ) * inner ℝ ξ α - p| ≤ B / (2 * (N : ℝ) + 1) ^ (j + 1))
    (hHQ : (H : ℝ) * Q ≤ N) (hHBS : (H : ℝ) * B * S ≤ ε * N)
    (hK : 1 ≤ K) (hlength : (N : ℝ) ≤ 2 * K * H) :
    ∃ β : (normalFunctional ζ).ker,
      latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) (j + 1) β H ≤
        (2 * Real.exp (4 * Real.pi + 1) * L * K) * latticeGaussianMean Λ t (j + 1) α N ∧
      normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) 0 ≤ Real.exp 1 * L * normalizedLatticeGaussian Λ t 0 := by
  have hroom := schmidt_primitive_dilation_room α ξ ζ m p q j H N hξ hζ hN
    hQ hB hS hs ha happrox hHQ hHBS
  obtain ⟨β, hmean, hmass⟩ := exists_schmidt_gaussian_mean_transfer_s2 Λ ζ hζ hζdual w hwΛ hw
    ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) ht hε hεone hbudget hroom
  have ha0 : (q : ℤ) * m ≠ 0 := mul_ne_zero (by exact_mod_cast hq.ne') hm
  have hsize : |(((q : ℤ) * m : ℤ) : ℝ)| * H ≤ N := by
    calc
      _ ≤ Q * H := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
      _ ≤ N := by nlinarith [hHQ]
  have hdilate := latticeGaussianMean_dilation_loss Λ t (j + 1) α ((q : ℤ) * m) ha0 H N
    hsize hK hlength
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hmean0 := latticeGaussianMean_nonneg Λ t (j + 1) α N
  have hmass0 := normalizedLatticeGaussian_nonneg Λ t 0
  have hnorm' := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos 1).le
  have hmean' := hmean.trans (mul_le_mul hnorm' hdilate
    (latticeGaussianMean_nonneg Λ t (j + 1) _ H) (by positivity))
  have hmass' := hmass.trans (mul_le_mul_of_nonneg_right hnorm' hmass0)
  refine ⟨β, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hmean' (Real.exp_pos (4 * Real.pi)).le
    have he : Real.exp (4 * Real.pi) * Real.exp (-4 * Real.pi) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have he' : Real.exp (4 * Real.pi) * Real.exp 1 = Real.exp (4 * Real.pi + 1) :=
      (Real.exp_add _ _).symm
    have hleft : Real.exp (4 * Real.pi) *
        (Real.exp (-4 * Real.pi) * Real.sqrt t *
          latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
            (t * (1 + ε) ^ 2) (j + 1) β H) =
        Real.sqrt t * latticeGaussianMean (latticeHyperplane Λ (normalFunctional ζ))
          (t * (1 + ε) ^ 2) (j + 1) β H := by rw [← mul_assoc, ← mul_assoc, he, one_mul]
    rw [hleft] at hh
    have hright : Real.exp (4 * Real.pi) *
        (Real.exp 1 * (Real.sqrt t * L) * (2 * K * latticeGaussianMean Λ t (j + 1) α N)) =
        Real.sqrt t * ((2 * Real.exp (4 * Real.pi + 1) * L * K) *
          latticeGaussianMean Λ t (j + 1) α N) := by rw [← he']; ring
    rw [hright] at hh
    exact (mul_le_mul_iff_right₀ hspos).mp hh
  · have hright : Real.exp 1 * (Real.sqrt t * L) * normalizedLatticeGaussian Λ t 0 =
        Real.sqrt t * (Real.exp 1 * L * normalizedLatticeGaussian Λ t 0) := by ring
    rw [hright] at hmass'
    exact (mul_le_mul_iff_right₀ hspos).mp hmass'

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.exists_schmidt_dilated_mean_transfer_s2_oai.{u_1} := @OAI.Erdos3.exists_schmidt_dilated_mean_transfer_s2_oai.{u_1}
