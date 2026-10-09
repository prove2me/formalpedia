-- Prove2me | solution 1 for OAI.Erdos3.exists_schmidt_dilated_mean_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T07:34:00.728982+00:00
-- url     : https://prove2.me/submissions/57a6a654-9099-424b-8388-7f98d6463e36

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B110
import Definitions.Def_OAIErdos3B122

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GaussianPerturbation
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_sq_le_four_add_dilated_norm_sq (x y : E) {ε : ℝ}
    (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hxy : ‖x - y‖ ≤ ε) :
    ‖x‖ ^ 2 ≤ 4 + ‖(1 + ε) • y‖ ^ 2 := by
  have hnorm : ‖x‖ ≤ ε + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ ε + ‖y‖ := add_le_add hxy le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + ε)]
  by_cases hx : ‖x‖ ≤ 2
  · nlinarith [norm_nonneg x, sq_nonneg ((1 + ε) * ‖y‖)]
  · have hlarge : 2 < ‖x‖ := lt_of_not_ge hx
    have hc : 0 ≤ ε * (‖x‖ - 1 - ε) := mul_nonneg hε (by linarith)
    have hm := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 1 + ε by linarith)
    have hbound : ‖x‖ ≤ (1 + ε) * ‖y‖ := by nlinarith only [hc, hm]
    nlinarith only [hbound, sq_nonneg ((1 + ε) * ‖y‖ - ‖x‖), norm_nonneg x]

theorem gaussian_perturbation_lower (x y : E) {ε : ℝ}
    (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hxy : ‖x - y‖ ≤ ε) :
    Real.exp (-4 * Real.pi) * Real.exp (-Real.pi * ‖(1 + ε) • y‖ ^ 2) ≤
      Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left (norm_sq_le_four_add_dilated_norm_sq x y hε hεone hxy)
    Real.pi_pos.le
  nlinarith only [hm]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem latticeHyperplane_span_top (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    Submodule.span ℝ (latticeHyperplane Λ f : Set f.ker) = ⊤ := by
  let S := Submodule.span ℝ (latticeHyperplane Λ f : Set f.ker)
  have hall : ∀ x : E, hyperplaneRetraction f w hw x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Λ : Set E) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hyperplaneRetraction_mem Λ f hint w hwΛ hw x hx)
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y hx hy hpx hpy => simpa only [map_add] using S.add_mem hpx hpy
    | smul a x hx hpx => simpa only [map_smul] using S.smul_mem a hpx
  apply top_le_iff.mp
  intro x hx
  simpa only [hyperplaneRetraction_on_kernel] using hall (x : E)

theorem latticeHyperplane_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (f : E →ₗ[ℝ] ℝ)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, f x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) :
    IsZLattice ℝ (latticeHyperplane Λ f) :=
  ⟨latticeHyperplane_span_top Λ f (IsZLattice.span_top (K := ℝ)) hint w hwΛ hw⟩

theorem hyperplane_finrank [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ)
    (w : E) (hw : f w = 1) : Module.finrank ℝ f.ker + 1 = Module.finrank ℝ E := by
  have hsurj : Function.Surjective f := by
    intro a
    exact ⟨a • w, by simp only [map_smul, hw, smul_eq_mul, mul_one]⟩
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h
  omega

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_nonneg (Λ : Submodule ℤ E) (t : ℝ) (x : E) :
    0 ≤ latticeGaussianMass Λ t x := tsum_nonneg (fun _ => (Real.exp_pos _).le)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeGaussianMass_eq_of_sub_mem (Λ : Submodule ℤ E) (t : ℝ) {x y : E}
    (hxy : x - y ∈ Λ) : latticeGaussianMass Λ t x = latticeGaussianMass Λ t y := by
  have h := latticeGaussianMass_add_lattice Λ t y ⟨x - y, hxy⟩
  simpa only [add_sub_cancel] using h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IntegralHyperplaneCorrection
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integralHyperplaneCorrection_inner (ξ x : E) (hξ : ξ ≠ 0) :
    inner ℝ ξ (integralHyperplaneCorrection ξ x) = (round (inner ℝ ξ x) : ℝ) := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  simp only [integralHyperplaneCorrection, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem integralHyperplaneCorrection_norm_sub (ξ x : E) (hξ : ξ ≠ 0) :
    ‖integralHyperplaneCorrection ξ x - x‖ =
      CircleFourier.integerDistance ((inner ℝ ξ x : ℝ) : CircleFourier.Circle) / ‖ξ‖ := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  rw [CircleFourier.integerDistance_coe]
  have hid : integralHyperplaneCorrection ξ x - x =
      -(((inner ℝ ξ x - (round (inner ℝ ξ x) : ℝ)) / ‖ξ‖ ^ 2) • ξ) := by
    unfold integralHyperplaneCorrection
    abel
  rw [hid, norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖ξ‖)]
  field_simp

theorem exists_hyperplane_lattice_translate (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (w : E) (hwΛ : w ∈ Λ) (hw : f w = 1) (x : E) (n : ℤ) (hx : f x = (n : ℝ)) :
    ∃ y : f.ker, x - (y : E) ∈ Λ := by
  refine ⟨hyperplaneRetraction f w hw x, ?_⟩
  change x - (x - f x • w) ∈ Λ
  rw [sub_sub_cancel, hx]
  simpa only [Int.cast_smul_eq_zsmul] using Λ.smul_mem n hwΛ

theorem exists_corrected_hyperplane_representative (Λ : Submodule ℤ E) (ξ : E) (hξ : ξ ≠ 0)
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) (x : E) :
    ∃ (β : E) (y : (normalFunctional ξ).ker),
      β - (y : E) ∈ Λ ∧
      ‖β - x‖ = CircleFourier.integerDistance ((inner ℝ ξ x : ℝ) : CircleFourier.Circle) / ‖ξ‖ := by
  let β := integralHyperplaneCorrection ξ x
  obtain ⟨y, hy⟩ := exists_hyperplane_lattice_translate Λ (normalFunctional ξ) w hwΛ hw β
    (round (inner ℝ ξ x)) (integralHyperplaneCorrection_inner ξ x hξ)
  exact ⟨β, y, hy, integralHyperplaneCorrection_norm_sub ξ x hξ⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NormalHyperplaneProjection
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem normalHyperplane_starProjection (ξ x : E) (hξ : ξ ≠ 0) :
    (normalFunctional ξ).ker.starProjection x =
      x - (inner ℝ ξ x / ‖ξ‖ ^ 2) • ξ := by
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hξ)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change inner ℝ ξ (x - (inner ℝ ξ x / ‖ξ‖ ^ 2) • ξ) = 0
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ hn, sub_self]
  · intro y hy
    have hy' : inner ℝ ξ y = 0 := hy
    rw [sub_sub_cancel, real_inner_smul_left, hy', mul_zero]

theorem normalHyperplane_height (ξ w : E) (hξ : ξ ≠ 0)
    (hw : inner ℝ ξ w = 1) :
    ‖w - (normalFunctional ξ).ker.starProjection w‖ = ‖ξ‖⁻¹ := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  rw [normalHyperplane_starProjection ξ w hξ, sub_sub_cancel, hw,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeGaussianHyperplane
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem latticeHyperplaneInclusion_injective (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ) :
    Function.Injective (latticeHyperplaneInclusion Λ f) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Λ => (z : E)) hxy

theorem latticeGaussianMass_hyperplane_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (f : E →ₗ[ℝ] ℝ) {t : ℝ} (ht : 0 < t) (x : f.ker) :
    latticeGaussianMass (latticeHyperplane Λ f) t x ≤ latticeGaussianMass Λ t (x : E) := by
  have h := tsum_comp_le_tsum_of_inj (lattice_gaussian_summable Λ ht (x : E))
    (fun _ => (Real.exp_pos _).le) (latticeHyperplaneInclusion_injective Λ f)
  exact h

theorem latticeGaussianMass_hyperplane_translate_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (f : E →ₗ[ℝ] ℝ) {t : ℝ} (ht : 0 < t) (x : E) (y : f.ker)
    (hxy : x - (y : E) ∈ Λ) :
    latticeGaussianMass (latticeHyperplane Λ f) t y ≤ latticeGaussianMass Λ t x := by
  rw [latticeGaussianMass_eq_of_sub_mem Λ t hxy]
  exact latticeGaussianMass_hyperplane_le Λ f ht y

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeGaussianTemperature
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussian_perturbation_at_temperature (x y : E) {t ε : ℝ}
    (ht : 0 ≤ t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hxy : Real.sqrt t * ‖x - y‖ ≤ ε) :
    Real.exp (-4 * Real.pi) * Real.exp (-Real.pi * (t * (1 + ε) ^ 2) * ‖y‖ ^ 2) ≤
      Real.exp (-Real.pi * t * ‖x‖ ^ 2) := by
  have he : ‖Real.sqrt t • x - Real.sqrt t • y‖ ≤ ε := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    exact hxy
  have h := gaussian_perturbation_lower (Real.sqrt t • x) (Real.sqrt t • y) hε hεone he
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t),
    abs_of_nonneg (show 0 ≤ 1 + ε by linarith), mul_pow, Real.sq_sqrt ht] at h
  rw [show -Real.pi * (t * (1 + ε) ^ 2) * ‖y‖ ^ 2 =
    -Real.pi * ((1 + ε) ^ 2 * (t * ‖y‖ ^ 2)) by ring,
    show -Real.pi * t * ‖x‖ ^ 2 = -Real.pi * (t * ‖x‖ ^ 2) by ring]
  exact h

variable [FiniteDimensional ℝ E]

theorem latticeGaussianMass_temperature_stability (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (x y : E) {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hxy : Real.sqrt t * ‖x - y‖ ≤ ε) :
    Real.exp (-4 * Real.pi) * latticeGaussianMass Λ (t * (1 + ε) ^ 2) y ≤
      latticeGaussianMass Λ t x := by
  unfold latticeGaussianMass
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    ((lattice_gaussian_summable Λ (mul_pos ht (sq_pos_of_pos (by linarith))) y).mul_left _)
    (lattice_gaussian_summable Λ ht x)
  intro m
  apply gaussian_perturbation_at_temperature _ _ ht.le hε hεone
  simpa only [sub_sub_sub_cancel_right] using hxy

theorem latticeGaussianMass_temperature_orbit_stability (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (α β : E) {N k : ℕ} {t ε : ℝ}
    (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hclose : Real.sqrt t * ((N : ℝ) ^ k * ‖α - β‖) ≤ ε)
    (n : ℤ) (hn : |n| ≤ (N : ℤ)) :
    Real.exp (-4 * Real.pi) * latticeGaussianMass Λ (t * (1 + ε) ^ 2) ((n : ℝ) ^ k • β) ≤
      latticeGaussianMass Λ t ((n : ℝ) ^ k • α) := by
  apply latticeGaussianMass_temperature_stability Λ _ _ ht hε hεone
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_pow]
  have hnR : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hn
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hnR k) (norm_nonneg _)) (Real.sqrt_nonneg t)).trans hclose

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtHyperplaneTransfer
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem monomial_smul_sub_mem_lattice (Λ : Submodule ℤ E) {x y : E}
    (hxy : x - y ∈ Λ) (n : ℤ) (k : ℕ) :
    (n : ℝ) ^ k • x - (n : ℝ) ^ k • y ∈ Λ := by
  rw [← smul_sub, ← Int.cast_pow, Int.cast_smul_eq_zsmul]
  exact Λ.smul_mem (n ^ k) hxy

theorem exists_schmidt_hyperplane_transfer_at_temperature (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (ξ : E) (hξ : ξ ≠ 0) (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    (α : E) {N k : ℕ} {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hsmall : Real.sqrt t * ((N : ℝ) ^ k *
      (CircleFourier.integerDistance ((inner ℝ ξ α : ℝ) : CircleFourier.Circle) / ‖ξ‖)) ≤ ε) :
    ∃ β : (normalFunctional ξ).ker, ∀ n : ℤ, |n| ≤ (N : ℤ) →
      Real.exp (-4 * Real.pi) *
          latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ)) (t * (1 + ε) ^ 2)
            ((n : ℝ) ^ k • β) ≤
        latticeGaussianMass Λ t ((n : ℝ) ^ k • α) := by
  obtain ⟨γ, β, hγβ, herror⟩ := exists_corrected_hyperplane_representative Λ ξ hξ w hwΛ hw α
  have hclose : Real.sqrt t * ((N : ℝ) ^ k * ‖α - γ‖) ≤ ε := by
    rw [norm_sub_rev, herror]
    exact hsmall
  refine ⟨β, ?_⟩
  intro n hn
  have htransfer := latticeGaussianMass_hyperplane_translate_le Λ (normalFunctional ξ)
    (t := t * (1 + ε) ^ 2)
    (mul_pos ht (sq_pos_of_pos (by linarith))) ((n : ℝ) ^ k • γ) ((n : ℝ) ^ k • β)
    (monomial_smul_sub_mem_lattice Λ hγβ n k)
  exact (mul_le_mul_of_nonneg_left htransfer (Real.exp_pos _).le).trans
    (latticeGaussianMass_temperature_orbit_stability Λ α γ ht hε hεone hclose n hn)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeHyperplane_covolume_sq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) :
    ZLattice.covolume Λ ^ 2 =
      ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) ^ 2 * (‖ξ‖⁻¹) ^ 2 := by
  classical
  let f := normalFunctional ξ
  let K := latticeHyperplane Λ f
  let : IsZLattice ℝ K := latticeHyperplane_isZLattice Λ f hint w hwΛ hw
  let bK := Module.Free.chooseBasis ℤ K
  let b := latticeHyperplaneBasis Λ f hint w hwΛ hw bK
  let bR := b.ofZLatticeBasis ℝ Λ
  let bKR := bK.ofZLatticeBasis ℝ K
  have hinl (i) : bR (Sum.inl i) = (bKR i : E) := by
    simpa only [bR, bKR, Module.Basis.ofZLatticeBasis_apply, b] using
      latticeHyperplaneBasis_inl Λ f hint w hwΛ hw bK i
  have hinr (j : Unit) : bR (Sum.inr j) = w := by
    simpa only [bR, Module.Basis.ofZLatticeBasis_apply, b] using
      latticeHyperplaneBasis_inr Λ f hint w hwΛ hw bK j
  have hspan : Submodule.span ℝ (Set.range (fun i => bR (Sum.inl i))) = f.ker := by
    rw [show (fun i => bR (Sum.inl i)) = (fun i => (bKR i : E)) from funext hinl]
    change Submodule.span ℝ (Set.range (f.ker.subtype ∘ bKR)) = _
    rw [Set.range_comp, ← Submodule.map_span, bKR.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hkernel : (Matrix.gram ℝ (fun i => bR (Sum.inl i))).det = ZLattice.covolume K ^ 2 := by
    have he : Matrix.gram ℝ (fun i => bR (Sum.inl i)) = Matrix.gram ℝ bKR := by
      ext i j
      simp only [Matrix.gram_apply, hinl]
      rfl
    rw [he]
    exact (lattice_covolume_sq_eq_gram K bK).symm
  have hblock := gram_det_orthogonal_block bR
  dsimp only at hblock
  rw [hspan, hkernel, Matrix.det_unique (n := Unit), Matrix.gram_apply, hinr,
    real_inner_self_eq_norm_sq, normalHyperplane_height ξ w hξ hw] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  exact hblock

theorem latticeHyperplane_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) :
    ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) =
      ‖ξ‖ * ZLattice.covolume Λ := by
  let := latticeHyperplane_isZLattice Λ (normalFunctional ξ) hint w hwΛ hw
  have h := latticeHyperplane_covolume_sq Λ ξ hξ hint w hwΛ hw
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hc := ZLattice.covolume_pos Λ MeasureTheory.volume
  have hk := ZLattice.covolume_pos (latticeHyperplane Λ (normalFunctional ξ)) MeasureTheory.volume
  have hs : (‖ξ‖ * ZLattice.covolume Λ) ^ 2 =
      ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) ^ 2 := by
    rw [mul_pow, h]
    field_simp
  nlinarith [mul_pos hn hc]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

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

theorem latticeGaussianNormalizer_hyperplane (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ 1 + ε) :
    Real.sqrt t * latticeGaussianNormalizer (latticeHyperplane Λ (normalFunctional ξ))
        (t * (1 + ε) ^ 2) =
      ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
        latticeGaussianNormalizer Λ t := by
  unfold latticeGaussianNormalizer
  rw [Real.sqrt_mul ht, Real.sqrt_sq hε,
    latticeHyperplane_covolume Λ ξ hξ hint w hwΛ hw,
    ← hyperplane_finrank (normalFunctional ξ) w hw, pow_succ, mul_pow]
  ring

theorem normalizedLatticeGaussian_transfer (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    {t ε c : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ 1 + ε)
    (x : E) (y : (normalFunctional ξ).ker)
    (htransfer : c * latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ))
      (t * (1 + ε) ^ 2) y ≤ latticeGaussianMass Λ t x) :
    c * Real.sqrt t * normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
        (t * (1 + ε) ^ 2) y ≤
      ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
        normalizedLatticeGaussian Λ t x := by
  have h := mul_le_mul_of_nonneg_left htransfer
    (mul_nonneg (mul_nonneg (norm_nonneg ξ)
      (pow_nonneg hε (Module.finrank ℝ (normalFunctional ξ).ker)))
      (latticeGaussianNormalizer_nonneg Λ t))
  have hid := latticeGaussianNormalizer_hyperplane Λ ξ hξ hint w hwΛ hw ht hε
  unfold normalizedLatticeGaussian
  calc
    _ = (Real.sqrt t * latticeGaussianNormalizer (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2)) *
        (c * latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2) y) := by ring
    _ = (‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
          latticeGaussianNormalizer Λ t) *
        (c * latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2) y) := by rw [hid]
    _ ≤ _ := by simpa only [mul_assoc] using h

theorem exists_normalized_schmidt_hyperplane_transfer (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    (α : E) {N k : ℕ} {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hsmall : Real.sqrt t * ((N : ℝ) ^ k *
      (CircleFourier.integerDistance ((inner ℝ ξ α : ℝ) : CircleFourier.Circle) / ‖ξ‖)) ≤ ε) :
    ∃ β : (normalFunctional ξ).ker, ∀ n : ℤ, |n| ≤ (N : ℤ) →
      Real.exp (-4 * Real.pi) * Real.sqrt t *
          normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
            (t * (1 + ε) ^ 2) ((n : ℝ) ^ k • β) ≤
        ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
          normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α) := by
  obtain ⟨β, hβ⟩ := exists_schmidt_hyperplane_transfer_at_temperature Λ ξ hξ w hwΛ hw
    α ht hε hεone hsmall
  exact ⟨β, fun n hn => normalizedLatticeGaussian_transfer Λ ξ hξ hint w hwΛ hw ht.le
    (by linarith) _ _ (hβ n hn)⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem latticeGaussianMass_antitone (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : E) :
    latticeGaussianMass Λ t x ≤ latticeGaussianMass Λ s x := by
  apply (lattice_gaussian_summable Λ (hs.trans_le hst) x).tsum_le_tsum
    _ (lattice_gaussian_summable Λ hs x)
  intro m
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonpos_left hst (neg_nonpos.mpr Real.pi_pos.le)) (sq_nonneg _)

theorem normalizedLatticeGaussian_hyperplane_origin_le (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) :
    Real.sqrt t * normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
        (t * (1 + ε) ^ 2) 0 ≤
      ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker *
        normalizedLatticeGaussian Λ t 0 := by
  have htemp : t ≤ t * (1 + ε) ^ 2 := by nlinarith [mul_nonneg ht.le (sq_nonneg ε)]
  have hmass := (latticeGaussianMass_antitone (latticeHyperplane Λ (normalFunctional ξ))
    ht htemp 0).trans (latticeGaussianMass_hyperplane_le Λ (normalFunctional ξ) ht 0)
  simpa only [one_mul] using normalizedLatticeGaussian_transfer Λ ξ hξ hint w hwΛ hw
    ht.le (by linarith) 0 0 (c := 1) (by simpa only [one_mul, Submodule.coe_zero] using hmass)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module _root_.Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module _root_.Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtGaussianMean
namespace OAI

section

namespace Erdos3

theorem one_add_pow_le_exp_one {r : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hbudget : (r : ℝ) * ε ≤ 1) : (1 + ε) ^ r ≤ Real.exp 1 := by
  calc
    _ ≤ (Real.exp ε) ^ r := pow_le_pow_left₀ (by linarith)
      (by simpa only [add_comm] using Real.add_one_le_exp ε) _
    _ = Real.exp ((r : ℝ) * ε) := (Real.exp_nat_mul ε r).symm
    _ ≤ _ := Real.exp_le_exp.mpr hbudget

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianMean_nonneg (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) :
    0 ≤ latticeGaussianMean Λ t k α N := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun _ _ => normalizedLatticeGaussian_nonneg Λ t _

theorem latticeGaussianMean_transfer
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (Λ : Submodule ℤ E) (Γ : Submodule ℤ F) (t s c C : ℝ) (k : ℕ) (α : E) (β : F) (N : ℕ)
    (h : ∀ n : ℤ, |n| ≤ (N : ℤ) →
      c * normalizedLatticeGaussian Γ s ((n : ℝ) ^ k • β) ≤
        C * normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α)) :
    c * latticeGaussianMean Γ s k β N ≤ C * latticeGaussianMean Λ t k α N := by
  unfold latticeGaussianMean
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun n hn => h n (abs_le.mpr (Finset.mem_Icc.mp hn))

theorem exists_schmidt_gaussian_mean_transfer (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0) (hξdual : ξ ∈ euclideanDualLattice Λ)
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    (α : E) {N k : ℕ} {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hbudget : (Module.finrank ℝ (normalFunctional ξ).ker : ℝ) * ε ≤ 1)
    (hsmall : Real.sqrt t * ((N : ℝ) ^ k *
      (CircleFourier.integerDistance ((inner ℝ ξ α : ℝ) : CircleFourier.Circle) / ‖ξ‖)) ≤ ε) :
    ∃ β : (normalFunctional ξ).ker,
      Real.exp (-4 * Real.pi) * Real.sqrt t *
          latticeGaussianMean (latticeHyperplane Λ (normalFunctional ξ))
            (t * (1 + ε) ^ 2) k β N ≤
        Real.exp 1 * ‖ξ‖ * latticeGaussianMean Λ t k α N ∧
      Real.sqrt t * normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2) 0 ≤
        Real.exp 1 * ‖ξ‖ * normalizedLatticeGaussian Λ t 0 := by
  have hint := (mem_euclideanDualLattice Λ ξ).mp hξdual
  obtain ⟨β, hβ⟩ := exists_normalized_schmidt_hyperplane_transfer Λ ξ hξ hint w hwΛ hw
    α ht hε hεone hsmall
  have hfactor : ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker ≤
      Real.exp 1 * ‖ξ‖ := by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (one_add_pow_le_exp_one hε hbudget) (norm_nonneg ξ)
  refine ⟨β, ?_, ?_⟩
  · exact (latticeGaussianMean_transfer Λ _ _ _ _ _ k α β N hβ).trans
      (mul_le_mul_of_nonneg_right hfactor (latticeGaussianMean_nonneg Λ t k α N))
  · exact (normalizedLatticeGaussian_hyperplane_origin_le Λ ξ hξ hint w hwΛ hw ht hε).trans
      (mul_le_mul_of_nonneg_right hfactor (normalizedLatticeGaussian_nonneg Λ t 0))

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

variable [FiniteDimensional ℝ E]

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

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

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

theorem exists_schmidt_dilated_mean_transfer
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
  obtain ⟨β, hmean, hmass⟩ := exists_schmidt_gaussian_mean_transfer Λ ζ hζ hζdual w hwΛ hw
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

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Polynomial

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

universe u

open Polynomial

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.exists_schmidt_dilated_mean_transfer.{u_1} := @OAI.Erdos3.exists_schmidt_dilated_mean_transfer.{u_1}
