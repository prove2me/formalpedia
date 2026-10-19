-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.Resolvent.weighted_distance_jensen
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:33:14.089988+00:00
-- url     : https://prove2.me/submissions/beeb11e7-4666-4f50-a62c-73933462698c

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SpectralEntropy.lean:L321-L348
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.Resolvent.weighted_distance_jensen. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Theorems.Thm_OAI_ThresholdParallelRepetition_Resolvent_scalar_entropy_integral

-- ---- from OAI.Probability.EntangledGames.Resolvent ----
namespace OAI

universe u_n u_J

open scoped BigOperators ComplexOrder

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.Resolvent

variable {n : Type u_n} [Fintype n] [DecidableEq n]

omit [Fintype n] in

lemma shift_posDef {A : Matrix n n ℂ} (hA : A.PosSemidef) {s : ℝ} (hs : 0 < s) :
    (A + s • (1 : Matrix n n ℂ)).PosDef := by
  simpa only [add_comm] using ((Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hs).add_posSemidef hA

lemma second_resolvent_identity (A B : Matrix n n ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹ = B⁻¹ - B⁻¹ * (A - B) * B⁻¹ +
      B⁻¹ * (A - B) * A⁻¹ * (A - B) * B⁻¹ := by
  have h₁ : B⁻¹ - A⁻¹ = B⁻¹ * (A - B) * A⁻¹ :=
    Matrix.inv_sub_inv (by simp [hA, hB])
  have h₂ : A⁻¹ - B⁻¹ = -(A⁻¹ * (A - B) * B⁻¹) := by
    rw [Matrix.inv_sub_inv (by simp [hA, hB]), ← neg_sub A B, mul_neg, neg_mul]
  rw [← h₁]
  calc
    A⁻¹ = B⁻¹ - A⁻¹ * (A - B) * B⁻¹ := by
      apply sub_eq_iff_eq_add.mp at h₂
      simpa only [sub_eq_add_neg, add_comm] using h₂
    _ = B⁻¹ - B⁻¹ * (A - B) * B⁻¹ +
        (B⁻¹ - A⁻¹) * (A - B) * B⁻¹ := by noncomm_ring

lemma resolvent_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : (resolvent A s).PosSemidef :=
  (shift_posDef hA hs).posSemidef.inv

lemma resolvent_mul_shift {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : resolvent A s * (A + s • 1) = 1 := by
  exact Matrix.nonsing_inv_mul _ ((shift_posDef hA hs).isUnit.map Matrix.detMonoidHom)

lemma shift_mul_resolvent {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : (A + s • 1) * resolvent A s = 1 := by
  exact Matrix.mul_nonsing_inv _ ((shift_posDef hA hs).isUnit.map Matrix.detMonoidHom)

lemma purificationKernel_eq {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : purificationKernel A s = 1 - s • resolvent A s := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_mul, smul_mul_assoc, one_mul, purificationKernel] using
    shift_mul_resolvent hA hs

lemma resolvent_mul_eq {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) : resolvent A s * A = 1 - s • resolvent A s := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [mul_add, mul_smul_comm, mul_one] using resolvent_mul_shift hA hs

lemma resolvent_square_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    s • (resolvent A s * resolvent A s) ≤ resolvent A s := by
  rw [Matrix.le_iff]
  have hp := hA.conjTranspose_mul_mul_same (resolvent A s)
  rw [(resolvent_posSemidef hA hs).isHermitian.eq, resolvent_mul_eq hA hs,
    sub_mul, one_mul, smul_mul_assoc] at hp
  exact hp

lemma purificationKernel_sub {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ} (hs : 0 < s) :
    purificationKernel A s - purificationKernel B s =
      s • (resolvent A s * (A - B) * resolvent B s) := by
  rw [purificationKernel_eq hA hs, purificationKernel_eq hB hs]
  have h : resolvent A s - resolvent B s =
      -(resolvent A s * (A - B) * resolvent B s) := by
    dsimp only [resolvent]
    rw [Matrix.inv_sub_inv (by simp [(shift_posDef hA hs).isUnit,
      (shift_posDef hB hs).isUnit])]
    rw [add_sub_add_right_eq_sub, ← neg_sub A B, mul_neg, neg_mul]
  calc
    _ = -(s • (resolvent A s - resolvent B s)) := by module
    _ = _ := by rw [h, smul_neg, neg_neg]

lemma purificationKernel_square_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {s : ℝ} (hs : 0 < s) :
    (purificationKernel A s - purificationKernel B s)ᴴ *
      (purificationKernel A s - purificationKernel B s) ≤
      s • (resolvent B s * (A - B) * resolvent A s * (A - B) * resolvent B s) := by
  have hRA := (resolvent_posSemidef hA hs).isHermitian.eq
  have hRB := (resolvent_posSemidef hB hs).isHermitian.eq
  have hD := (hA.isHermitian.sub hB.isHermitian).eq
  have hp := ((Matrix.le_iff.mp (resolvent_square_le hA hs)).conjTranspose_mul_mul_same
    ((A - B) * resolvent B s)).smul hs.le
  rw [Matrix.le_iff, purificationKernel_sub hA hB hs]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial,
    hRA, hRB, hD] at hp ⊢
  simp only [smul_sub, Matrix.mul_sub, Matrix.sub_mul,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc] at hp ⊢
  convert hp using 1
  first | rfl | module

lemma weighted_resolvent_identity {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    ∑ j, w j • (resolvent (A j) s - resolvent B s) =
      ∑ j, w j • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s) := by
  have hlinear : ∑ j, w j • (A j - B) = 0 := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, hmean, ← Finset.sum_smul, hw, one_smul, sub_self]
  have hzero : ∑ j, w j • (resolvent B s * (A j - B) * resolvent B s) = 0 := by
    calc
      _ = resolvent B s * (∑ j, w j • (A j - B)) * resolvent B s := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_smul_comm, smul_mul_assoc]
      _ = 0 := by rw [hlinear, mul_zero, zero_mul]
  have hsecond (j : J) : resolvent (A j) s =
      resolvent B s - resolvent B s * (A j - B) * resolvent B s +
        resolvent B s * (A j - B) * resolvent (A j) s * (A j - B) * resolvent B s := by
    simpa only [resolvent, add_sub_add_right_eq_sub] using
      second_resolvent_identity (A j + s • 1) (B + s • 1)
        (shift_posDef (hA j) hs).isUnit (shift_posDef hB hs).isUnit
  have heq (j : J) : resolvent (A j) s - resolvent B s =
      -(resolvent B s * (A j - B) * resolvent B s) +
        resolvent B s * (A j - B) * resolvent (A j) s * (A j - B) * resolvent B s := by
    rw [sub_eq_iff_eq_add]
    calc
      _ = _ := hsecond j
      _ = _ := by abel
  simp_rw [heq, smul_add, smul_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hzero, neg_zero, zero_add]

lemma weighted_kernel_square_le {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw0 : ∀ j, 0 ≤ w j) (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    ∑ j, w j • ((purificationKernel (A j) s - purificationKernel B s)ᴴ *
      (purificationKernel (A j) s - purificationKernel B s)) ≤
    s • ∑ j, w j • (resolvent (A j) s - resolvent B s) := by
  calc
    _ ≤ ∑ j, w j • (s • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s)) := by
      exact Finset.sum_le_sum fun j _ => smul_le_smul_of_nonneg_left
        (purificationKernel_square_le (hA j) hB hs) (hw0 j)
    _ = s • ∑ j, w j • (resolvent B s * (A j - B) * resolvent (A j) s *
        (A j - B) * resolvent B s) := by
      simp only [Finset.smul_sum, smul_smul, mul_comm (w _) s]
    _ = _ := by rw [weighted_resolvent_identity A w B hA hB hw hmean hs]

end ThresholdParallelRepetition.Resolvent

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ThresholdParallelRepetition.Resolvent

end ThresholdParallelRepetition.Resolvent

end
end

end OAI

-- ---- from OAI.Probability.EntangledGames.SpectralEntropy ----
namespace OAI

universe u_n u_α u_m u_p u_r u_J

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix MeasureTheory Set
namespace ThresholdParallelRepetition.Resolvent
variable {n : Type u_n} [Fintype n] [DecidableEq n]

attribute [local instance] OAI.ThresholdParallelRepetition.Resolvent.matrixContinuousENorm
attribute [local instance] OAI.ThresholdParallelRepetition.Resolvent.matrixPreorder
attribute [local instance] OAI.ThresholdParallelRepetition.Resolvent.matrixClosedIci
lemma integral_matrix_mono {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {f g : α → Matrix n n ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : f ≤ᵐ[μ] g) : (∫ s, f s ∂μ) ≤ ∫ s, g s ∂μ :=
  @integral_mono_ae α (Matrix n n ℂ) _ _ _ μ _ _ _ matrixClosedIci f g hf hg hfg

lemma integrable_cfc {α : Type u_α} [MeasurableSpace α] {μ : Measure α}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : α → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun s => f s (hA.eigenvalues i)) μ) :
    Integrable (fun s => cfc (f s) A) μ := by
  simp_rw [cfc_eq_spectralLinear hA]
  exact (spectralLinear _).integrable_comp (Integrable.of_eval hf)

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma eigenvalues_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : A ≤ 1) (i : n) : hA.isHermitian.eigenvalues i ≤ 1 := by
  have h : cfc (fun t : ℝ => t) A ≤ cfc (fun _ : ℝ => (1 : ℝ)) A := by
    erw [cfc_id' ℝ A hA.isHermitian, cfc_const (1 : ℝ) A hA.isHermitian,
      map_one]
    exact hA1
  exact (cfc_le_iff (fun t : ℝ => t) (fun _ : ℝ => (1 : ℝ)) A
    (ha := hA.isHermitian)).mp h _ (hA.isHermitian.eigenvalues_mem_spectrum_real i)

lemma entropyIntegrand_cfc {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    entropyIntegrand A s = cfc (fun t : ℝ => t / (1 + s) - t / (t + s)) A := by
  rw [entropyIntegrand, purificationKernel_cfc hA hs,
    cfc_sub (fun t : ℝ => t / (1 + s)) (fun t : ℝ => t / (t + s)) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  congr 1
  calc
    _ = cfc (fun t : ℝ => (1 / (1 + s)) • t) A := by
      erw [cfc_smul (1 / (1 + s) : ℝ) (fun t : ℝ => t) A,
        cfc_id' ℝ A hA.isHermitian]
    _ = _ := by apply cfc_congr; intro t _; simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma entropy_integrable {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    IntegrableOn (entropyIntegrand A) (Ioi 0) := by
  have hi := integrable_cfc hA.isHermitian
    (fun (s t : ℝ) => t / (1 + s) - t / (t + s))
    (fun i => (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).1)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (entropyIntegrand_cfc hA hs).symm

lemma entropy_integral {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    (∫ s : ℝ in Ioi 0, entropyIntegrand A s) = effectEntropy A := by
  calc
    _ = ∫ s : ℝ in Ioi 0, cfc (fun t : ℝ => t / (1 + s) - t / (t + s)) A := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact entropyIntegrand_cfc hA hs
    _ = cfc (fun t : ℝ => ∫ s : ℝ in Ioi 0, t / (1 + s) - t / (t + s)) A :=
      integral_cfc hA.isHermitian _ (fun i =>
        (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).1)
    _ = effectEntropy A := by
      apply cfc_congr
      intro t ht
      rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
      obtain ⟨i, rfl⟩ := ht
      exact (scalar_entropy_integral (hA.eigenvalues_nonneg i) (eigenvalues_le_one hA hA1 i)).2

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]
attribute [local instance] OAI.ThresholdParallelRepetition.Resolvent.rectContinuousENorm
lemma kernel_distance_integrable {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IntegrableOn (fun s : ℝ => (purificationKernel A s - purificationKernel B s)ᴴ *
      (purificationKernel A s - purificationKernel B s)) (Ioi 0) := by
  apply integrable_gram <;> intro i j <;>
    exact (kernel_entry_memLp hA i j).sub (kernel_entry_memLp hB i j)

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma entropy_gap_integrand_eq {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : B.PosSemidef)
    (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B)
    {s : ℝ} (hs : 0 < s) :
    (∑ j, w j • entropyIntegrand (A j) s) - entropyIntegrand B s =
      s • ∑ j, w j • (resolvent (A j) s - resolvent B s) := by
  have hc (c : ℝ) : ∑ j, w j • (c • A j) = c • B := by
    simp_rw [smul_comm (w _) c]
    rw [← Finset.smul_sum, hmean]
  have hone : ∑ j, w j • (1 : Matrix n n ℂ) = 1 := by
    rw [← Finset.sum_smul, hw, one_smul]
  have hr : ∑ j, w j • (s • resolvent (A j) s) = s • ∑ j, w j • resolvent (A j) s := by
    simp_rw [smul_comm (w _) s]
    rw [Finset.smul_sum]
  simp_rw [entropyIntegrand, purificationKernel_eq (hA _) hs, purificationKernel_eq hB hs,
    smul_sub, Finset.sum_sub_distrib]
  rw [hc, hone, hr, ← Finset.sum_smul, hw, one_smul]
  module

lemma weighted_distance_jensen {J : Type u_J} [Fintype J]
    (A : J → Matrix n n ℂ) (w : J → ℝ) (B : Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (hB : B.PosSemidef) (hB1 : B ≤ 1)
    (hw0 : ∀ j, 0 ≤ w j) (hw : ∑ j, w j = 1) (hmean : ∑ j, w j • A j = B) :
    (∑ j, w j • (∫ s : ℝ in Ioi 0,
        (purificationKernel (A j) s - purificationKernel B s)ᴴ *
          (purificationKernel (A j) s - purificationKernel B s))) ≤
      (∑ j, w j • effectEntropy (A j)) - effectEntropy B := by
  have hf (j : J) := (kernel_distance_integrable (hA j) hB).smul (w j)
  have hg (j : J) := (entropy_integrable (hA j) (hA1 j)).smul (w j)
  have hleft := integrable_finsetSum Finset.univ (fun j _ => hf j)
  have hright := (integrable_finsetSum Finset.univ (fun j _ => hg j)).sub
    (entropy_integrable hB hB1)
  have hi := integral_matrix_mono hleft hright (show
      (fun s => ∑ j, w j • ((purificationKernel (A j) s - purificationKernel B s)ᴴ *
        (purificationKernel (A j) s - purificationKernel B s))) ≤ᵐ[volume.restrict (Ioi 0)]
      (fun s => (∑ j, w j • entropyIntegrand (A j) s) - entropyIntegrand B s) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [entropy_gap_integrand_eq A w B hA hB hw hmean hs]
    exact weighted_kernel_square_le A w B hA hB hw0 hw hmean hs)
  erw [integral_finsetSum _ (fun j _ => hf j),
    integral_sub (integrable_finsetSum Finset.univ (fun j _ => hg j))
      (entropy_integrable hB hB1),
    integral_finsetSum _ (fun j _ => hg j)] at hi
  simp only [Pi.smul_apply] at hi
  simp_rw [integral_smul, entropy_integral (hA _) (hA1 _), entropy_integral hB hB1] at hi
  exact hi

end ThresholdParallelRepetition.Resolvent

end
end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.Resolvent
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped BigOperators MatrixOrder ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci


theorem solution.{u_n,u_J} : type_of% @_root_.OAI.ThresholdParallelRepetition.Resolvent.weighted_distance_jensen.{u_n,u_J} := @_root_.OAI.ThresholdParallelRepetition.Resolvent.weighted_distance_jensen.{u_n,u_J}
