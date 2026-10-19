-- Prove2me | solution 1 for OAI.DirectCrouzeix.uniform_sharpness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:53:24.65819+00:00
-- url     : https://prove2.me/submissions/ce83c7cf-5e5d-4d98-8c50-01efe818d864

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Sharpness.lean:L75-L89
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.DirectCrouzeix.uniform_sharpness.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_DirectCrouzeix_uniform_sharpness) verbatim and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness

-- ---- from OAI.Analysis.DirectCrouzeix.NumericalRange ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

theorem numericalRange_eq_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRange A =
      (fun u : EuclideanSpace ℂ (Fin n) => inner ℂ u
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)) '' Metric.sphere 0 1 := by
  ext z
  simp [numericalRange, Set.mem_image]

theorem isCompact_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    IsCompact (numericalRange A) := by
  rw [numericalRange_eq_image]
  exact (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1).image
    (continuous_id.inner (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).continuous)

theorem numericalRange_nonempty {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : (numericalRange A).Nonempty := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [numericalRange_eq_image]
  exact (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _

theorem continuous_polynomialValue {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : Continuous (polynomialValue B) := by
  unfold polynomialValue
  exact continuous_finsetSum _ (fun k _ => (continuous_id.pow _).smul continuous_const)

theorem rangeMaximum_attained {n m d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    ∃ z ∈ numericalRange A, ‖polynomialValue B z‖ = rangeMaximum A B := by
  have hc := (isCompact_numericalRange A).image (continuous_polynomialValue B).norm
  have hne := (numericalRange_nonempty hn A).image (fun z => ‖polynomialValue B z‖)
  obtain ⟨z, hz, he⟩ := hc.sSup_mem hne
  exact ⟨z, hz, he⟩

open scoped MatrixOrder ComplexOrder

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.Sharpness ----
namespace OAI

universe u_46

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem norm_entry_le_l2_opNorm {ι : Type u_46} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ ι := EuclideanSpace.single j 1
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  have he : ‖e‖ = 1 := by simp [e]
  have hij : (T e) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    ‖A i j‖ = ‖(T e) i‖ := congrArg norm hij.symm
    _ ≤ ‖T e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm _
    _ = ‖A‖ := by simp [T, he, Matrix.l2_opNorm_toEuclideanCLM]

theorem norm_le_one_of_mem_sharpnessRange {z : ℂ}
    (hz : z ∈ numericalRange sharpnessMatrix) : ‖z‖ ≤ 1 := by
  obtain ⟨u, hu, rfl⟩ := hz
  have hsum : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = 1 := by
    simpa [hu, Fin.sum_univ_two] using (EuclideanSpace.norm_sq_eq u).symm
  have hev : inner ℂ u
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) sharpnessMatrix u) =
      2 * star (u 0) * u 1 := by
    simp [sharpnessMatrix, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toEuclideanCLM, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  rw [hev]
  simp only [norm_mul, norm_star]
  norm_num
  nlinarith [sq_nonneg (‖u 0‖ - ‖u 1‖)]

theorem sharpness_rangeMaximum_le_one :
    rangeMaximum (d := 1) sharpnessMatrix sharpnessCoefficients ≤ 1 := by
  obtain ⟨z, hz, he⟩ := rangeMaximum_attained (by norm_num : 0 < 2)
    sharpnessMatrix (d := 1) sharpnessCoefficients
  rw [← he, sharpness_polynomialValue, norm_smul, norm_one, mul_one]
  exact norm_le_one_of_mem_sharpnessRange hz

theorem sharpness_tensor_norm_ge_two :
    2 ≤ ‖tensorEvaluation (d := 1) sharpnessMatrix sharpnessCoefficients‖ := by
  have h := norm_entry_le_l2_opNorm
    (sharpnessMatrix ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) (0, 0) (1, 0)
  rw [sharpness_tensorEvaluation]
  simpa [sharpnessMatrix, Matrix.kroneckerMap_apply] using h

theorem uniform_sharpness (c : ℝ) (hc : UniversalBound c) : 2 ≤ c := by
  have hmain := hc 2 1 1 (by norm_num) (by norm_num) sharpnessMatrix sharpnessCoefficients
  have hmax := sharpness_rangeMaximum_le_one
  have hlower := sharpness_tensor_norm_ge_two
  have hnonneg : 0 ≤ rangeMaximum (d := 1) sharpnessMatrix sharpnessCoefficients := by
    obtain ⟨z, hz, he⟩ := rangeMaximum_attained (by norm_num : 0 < 2)
      sharpnessMatrix (d := 1) sharpnessCoefficients
    rw [← he]
    exact norm_nonneg _
  have hcpos : 0 ≤ c := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hn) hnonneg
    linarith
  have hmul := mul_le_mul_of_nonneg_left hmax hcpos
  linarith

end DirectCrouzeix

end

end OAI

-- ---- mission target ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory

namespace OAI
namespace DirectCrouzeix
theorem _root_.solution (c : ℝ) (hc : UniversalBound c) : 2 ≤ c := by
  first
    | exact OAI.DirectCrouzeix.uniform_sharpness c hc
    | exact OAI.DirectCrouzeix.uniform_sharpness
    | (apply OAI.DirectCrouzeix.uniform_sharpness <;> assumption)
    | (intros; apply OAI.DirectCrouzeix.uniform_sharpness <;> assumption)
end DirectCrouzeix
end OAI
