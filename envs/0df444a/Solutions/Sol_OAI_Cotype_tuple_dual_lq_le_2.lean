-- Prove2me | solution 2 for OAI.Cotype.tuple_dual_lq_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:43:48.766752+00:00
-- url     : https://prove2.me/submissions/8677650e-fefc-4782-b756-98e64445ef98

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/TypeCotypeDuality.lean:L20-L78
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.tuple_dual_lq_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Theorems.Thm_OAI_Cotype_exists_unit_eval_gt

-- ---- from OAI.Analysis.Cotype.TypeCotypeDuality ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem tuple_dual_lq_le {n : ℕ} (φ : Fin n → (X →L[ℝ] ℝ))
    {p q C : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : (q-1)*p = q) (hC : 0 ≤ C)
    (h : ∀ x : Fin n → X, |∑ i, φ i (x i)| ≤ C*(∑ i, ‖x i‖^p)^(1/p)) :
    (∑ i, ‖φ i‖^q)^(1/q) ≤ C := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  let a : Fin n → ℝ := fun i => ‖φ i‖^(q-1)
  let S : ℝ := ∑ i, ‖φ i‖^q
  have ha i : 0 ≤ a i := Real.rpow_nonneg (norm_nonneg _) _
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hap i : (a i)^p = ‖φ i‖^q := by
    dsimp [a]; rw [← Real.rpow_mul (norm_nonneg _), hpq]
  have ham i : a i * ‖φ i‖ = ‖φ i‖^q := by
    by_cases hz : ‖φ i‖ = 0
    · simp [hz, Real.zero_rpow (ne_of_gt hq0)]
    · dsimp [a]
      calc
        _ = ‖φ i‖^(q-1) * ‖φ i‖^(1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))]
          congr 1; ring
  have hb : S ≤ C*S^(1/p) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let A := ∑ i, a i
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
    let δ := ε/(A+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    choose x hx he using (fun i => exists_unit_eval_gt (φ i) (by linarith : ‖φ i‖-δ < ‖φ i‖))
    let y : Fin n → X := fun i => a i • x i
    have hy : (∑ i, ‖y i‖^p)^(1/p) ≤ S^(1/p) := by
      apply Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))
      · apply Finset.sum_le_sum
        intro i _
        rw [← hap]
        apply Real.rpow_le_rpow (norm_nonneg _) _ hp0.le
        simpa [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i)] using
          mul_le_of_le_one_right (ha i) (hx i)
      · positivity
    have hval : (∑ i, φ i (y i)) ≤ C*S^(1/p) :=
      (le_abs_self _).trans ((h y).trans (mul_le_mul_of_nonneg_left hy hC))
    have hδA : δ*A ≤ ε := by
      have hh : δ*(A+1)=ε := by dsimp [δ]; field_simp
      nlinarith
    calc
      S = ∑ i, a i * ‖φ i‖ := by simp only [ham, S]
      _ ≤ ∑ i, (a i * φ i (x i) + δ*a i) := Finset.sum_le_sum (fun i _ => by
        nlinarith [mul_le_mul_of_nonneg_left (show ‖φ i‖ ≤ φ i (x i)+δ by linarith [he i]) (ha i)])
      _ = (∑ i, φ i (y i)) + δ*A := by simp [y, A, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by linarith
  change S^(1/q) ≤ C
  by_cases hz : S = 0
  · rw [hz, Real.zero_rpow (by positivity : (1/q : ℝ) ≠ 0)]; exact hC
  have hS0 : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  have he : 1/q+1/p = 1 := by field_simp [ne_of_gt hp0, ne_of_gt hq0]; nlinarith [hpq]
  have hsprod : S^(1/q)*S^(1/p) = S := by rw [← Real.rpow_add hS0, he, Real.rpow_one]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hS0 (1/p))).mp
  rw [hsprod]
  exact hb

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.tuple_dual_lq_le := @_root_.OAI.Cotype.tuple_dual_lq_le
