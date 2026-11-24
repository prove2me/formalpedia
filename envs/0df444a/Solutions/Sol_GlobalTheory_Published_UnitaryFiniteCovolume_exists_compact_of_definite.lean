-- Prove2me | solution 1 for GlobalTheory.Published.UnitaryFiniteCovolume.exists_compact_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:39:52.591703+00:00
-- url     : https://prove2.me/submissions/e7cf1efa-0bf1-4ae9-a813-1b32ff5a3d6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_DefiniteCompactness_ExistsCompactOfDefinite
import Theorems.Thm_P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.UnitaryFiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Published.UnitaryFiniteCovolume
theorem _root_.solution {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r) (τ : X.Ψ) :
    ∃ K : Set (Matrix (Fin r) (Fin r) ℂ), IsCompact K ∧ ∀ g : Matrix (Fin r) (Fin r) ℂ,
      (∀ u w, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ w) = hermC τ.1 X.Gm u w) → g ∈ K := by
  obtain ⟨P, hP, hg⟩ := X.signature τ
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  obtain ⟨ε, hε, hg'⟩ : ∃ ε : ℂ, ε ≠ 0 ∧ gram τ.1 X.Gm P = ε • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rcases hd with h | h
    · refine ⟨-1, by simp, ?_⟩
      rw [hg, h]
      ext a b
      by_cases hab : a = b <;> simp [sgn, hab]
    · refine ⟨1, by simp, ?_⟩
      rw [hg, h]
      ext a b
      by_cases hab : a = b <;> simp [sgn, hab]
  refine ⟨(fun V : Matrix (Fin r) (Fin r) ℂ => P * V.map (starRingEnd ℂ) * P⁻¹) ''
    (Matrix.unitaryGroup (Fin r) ℂ : Set (Matrix (Fin r) (Fin r) ℂ)), ?_, fun g h => ?_⟩
  · refine (GlobalTheory.isCompact_unitaryGroup (Fin r) ℂ).image ?_
    exact (continuous_const.matrix_mul
      (continuous_id.matrix_map Complex.continuous_conj)).matrix_mul continuous_const
  · set U : Matrix (Fin r) (Fin r) ℂ := P⁻¹ * g * P with hU
    have hPU : P * U = g * P := by
      rw [hU, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    have h1 : gram τ.1 X.Gm (g * P) = gram τ.1 X.Gm P := by
      ext a b
      simp only [gram, Matrix.of_apply, GlobalTheory.UnitaryFrames.col_mul', h]
    have h2 : gram τ.1 X.Gm (P * U) = Uᵀ * (gram τ.1 X.Gm P * U.map (starRingEnd ℂ)) := by
      simp only [GlobalTheory.UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul,
        Matrix.mul_assoc]
    rw [hPU, h1, hg', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul] at h2
    have h3 : Uᵀ * U.map (starRingEnd ℂ) = 1 := (smul_right_injective _ hε h2).symm
    have hcc : (U.map (starRingEnd ℂ)).map (starRingEnd ℂ) = U := by
      ext a b
      simp
    refine ⟨U.map (starRingEnd ℂ), ?_, ?_⟩
    · refine Matrix.mem_unitaryGroup_iff'.2 ?_
      rw [← h3]
      congr 1
      ext a b
      simp [Matrix.star_apply]
    · simp only [hcc]
      rw [hPU, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
end GlobalTheory.Published.UnitaryFiniteCovolume
