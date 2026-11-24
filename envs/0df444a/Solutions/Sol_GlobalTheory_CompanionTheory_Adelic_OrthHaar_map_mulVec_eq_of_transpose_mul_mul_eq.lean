-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.OrthHaar.map_mulVec_eq_of_transpose_mul_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:26.576897+00:00
-- url     : https://prove2.me/submissions/1f34b21e-e9f9-493b-8eac-03ee0e94f1b9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqOfTransposeMulMulEq
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_scale_of_isUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_scale_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_scale_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.OrthHaar
namespace GlobalTheory.CompanionTheory.Adelic.OrthHaar
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
      [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R],
      (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → R)) [μ.IsAddHaarMeasure]
        (B g : Matrix ι ι R), IsUnit B.det → gᵀ * B * g = B →
        μ.map (fun x => g *ᵥ x) = μ := by
  intro R _ _ _ _ _ _ _ _ hsr ι _ _ μ _ B g hB h
  have hg2 : g.det * g.det = 1 := by
    have e := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e
    have e2 : B.det * (g.det * g.det) = B.det * 1 := by linear_combination e
    exact hB.mul_left_cancel e2
  have hg : IsUnit g.det := isUnit_iff_exists_inv.mpr ⟨_, hg2⟩
  have hgt : IsUnit gᵀ.det := by rwa [Matrix.det_transpose]
  have hpos : 0 < scale B := by
    rw [scale_of_isUnit hB]
    exact addEquivAddHaarChar_pos _
  have hsq : scale g ^ 2 = 1 := by
    have e := congrArg scale h
    rw [scale_mul (by rw [Matrix.det_mul]; exact hgt.mul hB) hg, scale_mul hgt hB,
      scale_transpose hsr g hg] at e
    apply mul_left_cancel₀ hpos.ne'
    calc scale B * scale g ^ 2 = scale g * scale B * scale g := by ring
      _ = scale B := e
      _ = scale B * 1 := (mul_one _).symm
  have h1 : scale g = 1 := (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 hsq
  have hmap := addEquivAddHaarChar_smul_map μ (mulVecEquiv g hg)
  rw [← scale_of_isUnit hg, h1, one_smul] at hmap
  exact hmap
end GlobalTheory.CompanionTheory.Adelic.OrthHaar
