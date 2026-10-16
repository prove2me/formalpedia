-- Prove2me | solution 1 for OAI.Paper256.posSemidef_norm_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:52:12.72359+00:00
-- url     : https://prove2.me/submissions/333c27f8-51ba-485a-a0e8-5831326321e3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/NormThreshold.lean:L22-L35
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.posSemidef_norm_threshold. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Definitions.Def_OAI_Analysis_HyperbolicCones_GramProjection
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSmooth
import Definitions.Def_OAI_Analysis_HyperbolicCones_TangentBasic

-- ---- from OAI.Analysis.HyperbolicCones.InverseOrder ----
namespace OAI

/-! Simultaneous spectral comparison of a positive matrix and its scalar shifts. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem matrix_cfc_affine {n : ℕ} (H : Sym n) (a b : ℝ) :
    cfc (fun x : ℝ => a + b * x) (H : Mat n ℝ) =
      a • (1 : Mat n ℝ) + b • (H : Mat n ℝ) := by
  calc
    _ = algebraMap ℝ (Mat n ℝ) a + cfc (fun x : ℝ => b * x) (H : Mat n ℝ) :=
      cfc_const_add a (fun x : ℝ => b * x) (H : Mat n ℝ)
        (H.val.finite_real_spectrum.continuousOn _) H.property
    _ = _ := by
      have hmul : cfc (fun x : ℝ => b * x) (H : Mat n ℝ) = b • (H : Mat n ℝ) :=
        cfc_const_mul_id b (H : Mat n ℝ) H.property
      rw [hmul, Algebra.algebraMap_eq_smul_one]

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.NormThreshold ----
namespace OAI

/-! The exact scalar threshold of a positive semidefinite matrix. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem posSemidef_scalar_sub_iff {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian) (r : ℝ) :
    (r • (1 : Mat n ℝ) - A).PosSemidef ↔ ∀ x ∈ spectrum ℝ A, x ≤ r := by
  let H : Sym n := ⟨A, hA⟩
  have hshift : cfc (fun x : ℝ => r - x) A = r • (1 : Mat n ℝ) - A := by
    simpa only [neg_one_mul, neg_one_smul, sub_eq_add_neg] using matrix_cfc_affine H r (-1)
  rw [← Matrix.nonneg_iff_posSemidef, ← hshift]
  have h := cfc_nonneg_iff (fun x : ℝ => r - x) A
    (A.finite_real_spectrum.continuousOn _) hA
  simpa only [sub_nonneg] using h

theorem posSemidef_norm_threshold {n : ℕ} [NeZero n] (A : Mat n ℝ)
    (hA : A.PosSemidef) (r : ℝ) :
    (r • (1 : Mat n ℝ) - A).PosSemidef ↔ ‖A‖ ≤ r := by
  rw [posSemidef_scalar_sub_iff A hA.isHermitian r]
  have hgreat := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (p := IsSelfAdjoint) A hA.isHermitian
  constructor
  · intro h
    obtain ⟨x, hx, hnorm⟩ := hgreat.1
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
    calc
      ‖A‖ = x := by simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hnorm.symm
      _ ≤ r := h x hx
  · intro h x hx
    exact (le_abs_self x).trans ((hgreat.2 ⟨x, hx, rfl⟩).trans h)

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.Paper256.posSemidef_norm_threshold := @_root_.OAI.Paper256.posSemidef_norm_threshold
