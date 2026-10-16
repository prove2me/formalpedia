-- Prove2me | solution 1 for OAI.Paper256.kernelProjection_eq_cfc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:57:03.097304+00:00
-- url     : https://prove2.me/submissions/bb7faadb-d3f4-4a58-84bb-223e0fb963d5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SpectralProjection.lean:L20-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.kernelProjection_eq_cfc. The node keeps its source
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

-- ---- from OAI.Analysis.HyperbolicCones.SpectralProjection ----
namespace OAI

/-! The kernel projection is the zero-eigenvalue spectral projection. -/

noncomputable section

open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace Paper256

theorem matrix_cfc_add {n : ℕ} (H : Sym n) (f g : ℝ → ℝ) :
    cfc (fun x => f x + g x) (H : Mat n ℝ) =
      cfc f (H : Mat n ℝ) + cfc g (H : Mat n ℝ) :=
  cfc_add (H : Mat n ℝ) f g (H.val.finite_real_spectrum.continuousOn f)
    (H.val.finite_real_spectrum.continuousOn g)

theorem kernelProjection_eq_cfc {n : ℕ} (H : Sym n) :
    kernelProjection (H : Mat n ℝ) =
      cfc (fun x : ℝ => if x = 0 then 1 else 0) (H : Mat n ℝ) := by
  let f : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  let P : Mat n ℝ := cfc f (H : Mat n ℝ)
  let G : Mat n ℝ := cfc (fun x : ℝ => x⁻¹) (H : Mat n ℝ)
  have hid : cfc (fun x : ℝ => x) (H : Mat n ℝ) = (H : Mat n ℝ) :=
    cfc_id' ℝ (H : Mat n ℝ) H.property
  have hPP : P * P = P := by
    change cfc f (H : Mat n ℝ) * cfc f (H : Mat n ℝ) = cfc f (H : Mat n ℝ)
    rw [← matrix_cfc_mul H f f]
    apply cfc_congr
    intro x _
    by_cases hx : x = 0 <;> simp [f, hx]
  have hHP : (H : Mat n ℝ) * P = 0 := by
    calc
      _ = cfc (fun x : ℝ => x) (H : Mat n ℝ) * cfc f (H : Mat n ℝ) := by rw [hid]
      _ = cfc (fun x : ℝ => x * f x) (H : Mat n ℝ) := (matrix_cfc_mul H _ _).symm
      _ = cfc (fun _ : ℝ => 0) (H : Mat n ℝ) := by
        apply cfc_congr
        intro x _
        by_cases hx : x = 0 <;> simp [f, hx]
      _ = 0 := cfc_const_zero ℝ (H : Mat n ℝ)
  have hPGH : P + G * (H : Mat n ℝ) = 1 := by
    calc
      _ = cfc f (H : Mat n ℝ) + cfc (fun x : ℝ => x⁻¹ * x) (H : Mat n ℝ) := by
        rw [matrix_cfc_mul H (fun x : ℝ => x⁻¹) (fun x => x), hid]
      _ = cfc (fun x : ℝ => f x + x⁻¹ * x) (H : Mat n ℝ) := (matrix_cfc_add H _ _).symm
      _ = cfc (fun _ : ℝ => 1) (H : Mat n ℝ) := by
        apply cfc_congr
        intro x _
        by_cases hx : x = 0 <;> simp [f, hx]
      _ = 1 := cfc_const_one ℝ (H : Mat n ℝ) H.property
  let φ := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
  have hp : IsStarProjection P := ⟨hPP, IsSelfAdjoint.cfc⟩
  have hrange : (φ P).range = (φ (H : Mat n ℝ)).ker := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change φ (H : Mat n ℝ) (φ P y) = 0
      have hm : φ (H : Mat n ℝ) * φ P = 0 := by
        simpa only [map_mul, map_zero] using congrArg φ hHP
      simpa using congrArg (fun T : Vec n →L[ℝ] Vec n => T y) hm
    · intro hx
      refine ⟨x, ?_⟩
      change φ (H : Mat n ℝ) x = 0 at hx
      have hm : φ P + φ G * φ (H : Mat n ℝ) = 1 := by
        simpa only [map_add, map_mul, map_one] using congrArg φ hPGH
      simpa [hx] using congrArg (fun T : Vec n →L[ℝ] Vec n => T x) hm
  have hproj : φ P = (φ (H : Mat n ℝ)).ker.starProjection := by
    apply (ContinuousLinearMap.IsStarProjection.ext_iff (hp.map φ)
      (isStarProjection_starProjection (U := (φ (H : Mat n ℝ)).ker))).mpr
    rw [Submodule.range_starProjection]
    exact hrange
  apply φ.injective
  change φ (kernelProjection (H : Mat n ℝ)) = φ P
  rw [hproj]
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (kernelProjection (H : Mat n ℝ)) x = _
  rw [kernelProjection, LinearEquiv.apply_symm_apply]
  rfl

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.Paper256.kernelProjection_eq_cfc := @_root_.OAI.Paper256.kernelProjection_eq_cfc
