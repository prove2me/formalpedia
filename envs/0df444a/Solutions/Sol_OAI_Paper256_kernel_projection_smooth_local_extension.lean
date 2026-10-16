-- Prove2me | solution 1 for OAI.Paper256.kernel_projection_smooth_local_extension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:43:59.027562+00:00
-- url     : https://prove2.me/submissions/464365c0-5edf-43bb-a2da-ab8f4d634c13

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/KernelSmooth.lean:L42-L72
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.kernel_projection_smooth_local_extension. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_exists_smooth_kernel_extension

-- ---- from OAI.Analysis.HyperbolicCones.KernelSmooth ----
namespace OAI

noncomputable section

open scoped ContDiff Matrix.Norms.L2Operator
open Set Matrix ContinuousLinearMap

namespace Paper256

theorem contDiff_outerSym : ContDiff ℝ ∞ (outerSym : Vec 4 → Sym 4) := by
  have hcoord : ContDiff ℝ ∞ (fun v : Vec 4 =>
      fun ij : SymIndex => v ij.val.1 * v ij.val.2) := by
    apply contDiff_pi.mpr
    intro ij
    exact (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := ij.val.1)).mul
      (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := ij.val.2))
  have heq : (outerSym : Vec 4 → Sym 4) = fun v =>
      symmetricCoordinateEquiv.symm (fun ij => v ij.val.1 * v ij.val.2) := by
    funext v
    apply symmetricCoordinateEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [heq]
  exact symmetricCoordinateEquiv.symm.toContinuousLinearEquiv.contDiff.comp hcoord

theorem contDiff_kernelFamily (c : ℕ) (E : Sym 4 →ₗ[ℝ] Sym c) :
    ContDiff ℝ ∞ (fun u => symmetricOperatorLinear c (E (1 - outerSym u))) := by
  exact (symmetricOperatorLinear c).toContinuousLinearMap.contDiff.comp
    (E.toContinuousLinearMap.contDiff.comp (contDiff_const.sub contDiff_outerSym))

theorem kernelFamily_isSelfAdjoint (c : ℕ) (E : Sym 4 →ₗ[ℝ] Sym c) (u : Vec 4) :
    IsSelfAdjoint (symmetricOperatorLinear c (E (1 - outerSym u))) :=
  (E (1 - outerSym u)).property.map (Matrix.toEuclideanCLM (n := Fin c) (𝕜 := ℝ))

theorem kernel_projection_smooth_local_extension (c : ℕ) (_hC : 0 < c)
    (E : Sym 4 →ₗ[ℝ] Sym c) :
    ∃ (v : Vec 4) (U : Set (Vec 4)) (F : Vec 4 → Mat c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ IsOpen U ∧ v ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ u ∈ U, ‖u‖ = 1 →
        F u = kernelProjection (E (1 - outerSym u) : Mat c ℝ) := by
  let A : Vec 4 → Vec c →L[ℝ] Vec c := fun u => symmetricOperatorLinear c (E (1 - outerSym u))
  have hA : ContDiff ℝ ∞ A := contDiff_kernelFamily c E
  let S : Set (Vec 4) := {u | ‖u‖ = 1 ∧ u 0 ≠ 0}
  have hs : S.Nonempty := ⟨PiLp.single 2 0 1, by simp [S]⟩
  have hself (u : Vec 4) (_hu : u ∈ S) : IsSelfAdjoint (A u) :=
    kernelFamily_isSelfAdjoint c E u
  obtain ⟨v, hv, U, P, hU, hvU, hP, heq⟩ := exists_smooth_kernel_extension S hs A hA hself
  let U' := U ∩ {u : Vec 4 | u 0 ≠ 0}
  let F : Vec 4 → Mat c ℝ := fun u =>
    (Matrix.toEuclideanCLM (n := Fin c) (𝕜 := ℝ)).symm (P u)
  refine ⟨v, U', F, hv.1, hv.2, ?_, ⟨hvU, hv.2⟩, ?_, ?_⟩
  · have hc : Continuous (fun u : Vec 4 => u 0) :=
      (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (n := ∞) (i := (0 : Fin 4))).continuous
    exact hU.inter (isOpen_ne.preimage hc)
  · exact (Matrix.toEuclideanCLM (n := Fin c) (𝕜 := ℝ)).symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hP.mono (fun _ hu => hu.1))
  · intro u hu hunit
    apply (Matrix.toEuclideanCLM (n := Fin c) (𝕜 := ℝ)).injective
    change (Matrix.toEuclideanCLM (n := Fin c) (𝕜 := ℝ))
      ((Matrix.toEuclideanCLM (n := Fin c) (𝕜 := ℝ)).symm (P u)) = _
    rw [StarAlgEquiv.apply_symm_apply, heq u hu.1 ⟨hunit, hu.2⟩]
    apply ContinuousLinearMap.coe_injective
    change _ = Matrix.toEuclideanLin (kernelProjection (E (1 - outerSym u) : Mat c ℝ))
    rw [kernelProjection, LinearEquiv.apply_symm_apply]
    rfl

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped ContDiff Matrix.Norms.L2Operator
open Set Matrix ContinuousLinearMap


theorem solution : type_of% @_root_.OAI.Paper256.kernel_projection_smooth_local_extension := @_root_.OAI.Paper256.kernel_projection_smooth_local_extension
