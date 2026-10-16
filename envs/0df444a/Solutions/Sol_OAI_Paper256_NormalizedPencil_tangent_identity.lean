-- Prove2me | solution 1 for OAI.Paper256.NormalizedPencil.tangent_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:05:38.882463+00:00
-- url     : https://prove2.me/submissions/dc59517e-8f7a-4ea6-b944-a544a013a8ce

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/TangentIdentity.lean:L15-L44
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.NormalizedPencil.tangent_identity. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_NormalizedPencil_norm_identity
import Theorems.Thm_OAI_Paper256_kernel_projection_tangent_derivative
import Theorems.Thm_OAI_Paper256_norm_sq_derivative_of_quadratic_curve

-- ---- from OAI.Analysis.HyperbolicCones.FormBasic ----
namespace OAI

/-! Exact identities for the Choi–Lam form. -/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem choiLam_expand {R : Type u} [CommRing R] (z y : Fin 3 → R) :
    choiLam z y =
      z 0 ^ 2 * y 0 ^ 2 + z 1 ^ 2 * y 1 ^ 2 + z 2 ^ 2 * y 2 ^ 2 -
      2 * (z 0 * y 0 * z 1 * y 1 + z 0 * y 0 * z 2 * y 2 +
        z 1 * y 1 * z 2 * y 2) +
      (z 0 ^ 2 * y 1 ^ 2 + z 1 ^ 2 * y 2 ^ 2 + z 2 ^ 2 * y 0 ^ 2) := by
  simp [choiLam, Fin.sum_univ_succ]
  ring

theorem choiLam_smul_left (z y : Fin 3 → ℝ) (s : ℝ) :
    choiLam (s • z) y = s ^ 2 * choiLam z y := by
  simp only [choiLam_expand, Pi.smul_apply, smul_eq_mul]
  ring

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.TangentBasic ----
namespace OAI

noncomputable section

open scoped RealInnerProductSpace

namespace Paper256

theorem tangentCurve_unit (v h : Vec 4) (hv : ‖v‖ = 1)
    (hh : inner ℝ v h = 0) (s : ℝ) : ‖tangentCurve v h s‖ = 1 := by
  have hp : 0 < 1 + s ^ 2 * ‖h‖ ^ 2 := by positivity
  have hn : ‖v + s • h‖ = Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2) := by
    symm
    apply (Real.sqrt_eq_iff_eq_sq hp.le (norm_nonneg _)).2
    symm
    rw [norm_add_sq_real, real_inner_smul_right, hh, hv, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [tangentCurve, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (Real.sqrt_pos.2 hp), hn, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hp))]

theorem tangentCurve_wedge (v h : Vec 4) (s : ℝ) :
    wedgeCoordinates v (tangentCurve v h s) =
      (s / Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2)) • wedgeCoordinates v h := by
  funext i
  simp [wedgeCoordinates, tangentCurve, div_eq_mul_inv]
  ring

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.OperatorEntries ----
namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

theorem operatorNorm_eq_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    operatorNorm A = ‖A‖ := rfl

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.NormIdentity ----
namespace OAI

/-! The norm identity follows from the exact scalar thresholds and their rank-one limits. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
namespace Paper256

theorem NormalizedPencil.same_direction_zero (P : NormalizedPencil)
    (v : Vec 4) (hv : ‖v‖ = 1) (y : Fin 3 → ℝ) :
    P.leftProjection v * P.B y * P.rightProjection v = 0 := by
  have h := P.norm_identity v v hv hv y
  have hz : wedgeCoordinates v v = 0 := by ext i; simp [wedgeCoordinates]
  rw [hz] at h
  have hc : choiLam (0 : Fin 3 → ℝ) y = 0 := by simp [choiLam]
  rw [hc, operatorNorm_eq_norm] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h.symm)

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.TangentIdentity ----
namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

namespace Paper256

theorem NormalizedPencil.tangent_identity (P : NormalizedPencil) :
    ∃ (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat P.c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ ∀ h : Vec 4, inner ℝ v h = 0 → ∀ y : Fin 3 → ℝ,
        choiLam (wedgeCoordinates v h) y =
          operatorNorm (P.leftProjection v * P.B y * T h) ^ 2 := by
  obtain ⟨v, T, hv, hv0, ht⟩ := kernel_projection_tangent_derivative P.c P.c_pos P.E
  refine ⟨v, T, hv, hv0, ?_⟩
  intro h hh y
  let M := mulLeftLinearMap (Fin P.c) ℝ (P.leftProjection v * P.B y)
  let f : ℝ → Matrix (Fin P.a) (Fin P.c) ℝ :=
    fun s => P.leftProjection v * P.B y * P.rightProjection (tangentCurve v h s)
  have hderiv : HasDerivAt f (P.leftProjection v * P.B y * T h) 0 := by
    simpa only [f, M, NormalizedPencil.rightProjection, Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap', mulLeftLinearMap_apply] using!
      M.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (ht h hh)
  have hzero : f 0 = 0 := by
    simpa [f, tangentCurve] using P.same_direction_zero v hv y
  have hval (s : ℝ) : ‖f s‖ ^ 2 =
      s ^ 2 / (1 + s ^ 2 * ‖h‖ ^ 2) * choiLam (wedgeCoordinates v h) y := by
    have he := P.norm_identity (tangentCurve v h s) v
      (tangentCurve_unit v h hv hh s) hv y
    rw [tangentCurve_wedge, choiLam_smul_left, operatorNorm_eq_norm] at he
    change (s / Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2)) ^ 2 *
      choiLam (wedgeCoordinates v h) y = ‖f s‖ ^ 2 at he
    rw [div_pow, Real.sq_sqrt (by positivity)] at he
    exact he.symm
  have hlim := norm_sq_derivative_of_quadratic_curve f
    (P.leftProjection v * P.B y * T h) (choiLam (wedgeCoordinates v h) y)
    (‖h‖ ^ 2) (sq_nonneg _) hderiv hzero hval
  simpa only [operatorNorm_eq_norm] using hlim.symm

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix


theorem solution : type_of% @_root_.OAI.Paper256.NormalizedPencil.tangent_identity := @_root_.OAI.Paper256.NormalizedPencil.tangent_identity
