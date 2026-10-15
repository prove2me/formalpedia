-- Prove2me | solution 1 for OAI.CompactBanach.exists_auerbach_basis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:16:42.880538+00:00
-- url     : https://prove2.me/submissions/67e2f115-7aab-4815-ab14-3f90086560ec

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Auerbach.lean:L10-L67
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.exists_auerbach_basis. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

-- ---- from OAI.Geometry.DoublingHilbert.Auerbach ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

theorem exists_auerbach_basis {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : Module.Basis ι ℝ E) :
    ∃ b : Module.Basis ι ℝ E, (∀ i, ‖b i‖ ≤ 1) ∧
      ∀ x i, |b.repr x i| ≤ ‖x‖ := by
  classical
  let U : Set (ι → E) := {v | ∀ i, ‖v i‖ ≤ 1}
  have hcompact : IsCompact U := by
    simpa only [U, Metric.mem_closedBall, dist_zero_right] using
      (isCompact_pi_infinite fun _ : ι => isCompact_closedBall (0 : E) 1)
  let en : Module.Basis ι ℝ E := e.unitsSMul fun i =>
    Units.mk0 (‖e i‖⁻¹) (inv_ne_zero (norm_ne_zero_iff.mpr (e.ne_zero i)))
  have hen : (en : ι → E) ∈ U := by
    intro i
    dsimp only [en]
    rw [Module.Basis.unitsSMul_apply]
    change ‖(‖e i‖ : ℝ)⁻¹ • e i‖ ≤ 1
    exact (norm_smul_inv_norm (𝕜 := ℝ) (e.ne_zero i)).le
  have hcont : Continuous fun v : ι → E => |e.det v| := by
    apply Continuous.abs
    change Continuous fun v : ι → E => Matrix.det (e.toMatrix v)
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i j
    exact (e.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
  obtain ⟨v, hv, hmax⟩ := hcompact.exists_isMaxOn ⟨en, hen⟩ hcont.continuousOn
  have hdet : e.det v ≠ 0 := by
    have hne : e.det en ≠ 0 := isUnit_iff_ne_zero.mp (e.isUnit_det en)
    have h := hmax hen
    exact abs_pos.mp (lt_of_lt_of_le (abs_pos.mpr hne) h)
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  let b : Module.Basis ι ℝ E := Module.Basis.mk hli hsp.ge
  refine ⟨b, ?_, ?_⟩
  · intro i
    simpa only [b, Module.Basis.mk_apply] using hv i
  · have hunit : ∀ x : E, ‖x‖ ≤ 1 → ∀ i, |b.repr x i| ≤ 1 := by
      intro x hx i
      have hu : Function.update v i x ∈ U := by
        intro j
        by_cases hj : j = i
        · subst j; simpa using hx
        · simpa [Function.update_of_ne hj] using hv j
      have hbound : |e.det (Function.update v i x)| ≤ |e.det v| := hmax hu
      have hid : e.det v * b.repr x i = e.det (Function.update v i x) := by
        have hh := congrArg (fun f : E →ₗ[ℝ] ℝ => f x)
          (e.det_smul_mk_coord_eq_det_update hli hsp.ge i)
        exact hh
      rw [← hid, abs_mul] at hbound
      exact (mul_le_mul_iff_right₀ (abs_pos.mpr hdet)).mp (by simpa using hbound)
    intro x i
    by_cases hx : x = 0
    · subst x; simp
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h := hunit (‖x‖⁻¹ • x) (norm_smul_inv_norm (𝕜 := ℝ) hx).le i
    have hid : b.repr (‖x‖⁻¹ • x) i = ‖x‖⁻¹ * b.repr x i := by simp
    rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hn)] at h
    have := mul_le_mul_of_nonneg_left h hn.le
    simpa [← mul_assoc, ne_of_gt hn] using this

                                                                                       
end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CompactBanach.exists_auerbach_basis := @_root_.OAI.CompactBanach.exists_auerbach_basis
