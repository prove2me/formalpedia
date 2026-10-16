-- Prove2me | solution 1 for OAI.Paper256.FiniteMatrix.isOpen_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:19:53.338641+00:00
-- url     : https://prove2.me/submissions/d1786ed8-750c-45f7-8807-f2346cb82eae

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/FiniteTopology.lean:L59-L73
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.FiniteMatrix.isOpen_posDef. The node keeps its source
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

-- ---- from OAI.Analysis.HyperbolicCones.FiniteTopology ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u v

namespace Paper256.FiniteMatrix

theorem sym_neg_norm_le {ι : Type u} [Fintype ι] [DecidableEq ι] (X : selfAdjoint (Matrix ι ι ℝ)) :
    -(‖(X : Matrix ι ι ℝ)‖) • (1 : Matrix ι ι ℝ) ≤ (X : Matrix ι ι ℝ) := by
  classical
  rcases isEmpty_or_nonempty (ι) with h | h
  · have := h
    exact (Subsingleton.elim _ _).le
  · have := h
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (algebraMap_le_iff_le_spectrum (R := ℝ) (p := IsSelfAdjoint) X.property).mpr
    intro x hx
    have hh := spectrum.norm_le_norm_of_mem hx
    have hl := neg_abs_le x
    simpa only [Real.norm_eq_abs] using le_trans (neg_le_neg hh) hl

theorem posDef_of_scalar_lower_bound {ι : Type u} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (hX : c • (1 : Matrix ι ι ℝ) ≤ X) : X.PosDef := by
  have h := (Matrix.PosDef.one.smul hc).add_posSemidef hX
  simpa only [add_sub_cancel] using h

theorem posDef_scalar_lower_bound {ι : Type u} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℝ) (hX : X.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : Matrix ι ι ℝ) ≤ X := by
  classical
  rcases isEmpty_or_nonempty (ι) with h | h
  · have := h
    exact ⟨1, zero_lt_one, (Subsingleton.elim _ _).le⟩
  · have := h
    have hh := (CFC.exists_pos_algebraMap_le_iff (a := X) hX.isHermitian).mpr
      (fun x hx => by
        rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hX.eigenvalues_pos i)
    simpa only [Algebra.algebraMap_eq_smul_one] using hh

theorem isOpen_posDef (ι : Type u) [Fintype ι] [DecidableEq ι] : IsOpen {X : selfAdjoint (Matrix ι ι ℝ) | (X : Matrix ι ι ℝ).PosDef} := by
  apply Metric.isOpen_iff.mpr
  intro H hH
  obtain ⟨c, hc, hbound⟩ := posDef_scalar_lower_bound (H : Matrix ι ι ℝ) hH
  refine ⟨c / 2, by positivity, ?_⟩
  intro X hX
  have hnorm : ‖((X - H : selfAdjoint (Matrix ι ι ℝ)) : Matrix ι ι ℝ)‖ < c / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, AddSubgroup.coe_norm] using hX
  have hlower : -(c / 2) • (1 : Matrix ι ι ℝ) ≤ ((X - H : selfAdjoint (Matrix ι ι ℝ)) : Matrix ι ι ℝ) :=
    (smul_le_smul_of_nonneg_right (by linarith : -(c / 2) ≤ -‖((X - H : selfAdjoint (Matrix ι ι ℝ)) : Matrix ι ι ℝ)‖)
      Matrix.PosSemidef.one.nonneg).trans (sym_neg_norm_le (X - H))
  apply posDef_of_scalar_lower_bound (show 0 < c / 2 by positivity)
  have hh : c • (1 : Matrix ι ι ℝ) + -(c / 2) • (1 : Matrix ι ι ℝ) ≤
      (H : Matrix ι ι ℝ) + ((X : Matrix ι ι ℝ) - (H : Matrix ι ι ℝ)) := add_le_add hbound hlower
  convert hh using 1 <;> module

end Paper256.FiniteMatrix

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256 OAI.Paper256.FiniteMatrix
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder


theorem solution.{u} : type_of% @_root_.OAI.Paper256.FiniteMatrix.isOpen_posDef.{u} := @_root_.OAI.Paper256.FiniteMatrix.isOpen_posDef.{u}
