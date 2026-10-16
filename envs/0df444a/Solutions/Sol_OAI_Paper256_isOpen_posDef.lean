-- Prove2me | solution 1 for OAI.Paper256.isOpen_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:59:16.487473+00:00
-- url     : https://prove2.me/submissions/15091658-7e18-4ccf-aad7-f8deeabe985d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilOrder.lean:L54-L68
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.isOpen_posDef. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_sym_neg_norm_le

-- ---- from OAI.Analysis.HyperbolicCones.PencilOrder ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem posDef_of_scalar_lower_bound {n : ℕ} {X : Mat n ℝ} {c : ℝ}
    (hc : 0 < c) (hX : c • (1 : Mat n ℝ) ≤ X) : X.PosDef := by
  have h := (Matrix.PosDef.one.smul hc).add_posSemidef hX
  simpa only [add_sub_cancel] using h

theorem posDef_scalar_lower_bound {n : ℕ} (X : Mat n ℝ) (hX : X.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : Mat n ℝ) ≤ X := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · have := h
    exact ⟨1, zero_lt_one, (Subsingleton.elim _ _).le⟩
  · have := h
    have hh := (CFC.exists_pos_algebraMap_le_iff (a := X) hX.isHermitian).mpr
      (fun x hx => posDef_real_spectrum_positive hX hx)
    simpa only [Algebra.algebraMap_eq_smul_one] using hh

theorem isOpen_posDef (n : ℕ) : IsOpen {X : Sym n | (X : Mat n ℝ).PosDef} := by
  apply Metric.isOpen_iff.mpr
  intro H hH
  obtain ⟨c, hc, hbound⟩ := posDef_scalar_lower_bound (H : Mat n ℝ) hH
  refine ⟨c / 2, by positivity, ?_⟩
  intro X hX
  have hnorm : ‖((X - H : Sym n) : Mat n ℝ)‖ < c / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, AddSubgroup.coe_norm] using hX
  have hlower : -(c / 2) • (1 : Mat n ℝ) ≤ ((X - H : Sym n) : Mat n ℝ) :=
    (smul_le_smul_of_nonneg_right (by linarith : -(c / 2) ≤ -‖((X - H : Sym n) : Mat n ℝ)‖)
      Matrix.PosSemidef.one.nonneg).trans (sym_neg_norm_le (X - H))
  apply posDef_of_scalar_lower_bound (show 0 < c / 2 by positivity)
  have hh : c • (1 : Mat n ℝ) + -(c / 2) • (1 : Mat n ℝ) ≤
      (H : Mat n ℝ) + ((X : Mat n ℝ) - (H : Mat n ℝ)) := add_le_add hbound hlower
  convert hh using 1 <;> module

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder


theorem solution : type_of% @_root_.OAI.Paper256.isOpen_posDef := @_root_.OAI.Paper256.isOpen_posDef
