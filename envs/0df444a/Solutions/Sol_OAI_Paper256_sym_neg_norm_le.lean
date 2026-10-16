-- Prove2me | solution 1 for OAI.Paper256.sym_neg_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:57:58.140417+00:00
-- url     : https://prove2.me/submissions/c4efa63a-6c7d-4469-8891-f6875a5291c5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilOrder.lean:L12-L24
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.sym_neg_norm_le. The node keeps its source
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

-- ---- from OAI.Analysis.HyperbolicCones.PencilOrder ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem sym_neg_norm_le {n : ℕ} (X : Sym n) :
    -(‖(X : Mat n ℝ)‖) • (1 : Mat n ℝ) ≤ (X : Mat n ℝ) := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · have := h
    exact (Subsingleton.elim _ _).le
  · have := h
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (algebraMap_le_iff_le_spectrum (R := ℝ) (p := IsSelfAdjoint) X.property).mpr
    intro x hx
    have hh := spectrum.norm_le_norm_of_mem hx
    have hl := neg_abs_le x
    simpa only [Real.norm_eq_abs] using le_trans (neg_le_neg hh) hl

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder


theorem solution : type_of% @_root_.OAI.Paper256.sym_neg_norm_le := @_root_.OAI.Paper256.sym_neg_norm_le
