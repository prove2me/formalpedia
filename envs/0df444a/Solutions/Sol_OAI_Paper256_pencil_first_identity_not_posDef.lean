-- Prove2me | solution 1 for OAI.Paper256.pencil_first_identity_not_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:06:01.627076+00:00
-- url     : https://prove2.me/submissions/78f0c5d5-6af7-44e4-b491-79364928527b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SplitBasic.lean:L68-L89
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.pencil_first_identity_not_posDef. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_interior_line_pair
import Theorems.Thm_OAI_Paper256_isOpen_posDef

-- ---- from OAI.Analysis.HyperbolicCones.SplitBasic ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem pencil_decomposition {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    L ((X, Z), y) = pencilFirst L X + pencilSecond L Z + pencilParameter L y := by
  change L ((X, Z), y) = L ((X, 0), 0) + L ((0, Z), 0) + L ((0, 0), y)
  rw [← map_add, ← map_add]
  simp

theorem pencil_first_identity_not_posDef {m : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    ¬ (pencilFirst L 1 : Mat m ℝ).PosDef := by
  intro hpos
  have hi : pencilFirst L 1 ∈ interior {Y : Sym m | (Y : Mat m ℝ).PosDef} := by
    rw [(isOpen_posDef m).interior_eq]
    exact hpos
  obtain ⟨ε, hε, _, hminus⟩ := interior_line_pair hi (pencilSecond L 1)
  have heq : L (((1, -(ε • 1)), 0) : Ambient) =
      pencilFirst L 1 - ε • pencilSecond L 1 := by
    rw [pencil_decomposition, map_neg, map_smul, map_zero]
    simp [sub_eq_add_neg]
  have hmem : (((1, -(ε • 1)), 0) : Ambient) ∈ K := by
    rw [hrep]
    change (L (((1, -(ε • 1)), 0) : Ambient) : Mat m ℝ).PosSemidef
    rw [heq]
    exact hminus.posSemidef
  have hh := ((hzero 1 (-(ε • 1))).mp hmem).2.diag_nonneg (i := (0 : Fin 4))
  have : 0 ≤ -ε := by simpa using hh
  linarith

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.pencil_first_identity_not_posDef := @_root_.OAI.Paper256.pencil_first_identity_not_posDef
