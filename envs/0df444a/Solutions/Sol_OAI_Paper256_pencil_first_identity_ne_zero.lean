-- Prove2me | solution 1 for OAI.Paper256.pencil_first_identity_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:04:31.913465+00:00
-- url     : https://prove2.me/submissions/b2b2bcdb-3982-4548-8d4c-d80583032141

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SplitBasic.lean:L50-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.pencil_first_identity_ne_zero. The node keeps its source
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

theorem pencil_components_positive {m : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    (∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (pencilFirst L X : Mat m ℝ).PosSemidef) ∧
    (∀ Z : Sym 4, (Z : Mat 4 ℝ).PosSemidef → (pencilSecond L Z : Mat m ℝ).PosSemidef) := by
  constructor
  · intro X hX
    have h := (hzero X 0).mpr ⟨hX, Matrix.PosSemidef.zero⟩
    simpa only [hrep, mem_ofPred_eq] using! h
  · intro Z hZ
    have h := (hzero 0 Z).mpr ⟨Matrix.PosSemidef.zero, hZ⟩
    simpa only [hrep, mem_ofPred_eq] using! h

theorem pencil_first_identity_ne_zero {m : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    (pencilFirst L 1 : Mat m ℝ) ≠ 0 := by
  intro hz
  have hz' : pencilFirst L 1 = 0 := Subtype.ext hz
  have hpositive := (pencil_components_positive K L hrep hzero).2 1 Matrix.PosSemidef.one
  have heq : L (((-1, 1), 0) : Ambient) = pencilSecond L 1 := by
    rw [pencil_decomposition, map_neg, hz', map_zero]
    simp
  have hmem : (((-1, 1), 0) : Ambient) ∈ K := by
    rw [hrep]
    change (L (((-1, 1), 0) : Ambient) : Mat m ℝ).PosSemidef
    rwa [heq]
  have hh := ((hzero (-1) 1).mp hmem).1.diag_nonneg (i := (0 : Fin 4))
  norm_num at hh

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Matrix
open scoped Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.pencil_first_identity_ne_zero := @_root_.OAI.Paper256.pencil_first_identity_ne_zero
