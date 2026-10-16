-- Prove2me | solution 1 for OAI.Paper256.isClosed_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:01:06.013321+00:00
-- url     : https://prove2.me/submissions/047abc72-89c4-404e-9271-59a85d74c7dc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilTopology.lean:L19-L35
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.isClosed_posSemidef. The node keeps its source
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

-- ---- from OAI.Analysis.HyperbolicCones.PencilTopology ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

theorem isClosed_posSemidef (n : ℕ) : IsClosed {X : Sym n | (X : Mat n ℝ).PosSemidef} := by
  have heq : {X : Sym n | (X : Mat n ℝ).PosSemidef} =
      ⋂ v : Fin n → ℝ, {X | 0 ≤ quadraticEvaluation v X} := by
    ext X
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h v
      simpa only [quadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk, star_trivial]
        using h.dotProduct_mulVec_nonneg v
    · intro h
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg X.property
      intro v
      simpa only [quadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk, star_trivial]
        using h v
  rw [heq]
  exact isClosed_iInter fun v => isClosed_le continuous_const
    (quadraticEvaluation v).continuous_of_finiteDimensional

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder


theorem solution : type_of% @_root_.OAI.Paper256.isClosed_posSemidef := @_root_.OAI.Paper256.isClosed_posSemidef
