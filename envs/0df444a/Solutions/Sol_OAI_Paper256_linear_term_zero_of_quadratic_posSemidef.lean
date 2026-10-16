-- Prove2me | solution 1 for OAI.Paper256.linear_term_zero_of_quadratic_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:15:10.158017+00:00
-- url     : https://prove2.me/submissions/60845887-fc1b-4649-95fd-e02cc25c9496

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/RescalingBasic.lean:L28-L47
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.linear_term_zero_of_quadratic_posSemidef. The node keeps its source
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

-- ---- from OAI.Analysis.HyperbolicCones.RescalingBasic ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem linear_coefficient_zero_of_quadratic_nonneg (a b : ℝ)
    (h : ∀ s : ℝ, 0 ≤ a * s ^ 2 + b * s) : b = 0 := by
  have ha : 0 ≤ a := by nlinarith [h 1, h (-1)]
  rcases eq_or_lt_of_le ha with hzero | hpos
  · have ht := h (-b)
    rw [← hzero] at ht
    nlinarith [sq_nonneg b]
  · have ht := h (-b / (2 * a))
    have heq : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) =
        -b ^ 2 / (4 * a) := by
      field_simp
      ring
    rw [heq] at ht
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * a)).mp ht
    nlinarith [sq_nonneg b]

theorem linear_term_zero_of_quadratic_posSemidef {n : ℕ} (E G : Sym n)
    (h : ∀ s : ℝ, (s ^ 2 • (E : Mat n ℝ) + s • (G : Mat n ℝ)).PosSemidef) :
    G = 0 := by
  have hq (v : Fin n → ℝ) : v ⬝ᵥ ((G : Mat n ℝ) *ᵥ v) = 0 := by
    apply linear_coefficient_zero_of_quadratic_nonneg (v ⬝ᵥ ((E : Mat n ℝ) *ᵥ v))
    intro s
    have hs := (h s).dotProduct_mulVec_nonneg v
    simpa only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul, mul_comm] using hs
  have hg : (G : Mat n ℝ).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg G.property
    intro v
    simpa only [star_trivial, hq] using (le_refl (0 : ℝ))
  have hneg : (-(G : Mat n ℝ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg G.property.neg
    intro v
    simpa only [star_trivial, neg_mulVec, dotProduct_neg, hq, neg_zero]
      using (le_refl (0 : ℝ))
  apply Subtype.ext
  exact le_antisymm (neg_nonneg.mp hneg.nonneg) hg.nonneg

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder


theorem solution : type_of% @_root_.OAI.Paper256.linear_term_zero_of_quadratic_posSemidef := @_root_.OAI.Paper256.linear_term_zero_of_quadratic_posSemidef
