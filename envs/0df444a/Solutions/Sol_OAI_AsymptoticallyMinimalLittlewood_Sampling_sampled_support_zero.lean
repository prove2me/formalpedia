-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.sampled_support_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:53:53.183107+00:00
-- url     : https://prove2.me/submissions/1af9d157-cff5-4010-aba6-3e90ede8e871

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingEnergy.lean:L199-L212
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.sampled_support_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy

-- ---- from OAI.Analysis.Littlewood.SamplingEnergy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

lemma sampled_support_zero {g : ℝ → ℂ} (hg : tsupport g⊆Set.Ioo (0:ℝ) 1)
    {N : ℕ} (hN : 0<N) {k : ℤ} (hk : k<0 ∨ (N : ℤ)≤k) :
    g ((k : ℝ)/N)=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have hh := hg hx
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  rcases hk with hk | hk
  · have hkr : (k : ℝ)<0 := by exact_mod_cast hk
    have : (k : ℝ)/N<0 := div_neg_of_neg_of_pos hkr hNr
    linarith [hh.1]
  · have hkr : (N : ℝ)≤k := by exact_mod_cast hk
    have : 1≤(k : ℝ)/N := (le_div_iff₀ hNr).mpr (by simpa using hkr)
    linarith [hh.2]

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.sampled_support_zero := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.sampled_support_zero
