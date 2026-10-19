-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.packing_choose_R
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:29:09.095337+00:00
-- url     : https://prove2.me/submissions/d33dc77d-1047-4cf0-98b2-ec9cbe484f59

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SlotParameters.lean:L141-L170
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.packing_choose_R. The node keeps its source
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

-- ---- from OAI.Analysis.Littlewood.SlotParameters ----
namespace OAI

universe uV

/-! Parameter choices for the concrete signed-slot packing. The chunk
length is chosen first and remains fixed while the prime modulus grows. -/
namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open Filter Topology
open scoped BigOperators

lemma packingALimit_tendsto (r : ℕ) :
    Tendsto (packingALimit r) atTop (𝓝 (0 : ℝ)) := by
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

lemma packingNLimit_tendsto (r L : ℕ) :
    Tendsto (packingNLimit r L) atTop (𝓝 ((r : ℝ)/(2*L))) := by
  have hq : Tendsto (fun R : ℕ ↦ 1/(R : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  unfold packingNLimit
  simpa only [sub_zero, mul_one] using
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hq).const_mul (r : ℝ)).div_const (2*L)

lemma packingBLimit_tendsto (r : ℕ) (e p : ℝ) :
    Tendsto (fun R ↦ packingBLimit r R e p) atTop (𝓝 (0 : ℝ)) := by
  have h := ((packingALimit_tendsto r).const_mul (r : ℝ)).div_const ((e*p/2)^2)
  unfold packingBLimit
  simpa only [mul_zero,zero_div] using h

lemma packing_choose_R {r L : ℕ} (hr : 0<r) (hL : 0<L)
    {e p η t : ℝ} (he : 0<e) (hp : 0<p)
    (hmargin : (r : ℝ)*t<(1-η)*((r : ℝ)/(2*L))) :
    ∃ R : ℕ, 3≤R ∧
      packingBLimit r R e p<e*p/2 ∧
      0<packingNLimit r L R-packingBLimit r R e p ∧
      packingNLimit r L R<(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p) := by
  have hNpos : (0 : ℝ)<(r : ℝ)/(2*L) := by positivity
  have hNlt : (r : ℝ)/(2*L)<r := by
    have hl : (1 : ℝ)≤L := by exact_mod_cast hL
    have hr' : (0 : ℝ)<r := by exact_mod_cast hr
    apply (div_lt_iff₀ (by positivity : (0 : ℝ)<2*L)).mpr
    nlinarith
  have hN := packingNLimit_tendsto r L
  have hB := packingBLimit_tendsto r e p
  have hS := hN.sub hB
  have hSp : Tendsto (fun R ↦ packingNLimit r L R-packingBLimit r R e p) atTop
      (𝓝 ((r : ℝ)/(2*L))) := by simpa using hS
  have hev : ∀ᶠ R : ℕ in atTop, 3≤R ∧
      packingBLimit r R e p<e*p/2 ∧
      0<packingNLimit r L R-packingBLimit r R e p ∧
      packingNLimit r L R<(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p) := by
    filter_upwards [eventually_ge_atTop 3,
      hB.eventually (gt_mem_nhds (show (0 : ℝ)<e*p/2 by positivity)),
      hSp.eventually (lt_mem_nhds hNpos),hN.eventually (gt_mem_nhds hNlt),
      (hSp.const_mul (1-η)).eventually (lt_mem_nhds hmargin)] with R hR h1 h2 h3 h4
    exact ⟨hR,h1,h2,h3,h4⟩
  exact hev.exists

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open Filter Topology
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.packing_choose_R := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.packing_choose_R
