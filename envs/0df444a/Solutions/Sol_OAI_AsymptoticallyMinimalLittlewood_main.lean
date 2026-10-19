-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:10:43.665762+00:00
-- url     : https://prove2.me/submissions/094d7fcd-f320-467c-a39c-bbfbf855d459

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Main.lean:L187-L227
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.AsymptoticallyMinimalLittlewood.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_almost_sign_sampler
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_round_sample_once

-- ---- from OAI.Analysis.Littlewood.Main ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators
end
end AsymptoticallyMinimalLittlewood
namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped Topology
open Filter

lemma small_delta_budget {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ<1/20 ∧
      Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ))<1+η/2 := by
  let f (x : ℝ) := Real.sqrt ((1+x)^3/(1-x))+
    393216*Real.sqrt (x*Real.log 20-x*Real.log x)
  have hf : ContinuousAt f 0 := by
    apply ContinuousAt.add
    · exact Real.continuous_sqrt.continuousAt.comp
        (((continuousAt_const.add continuousAt_id).pow 3).div
          (continuousAt_const.sub continuousAt_id) (by norm_num))
    · exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
        ((continuousAt_id.mul continuousAt_const).sub Real.continuous_mul_log.continuousAt))
  have hf0 : f 0=1 := by norm_num [f]
  obtain ⟨r,hr,hh⟩ := Metric.continuousAt_iff.mp hf (η/2) (by positivity)
  let δ := min (r/2) (1/40)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ20 : δ<1/20 := (min_le_right _ _).trans_lt (by norm_num)
  have hδr : δ<r := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist δ (0:ℝ)<r := by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using hδr
  have hval := hh hd
  rw [hf0,Real.dist_eq] at hval
  have he : f δ=Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ)) := by
    dsimp [f]
    rw [Real.log_div (by norm_num : (20:ℝ)≠0) hδ.ne',mul_sub]
  refine ⟨δ,hδ,hδ20,?_⟩
  rw [he] at hval
  have := (abs_lt.mp hval).2
  linarith

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

theorem main : MainStatement := by
  intro η hη
  obtain ⟨δ,hδ,hδ20,hbudget⟩ := small_delta_budget hη
  obtain ⟨X,L,C,hC,hL,hX,hE,hmax⟩ := almost_sign_sampler hδ hδ20
  let B := Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ))
  have hB : B<1+η := by dsimp [B]; linarith
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hinv : Tendsto (fun N : ℕ ↦ 1/Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp hsqrt) using 1
    funext N
    simp only [Function.comp_apply,one_div]
  have hrem : Tendsto (fun N : ℕ ↦ C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat C).add (hinv.const_mul 196608)
  have her : ∀ᶠ N : ℕ in atTop,
      C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))<1+η-B :=
    hrem.eventually (gt_mem_nhds (sub_pos.mpr hB))
  have hen : ∀ᶠ N : ℕ in atTop, 1-8*δ<(∑ k, (X N k)^2)/(N : ℝ) :=
    hE.eventually (lt_mem_nhds (show 1-8*δ<L by linarith))
  have hall : ∀ᶠ N : ℕ in atTop,
      1≤N ∧ 1-8*δ<(∑ k, (X N k)^2)/(N : ℝ) ∧
        C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))<1+η-B := by
    filter_upwards [eventually_ge_atTop (1:ℕ),hen,her] with N hN hn hr
    exact ⟨hN,hn,hr⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hall
  refine ⟨N₀,(hN₀ N₀ le_rfl).1,?_⟩
  intro N hN
  obtain ⟨hN1,hen,her⟩ := hN₀ N hN
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hener : (1-8*δ)*(N : ℝ)≤∑ k, (X N k)^2 :=
    ((lt_div_iff₀ hNr).mp hen).le
  obtain ⟨ε,hε,hεb⟩ := round_sample_once hN1 hδ hδ20 (X N) (hX N hN1)
    hener (hmax N hN1)
  refine ⟨ε,hε,?_⟩
  intro z hz
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hNr)).mp
  have hb := hεb z hz
  dsimp [B] at her
  linarith

end
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- mission target ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open scoped BigOperators Topology
open Filter

namespace OAI
namespace AsymptoticallyMinimalLittlewood
theorem _root_.solution : MainStatement := by
  first
    | exact OAI.AsymptoticallyMinimalLittlewood.main
    | (apply OAI.AsymptoticallyMinimalLittlewood.main <;> assumption)
    | (intros; apply OAI.AsymptoticallyMinimalLittlewood.main <;> assumption)
end AsymptoticallyMinimalLittlewood
end OAI
