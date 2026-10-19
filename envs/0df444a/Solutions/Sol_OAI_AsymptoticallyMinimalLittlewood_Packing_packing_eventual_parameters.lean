-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.packing_eventual_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:30:37.902521+00:00
-- url     : https://prove2.me/submissions/5f1c8e0b-49b1-43f1-88e5-daa22e5cb234

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SlotParameters.lean:L172-L194
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.packing_eventual_parameters. The node keeps its source
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

lemma chunkCount_bounds {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    B*chunkCount B q<q ∧ q≤B*(chunkCount B q+1) := by
  have hm := Nat.mod_lt (q-1) hB
  have he := Nat.mod_add_div (q-1) B
  dsimp [chunkCount]
  constructor
  · have hd := Nat.mul_div_le (q-1) B
    omega
  · nlinarith only [hm,he,show q-1+1=q by omega]

lemma chunkCount_ratio_error {B q : ℕ} (hB : 0<B) (hq : 0<q) :
    |(chunkCount B q : ℝ)/q-1/(B : ℝ)|≤1/(q : ℝ) := by
  obtain ⟨hlo,hhi⟩ := chunkCount_bounds hB hq
  have hB' : (0 : ℝ)<B := by exact_mod_cast hB
  have hq' : (0 : ℝ)<q := by exact_mod_cast hq
  have hlo' : (B : ℝ)*chunkCount B q≤q := by exact_mod_cast hlo.le
  have hhi' : (q : ℝ)≤B*(chunkCount B q+1) := by exact_mod_cast hhi
  rw [abs_le]
  constructor
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hB' hq')).mp
    field_simp
    nlinarith only [hhi']
  · apply (mul_le_mul_iff_of_pos_right (mul_pos hB' hq')).mp
    field_simp
    nlinarith only [hlo']

lemma chunkCount_ratio_tendsto {B : ℕ} (hB : 0<B) :
    Tendsto (fun q : ℕ ↦ (chunkCount B q : ℝ)/q) atTop (𝓝 (1/(B : ℝ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun q ↦ norm_nonneg _))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    simpa only [Real.norm_eq_abs] using chunkCount_ratio_error hB hq
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

lemma packingAV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) :
    Tendsto (packingAV r L R) atTop (𝓝 (packingALimit r R)) := by
  have hk := chunkCount_ratio_tendsto (show 0<2*R*L by positivity)
  have hq : Tendsto (fun q : ℕ ↦ 1/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  let a := ((r-1 : ℕ) : ℝ)
  let c := 2*((R : ℝ)-2)*L
  have hb := tendsto_const_nhds (x := (1 : ℝ)) |>.sub (hk.const_mul c)
  have ht := (((hb.const_mul a).add (hq.const_mul (2*a^2*(2*(R : ℝ)*L+1)))).const_mul 2 |>.add
    ((hb.add (hq.const_mul c)).const_mul (a^2))).const_mul 3
  have he : 3*(2*(a*(1-c*(1/((2*R*L : ℕ) : ℝ)))+
      2*a^2*(2*(R : ℝ)*L+1)*0)+a^2*(1-c*(1/((2*R*L : ℕ) : ℝ))+c*0)) =
      packingALimit r R := by
    dsimp [a,c,packingALimit]
    have hRn : (R : ℝ)≠0 := by exact_mod_cast hR.ne'
    have hLn : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
    ring
  rw [he] at ht
  exact ht

lemma packingNV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) :
    Tendsto (packingNV r L R) atTop (𝓝 (packingNLimit r L R)) := by
  have hk := chunkCount_ratio_tendsto (show 0<2*R*L by positivity)
  have ht := hk.const_mul ((r : ℝ)*((R : ℝ)-1))
  have he : (r : ℝ)*((R : ℝ)-1)*(1/((2*R*L : ℕ) : ℝ))=packingNLimit r L R := by
    dsimp [packingNLimit]
    have hRn : (R : ℝ)≠0 := by exact_mod_cast hR.ne'
    have hLn : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp

  rw [he] at ht
  exact ht

lemma packingBV_tendsto {r L R : ℕ} (hL : 0<L) (hR : 0<R) (e p : ℝ) :
    Tendsto (packingBV r L R e p) atTop (𝓝 (packingBLimit r R e p)) := by
  have hA : 0≤packingALimit r R := by unfold packingALimit; positivity
  have h := (((packingAV_tendsto (r := r) hL hR).max
    (tendsto_const_nhds (x := (0 : ℝ)))).const_mul (r : ℝ)).div_const ((e*p/2)^2)
  unfold packingBV packingBLimit
  simpa only [max_eq_left hA] using h

lemma packing_eventual_parameters {r L R : ℕ} (hL : 0<L) (hR : 0<R)
    {e p η t T : ℝ} (he : 0<e) (hp : 0<p)
    (hB : packingBLimit r R e p<e*p/2)
    (hS : 0<packingNLimit r L R-packingBLimit r R e p)
    (hN : packingNLimit r L R<(r : ℝ))
    (hM : (r : ℝ)*t<(1-η)*(packingNLimit r L R-packingBLimit r R e p)) :
    ∀ᶠ q : ℕ in atTop,
      1/(q : ℝ)≤e*p ∧ T/(q : ℝ)≤p ∧
      T/(q : ℝ)≤packingNV r L R q-packingBV r L R e p q ∧
      packingBV r L R e p q≤e*p/2 ∧ packingNV r L R q≤(r : ℝ) ∧
      (r : ℝ)*t<(1-η)*(packingNV r L R q-packingBV r L R e p q) := by
  have hNt := packingNV_tendsto (r := r) hL hR
  have hBt := packingBV_tendsto (r := r) hL hR e p
  have hSt := hNt.sub hBt
  have hq : Tendsto (fun q : ℕ ↦ 1/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hT : Tendsto (fun q : ℕ ↦ T/(q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hq.eventually (gt_mem_nhds (mul_pos he hp)),
    hT.eventually (gt_mem_nhds hp),hT.eventually_lt hSt hS,
    hBt.eventually (gt_mem_nhds hB),hNt.eventually (gt_mem_nhds hN),
    (hSt.const_mul (1-η)).eventually (lt_mem_nhds hM)] with q h1 h2 h3 h4 h5 h6
  exact ⟨h1.le,h2.le,h3.le,h4.le,h5.le,h6⟩

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


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.packing_eventual_parameters := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.packing_eventual_parameters
