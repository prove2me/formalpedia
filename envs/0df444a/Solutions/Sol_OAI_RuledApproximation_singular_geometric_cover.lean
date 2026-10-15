-- Prove2me | solution 1 for OAI.RuledApproximation.singular_geometric_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:41:57.767848+00:00
-- url     : https://prove2.me/submissions/f815f1bd-5f89-4f59-8413-646f00d3dbad

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularGeometry.lean:L12-L74
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singular_geometric_cover. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Theorems.Thm_OAI_RuledApproximation_singular_inverse_small
import Theorems.Thm_OAI_RuledApproximation_singular_overlap_small

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_cutoff_small {p gamma : ℝ} (hpg : 0 < 1+gamma*(p-2)) :
    Tendsto (fun c : ℝ => c*(c^gamma)^(p-2)) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c^(1+gamma*(p-2))) (𝓝[>] 0)
      (𝓝 ((0:ℝ)^(1+gamma*(p-2)))) :=
    ((Real.continuous_rpow_const hpg.le).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [Real.zero_rpow hpg.ne'] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc : 0 < c := hc
  rw [← Real.rpow_mul hc.le,Real.rpow_add hc,Real.rpow_one]

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularOverlap ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma right_rpow_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 ((0:ℝ)^q)) :=
    ((Real.continuous_rpow_const hq.le).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  simpa only [Real.zero_rpow hq.ne'] using h

lemma overlap_error_eventually (K : ℝ) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, 16*K^2*c^3 ≤ 2*c^(5/2:ℝ) := by
  have h : Tendsto (fun c : ℝ => 16*K^2*c^(1/2:ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (right_rpow_tendsto_zero (q := (1/2:ℝ)) (by norm_num)).const_mul (16*K^2)
  filter_upwards [self_mem_nhdsWithin,h.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<2))] with c hc hb
  have hc : 0 < c := hc
  have he : c^3=c^(1/2:ℝ)*c^(5/2:ℝ) := by
    rw [← Real.rpow_add hc]
    norm_num
  rw [he]
  nlinarith only [mul_le_mul_of_nonneg_right hb.le (Real.rpow_nonneg hc.le (5/2:ℝ))]

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularGeometry ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_geometric_cover {p gamma : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hpg : 0 < 1+gamma*(p-2)) :
    ∀ᶠ c : ℝ in 𝓝[>] 0,
      tetrahedron ⊆ singularLower p gamma c ∪ singularUpper p gamma c ∪
        lowerTip (c^gamma) ∪ upperTip (c^gamma) := by
  obtain ⟨C,_,hinv⟩ := singular_inverse_small hp2
  obtain ⟨K,_,hover⟩ := singular_overlap_small (by linarith : 0 ≤ p) hp2.le
  have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hcut : Tendsto (fun c : ℝ => c*C*(c^gamma)^(p-2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_assoc,mul_left_comm,mul_zero] using (singular_cutoff_small hpg).const_mul C
  have hKlim : Tendsto (fun c : ℝ => c*K) (𝓝[>] 0) (𝓝 0) := by simpa using h0.mul_const K
  filter_upwards [self_mem_nhdsWithin,h0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hKlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),overlap_error_eventually K]
    with c hc hc1 hcut hcK herr
  have hc : 0 < c := hc
  intro z hz
  obtain ⟨t,ht0,ht1,hx,hy,hz2⟩ := hz
  by_cases htip : t ≤ 2*c^gamma
  · exact Or.inl (Or.inr ⟨t,ht0,htip,hy,hz2⟩)
  by_cases htip' : 1-t ≤ 2*c^gamma
  · exact Or.inr ⟨1-t,by linarith,htip',hx,by rw [hz2]; congr 1; ring⟩
  have hx1 : |z 0| ≤ 1 := hx.trans (by linarith)
  have hy1 : |z 1| ≤ 1 := hy.trans ht1
  have hkx : |c*z 0| ≤ c := by simpa only [abs_mul,abs_of_pos hc,mul_one] using mul_le_mul_of_nonneg_left hx1 hc.le
  have hky : |-c*z 1| ≤ c := by simpa only [abs_mul,abs_neg,abs_of_pos hc,mul_one] using mul_le_mul_of_nonneg_left hy1 hc.le
  obtain ⟨zm,hm0,hm2,hmb,hem⟩ := hinv (c^gamma) c (z 1) t (c*z 0)
    (Real.rpow_pos_of_pos hc gamma) hc.le hcut.le (by linarith) ht1 hy hkx
  obtain ⟨zp,hp0,hp2',hpb,hep⟩ := hinv (c^gamma) c (z 0) (1-t) (-c*z 1)
    (Real.rpow_pos_of_pos hc gamma) hc.le hcut.le (by linarith) (by linarith) hx hky
  have hem0 := congrArg (fun w : Plane => w 0) hem
  have hem1 := congrArg (fun w : Plane => w 1) hem
  have hep0 := congrArg (fun w : Plane => w 0) hep
  have hep1 := congrArg (fun w : Plane => w 1) hep
  change z 1 = zm 0+(c*z 0)*singularField p zm 0 at hem0
  change t = zm 1+(c*z 0)*singularField p zm 1 at hem1
  change z 0 = zp 0+(-c*z 1)*singularField p zp 0 at hep0
  change 1-t = zp 1+(-c*z 1)*singularField p zp 1 at hep1
  have hceil := hover c (z 0) (z 1) zm zp hc.le hc1.le hcK.le herr hx1 hy1 hm2 hp2' hmb hpb
    (by linarith only [hem0]) (by linarith only [hep0]) (by nlinarith only [hem1,hep1])
  rcases hceil with hm | hp'
  · apply Or.inl ∘ Or.inl ∘ Or.inl
    refine ⟨zm,⟨hm0,hm2,hmb,hm⟩,z 0,hx1,?_⟩
    ext i
    fin_cases i
    · rfl
    · change z 1 = zm 0+z 0*(c*singularField p zm 0)
      nlinarith only [hem0]
    · change z 2 = Real.sqrt 2*(zm 1+z 0*(c*singularField p zm 1))
      rw [hz2]
      congr 1
      nlinarith only [hem1]
  · apply Or.inl ∘ Or.inl ∘ Or.inr
    refine ⟨zp,⟨hp0,hp2',hpb,hp'⟩,z 1,hy1,?_⟩
    ext i
    fin_cases i
    · change z 0 = zp 0-c*z 1*singularField p zp 0
      nlinarith only [hep0]
    · rfl
    · change z 2 = Real.sqrt 2*(1-(zp 1-c*z 1*singularField p zp 1))
      rw [hz2]
      congr 1
      nlinarith only [hep1]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singular_geometric_cover := @_root_.OAI.RuledApproximation.singular_geometric_cover
