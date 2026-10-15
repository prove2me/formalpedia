-- Prove2me | solution 1 for OAI.RuledApproximation.singular_overlap_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:40:35.646994+00:00
-- url     : https://prove2.me/submissions/7855ec0d-af63-4979-b91b-5dc86d57794d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularOverlap.lean:L202-L229
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singular_overlap_small. The node keeps its source
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
import Theorems.Thm_OAI_RuledApproximation_singular_overlap_algebra
import Theorems.Thm_OAI_RuledApproximation_singular_region_estimates

-- ---- from OAI.Geometry.RuledCovering.SingularOverlap ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma ceiling_nonneg {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (b : ℝ) :
    0 ≤ ceilingPolynomial p b := by
  unfold ceilingPolynomial
  have : 0 ≤ 2-p := sub_nonneg.mpr hp2
  positivity

lemma singular_overlap_small {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c x y : ℝ) (zm zp : Plane),
      0 ≤ c → c ≤ 1 → c*K ≤ 1/2 → 16*K^2*c^3 ≤ 2*c^(5/2:ℝ) →
      |x| ≤ 1 → |y| ≤ 1 → zm 1 ≤ 2 → zp 1 ≤ 2 →
      |zm 0| ≤ zm 1 → |zp 0| ≤ zp 1 →
      zm 0=y-c*x*singularField p zm 0 → zp 0=x+c*y*singularField p zp 0 →
      zm 1+zp 1=1+c*(y*singularField p zp 1-x*singularField p zm 1) →
      zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ) ∨
      zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ) := by
  obtain ⟨K,hK,he⟩ := singular_region_estimates p
  refine ⟨K,hK,?_⟩
  intro c x y zm zp hc hc1 hcK hsmall hx hy hzm hzp hbzm hbzp hezm hezp hesum
  by_cases hm : zm 1 ≤ 1/2+c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ)
  · exact Or.inl hm
  by_cases hp' : zp 1 ≤ 1/2+c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ)
  · exact Or.inr hp'
  have hrm : 1/2 ≤ zm 1 := by
    have hn := ceiling_nonneg hp hp2 (zm 0)
    have hn' : 0 ≤ c^2*ceilingPolynomial p (zm 0)+c^(5/2:ℝ) := by positivity
    linarith
  have hrp : 1/2 ≤ zp 1 := by
    have hn := ceiling_nonneg hp hp2 (zp 0)
    have hn' : 0 ≤ c^2*ceilingPolynomial p (zp 0)+c^(5/2:ℝ) := by positivity
    linarith
  obtain ⟨hPm,hQm,hPmy,hdm⟩ := he zm y (hbzm.trans hzm) hrm hzm (hy.trans (by norm_num))
  obtain ⟨hPp,hQp,hPpx,hdp⟩ := he zp x (hbzp.trans hzp) hrp hzp (hx.trans (by norm_num))
  exact singular_overlap_algebra hp2 hK hc hc1 hcK hsmall hx hy hrm hrp
    hPm hPp hQm hQp hPmy hPpx hdm hdp hezm hezp hesum

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singular_overlap_small := @_root_.OAI.RuledApproximation.singular_overlap_small
