-- Prove2me | solution 1 for OAI.GaussianPropeller.FourAlgebra.quartic_positive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:29:01.754775+00:00
-- url     : https://prove2.me/submissions/13c359d0-4b69-4286-b52b-4956b50d4d8e

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/FourAlgebra.lean:L38-L55
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.FourAlgebra.quartic_positive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates

-- ---- from OAI.Probability.GaussianPropeller.FourAlgebra ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourAlgebra
open scoped RealInnerProductSpace

lemma quartic_positive {t L c₀ c₁ c₂ c₄:ℝ} (ht:0≤t) (htL:t≤L) (hL:0<L)
    (hc₄:0≤c₄) (hconc:c₂+3*c₄*L^2≤0) (hc₀:0<c₀)
    (hend:0<c₀+c₁*L+c₂*L^2+c₄*L^4) : 0<c₀+c₁*t+c₂*t^2+c₄*t^4 := by
  have ht2 : t^2≤L^2 := (sq_le_sq₀ ht hL.le).mpr htL
  have htL' : L*t≤L^2 := by nlinarith only [mul_le_mul_of_nonneg_left htL hL.le]
  have hb : 0≤-c₂-c₄*(t^2+L*t+L^2) := by
    have hh := mul_le_mul_of_nonneg_left (show t^2+L*t+L^2≤3*L^2 by linarith only [ht2,htL']) hc₄
    linarith only [hh,hconc]
  have hp:=mul_nonneg (mul_nonneg ht (sub_nonneg.mpr htL)) hb
  have hid : L*(c₀+c₁*t+c₂*t^2+c₄*t^4) =
      (L-t)*c₀+t*(c₀+c₁*L+c₂*L^2+c₄*L^4)+L*(t*(L-t)*(-c₂-c₄*(t^2+L*t+L^2))) := by ring
  have hlin : 0<(L-t)*c₀+t*(c₀+c₁*L+c₂*L^2+c₄*L^4) := by
    by_cases htz:t=0
    · subst t; simpa using mul_pos hL hc₀
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr htL) hc₀.le)
        (mul_pos (lt_of_le_of_ne ht (Ne.symm htz)) hend)
  have hm:=mul_nonneg hL.le hp
  nlinarith only [hid,hlin,hm,hL]

end GaussianPropeller.FourAlgebra

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.FourAlgebra
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.FourAlgebra.quartic_positive := @_root_.OAI.GaussianPropeller.FourAlgebra.quartic_positive
