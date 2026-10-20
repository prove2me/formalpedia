-- Prove2me | solution 1 for OAI.GaussianPropeller.FourAlgebra.small_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:33:32.669687+00:00
-- url     : https://prove2.me/submissions/b6e6f910-89ed-4fab-a3b9-b237a90ad836

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/FourAlgebra.lean:L131-L150
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.FourAlgebra.small_exclusion. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_FourAlgebra_small_core

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

lemma small_exclusion {t a b c H V D:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ))
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hs:a+b+c=1)
    (hH:H=1-t^2-(a^2+b^2+c^2)*t^2)
    (hV:(3/5:ℝ)*V≤(10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2)
    (hD:4*D=H^2-2*V)
    (hab:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+b)^2)
    (hac:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+c)^2)
    (hbc:D≤(3/Real.pi)^2*t^2*(1+b)^2*(1+c)^2) : False := by
  by_cases hac':a≤c
  · by_cases hbc':b≤c
    · exact small_core ht ha hb hc hs hac' hbc' hH hV hD hab
    · apply small_core (a:=a) (b:=c) (c:=b) ht ha hc hb (by linarith only [hs])
        (hac'.trans (le_of_not_ge hbc')) (le_of_not_ge hbc')
        (by nlinarith only [hH]) hV hD hac
  · by_cases hba:b≤a
    · exact small_core (a:=b) (b:=c) (c:=a) ht hb hc ha (by linarith only [hs]) hba
        (le_of_not_ge hac') (by nlinarith only [hH]) hV hD hbc
    · exact small_core (a:=a) (b:=c) (c:=b) ht ha hc hb (by linarith only [hs])
        (le_of_not_ge hba) ((le_of_not_ge hac').trans (le_of_not_ge hba))
        (by nlinarith only [hH]) hV hD hac

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.FourAlgebra.small_exclusion := @_root_.OAI.GaussianPropeller.FourAlgebra.small_exclusion
