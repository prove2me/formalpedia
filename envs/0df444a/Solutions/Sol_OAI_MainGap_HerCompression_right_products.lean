-- Prove2me | solution 1 for OAI.MainGap.HerCompression.right_products
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:34:12.288749+00:00
-- url     : https://prove2.me/submissions/336eaf68-001c-43ff-b954-49a294e2f1ed

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Signal.lean:L158-L199
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.HerCompression.right_products. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma mul_star_mem_Her (h : A) : h * star h ∈ Her h := by
  apply (isClosed_Her h).mem_of_tendsto
    (((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const (star h))
  exact Filter.Eventually.of_forall (sandwich_mem_Her h)

lemma self_mem_Her {h : A} (hh : 0 ≤ h) : h ∈ Her h := by
  have hm : h * h ∈ Her h := by
    simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using mul_star_mem_Her h
  simpa only [CFC.sqrt_mul_self h hh] using
    sqrt_mem_Her hm (by simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using
      star_mul_self_nonneg h)

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Signal ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalCutPartialOrder
attribute [local instance] OAI.MainGap.signalCutStarOrderedRing
end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalComparisonPartialOrder
attribute [local instance] OAI.MainGap.signalComparisonStarOrderedRing
attribute [local instance] OAI.MainGap.signalOperatorPartialOrder
attribute [local instance] OAI.MainGap.signalOperatorStarOrderedRing
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalCoefficientPartialOrder
attribute [local instance] OAI.MainGap.signalCoefficientStarOrderedRing
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalProductsPartialOrder
attribute [local instance] OAI.MainGap.signalProductsStarOrderedRing
lemma HerCompression.right_products {p q c : A} {κ : ℝ} (hκ : 0 ≤ κ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : HerCompression p q c κ) (w z : A) :
    ‖star (p*w) * c * (q*z)‖ ≤ κ * ‖p*w‖ * ‖q*z‖ := by
  let : PartialOrder (Her p) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Her p) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (Her q) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Her q) := CStarAlgebra.spectralOrderedRing _
  let ap := CStarAlgebra.increasingApproximateUnit (Her p)
  let aq := CStarAlgebra.increasingApproximateUnit (Her q)
  let pp : Her p := ⟨p, self_mem_Her hp⟩
  let qq : Her q := ⟨q, self_mem_Her hq⟩
  have htp : Tendsto (fun e : Her p => (e : A) * (p*w))
      (CStarAlgebra.approximateUnit (Her p)) (𝓝 (p*w)) := by
    have hh := ((continuous_subtype_val.tendsto pp).comp (ap.tendsto_mul_right pp)).mul
      (tendsto_const_nhds (x := w))
    change Tendsto (fun e : Her p => ((e : A) * p) * w) _ (𝓝 (p*w)) at hh
    simpa only [mul_assoc] using hh
  have htq : Tendsto (fun e : Her q => (e : A) * (q*z))
      (CStarAlgebra.approximateUnit (Her q)) (𝓝 (q*z)) := by
    have hh := ((continuous_subtype_val.tendsto qq).comp (aq.tendsto_mul_right qq)).mul
      (tendsto_const_nhds (x := z))
    change Tendsto (fun e : Her q => ((e : A) * q) * z) _ (𝓝 (q*z)) at hh
    simpa only [mul_assoc] using hh
  have ht := ((htp.comp tendsto_fst).star.mul (tendsto_const_nhds (x := c))).mul
    (htq.comp tendsto_snd)
  apply le_of_tendsto ht.norm
  filter_upwards [ap.eventually_norm.prod_mk aq.eventually_norm] with ef hef
  rcases ef with ⟨e,f⟩
  change ‖star ((e : A)*(p*w))*c*((f : A)*(q*z))‖ ≤ _
  have he : ‖(e : A)‖ ≤ 1 := hef.1
  have hf : ‖(f : A)‖ ≤ 1 := hef.2
  calc
    ‖star ((e : A)*(p*w))*c*((f : A)*(q*z))‖ =
        ‖star (p*w) * (star (e : A)*c*(f : A)) * (q*z)‖ := by
      simp only [star_mul, mul_assoc]
    _ ≤ ‖p*w‖ * ‖star (e : A)*c*(f : A)‖ * ‖q*z‖ := by
      grw [norm_mul_le, norm_mul_le, norm_star]
    _ ≤ ‖p*w‖ * (κ*‖(e : A)‖*‖(f : A)‖) * ‖q*z‖ := by
      gcongr
      simpa only [norm_star] using h (star (e : A)) (star_mem e.property) (f : A) f.property
    _ ≤ ‖p*w‖ * (κ*1*1) * ‖q*z‖ := by gcongr
    _ = κ * ‖p*w‖ * ‖q*z‖ := by ring

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.signalProductsPartialOrder
attribute [local instance] OAI.MainGap.signalProductsStarOrderedRing


theorem solution : type_of% @_root_.OAI.MainGap.HerCompression.right_products := @_root_.OAI.MainGap.HerCompression.right_products
