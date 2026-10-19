-- Prove2me | solution 1 for OAI.MainGap.compression_of_conditional_loss
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:08:37.343559+00:00
-- url     : https://prove2.me/submissions/b89e25b9-2d8c-4e74-a6d3-796d6da42b05

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean:L249-L270
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.compression_of_conditional_loss. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_cutInverseFn_bound

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_sandwich {h k : A} (hk : k ∈ Her h) (a : A) : k * a * star k ∈ Her h := by
  let k' : Her h := ⟨k, hk⟩
  change (k' : A) * a * star (k' : A) ∈ Her h
  refine (sandwichMap_dense h).induction_on k'
    ((isClosed_Her h).preimage (by fun_prop)) ?_
  intro b
  change (h * b * star h) * a * star (h * b * star h) ∈ Her h
  convert sandwich_mem_Her h (b * star h * a * h * star b) using 1
  simp only [star_mul, star_star, mul_assoc]

lemma Her_mono_of_mem {h k : A} (hk : k ∈ Her h) : Her k ≤ Her h := by
  apply closure_minimal _ (isClosed_Her h)
  rintro _ ⟨a, rfl⟩
  exact Her_sandwich hk a

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

lemma cut_nonneg (d : A) (ε : ℝ) : 0 ≤ cut d ε := by
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section MoreHer
variable [PartialOrder A] [StarOrderedRing A]

end MoreHer
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section Ramps
variable [PartialOrder A] [StarOrderedRing A]

lemma ramp_mem_Her_cut {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) :
    ramp a l u ∈ Her (cut a l) := by
  have hcomp : ramp a l u = cfcₙ (fun t : ℝ => min 1 (t / (u-l))) (cut a l) := by
    unfold ramp cut
    exact cfcₙ_comp (fun t : ℝ => min 1 (t / (u-l))) (fun t : ℝ => max (t-l) 0) a
      (continuous_const.min (continuous_id.div_const _)).continuousOn (by norm_num)
      ((continuous_id.sub continuous_const).max continuous_const).continuousOn
      (by simp [max_eq_right (neg_nonpos.mpr hl)]) (.of_nonneg ha)
  rw [hcomp]
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her (cut_nonneg a l))

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_fixed_left {h t : A} (ht : t * h = h) {k : A} (hk : k ∈ Her h) : t * k = k := by
  have hc : IsClosed {k : A | t * k = k} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change t * (h * a * star h) = h * a * star h
  simp only [← mul_assoc, ht]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Graph ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
namespace OrthogonalSlots
section GraphAlgebra
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

end GraphAlgebra
end OrthogonalSlots

section UnitalGraph
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end UnitalGraph
lemma Her_fixed_right {h t : A} (hh : IsSelfAdjoint h) (ht : h * t = h)
    {k : A} (hk : k ∈ Her h) : k * t = k := by
  have he : star t * h = h := by
    simpa only [star_mul, hh.star_eq] using congrArg star ht
  have hs := Her_fixed_left he (StarMemClass.star_mem (s := Her h) hk)
  simpa only [star_mul, star_star] using congrArg star hs

section InverseOrder
variable [PartialOrder A] [StarOrderedRing A]

end InverseOrder
section GraphDefect
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end GraphDefect

section GraphConstruction
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable {h a t : D} (V : OrthogonalSlots 6 h a) (ht : 0 ≤ t) (htH : t ∈ Her h)

end GraphConstruction

section AbstractMeasurements
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end AbstractMeasurements

section RepresentedGraph
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
variable (π : D →⋆ₐ[ℂ] E) {h a t : D} (V : OrthogonalSlots 6 h a)
  (ht : 0 ≤ t) (htH : t ∈ Her h)

end RepresentedGraph

end MainGap

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.graphNonvanishingOrder
attribute [local instance] OAI.MainGap.graphNonvanishingStarOrder
attribute [local instance] OAI.MainGap.graphOperatorOrder
attribute [local instance] OAI.MainGap.graphOperatorStarOrder
end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Compression ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma continuous_cutInverseFn {δ : ℝ} (hδ : 0 < δ) : Continuous (cutInverseFn δ) := by
  exact continuous_id.div (((continuous_const.max continuous_id).pow 2))
    (fun t => pow_ne_zero _ (ne_of_gt (hδ.trans_le (le_max_left _ _))))

lemma cutInverseFn_zero (δ : ℝ) : cutInverseFn δ 0=0 := by simp [cutInverseFn]

lemma norm_cutInverse_le {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    ‖cutInverse a δ‖ ≤ 1/δ := by
  apply norm_cfcₙ_le
  intro t ht
  have hb := cutInverseFn_bound hδ (quasispectrum_nonneg_of_nonneg a ha t ht)
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma cut_mul_cutInverse {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    cut a δ * (cutInverse a δ * a) = cut a δ := by
  have hc : Continuous (fun t : ℝ => max (t-δ) 0) := by fun_prop
  have h0 : (fun t : ℝ => max (t-δ) 0) 0=0 := by
    simp [max_eq_right (neg_nonpos.mpr hδ.le)]
  have he : cutInverse a δ*a = cfcₙ (fun t : ℝ => cutInverseFn δ t*t) a := by
    simpa only [id_eq, cfcₙ_id ℝ a ha.isSelfAdjoint, cfcₙ_id' ℝ a ha.isSelfAdjoint, cutInverse] using
      (cfcₙ_mul (cutInverseFn δ) id a (continuous_cutInverseFn hδ).continuousOn
        (cutInverseFn_zero δ) continuousOn_id rfl).symm
  rw [he, cut, ← cfcₙ_mul (fun t : ℝ => max (t-δ) 0)
    (fun t : ℝ => cutInverseFn δ t*t) a hc.continuousOn h0
    ((continuous_cutInverseFn hδ).mul continuous_id).continuousOn (by simp [cutInverseFn_zero])]
  apply cfcₙ_congr
  intro t _
  dsimp only
  by_cases ht : t ≤ δ
  · rw [max_eq_right (sub_nonpos.mpr ht), zero_mul]
  · have ht0 : t ≠ 0 := ne_of_gt (hδ.trans (lt_of_not_ge ht))
    dsimp [cutInverseFn]
    rw [max_eq_right (le_of_not_ge ht)]
    field_simp

lemma Her_right_fixed_cutInverse {a x : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ)
    (hx : x ∈ Her (cut a δ)) : x*(cutInverse a δ*a)=x :=
  Her_fixed_right (cut_nonneg a δ).isSelfAdjoint (cut_mul_cutInverse ha hδ) hx

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma compression_of_conditional_loss {p q c : A} (hp : 0 ≤ p) {τ r : ℝ}
    (hτ : 0 < τ) (_hr : 0 ≤ r)
    (h : ∀ k : A, k ∈ Her q → ‖p*c*k‖ ≤ r*‖k‖) :
    HerCompression (ramp p τ 1) q c (r/τ) := by
  intro x hx k hk
  have hxH : x ∈ Her (cut p τ) :=
    Her_mono_of_mem (ramp_mem_Her_cut hp hτ.le) hx
  have hfix : x*(cutInverse p τ*p)=x := Her_right_fixed_cutInverse hp hτ hxH
  have he : x*c*k = (x*cutInverse p τ)*(p*c*k) := by
    calc
      x*c*k = (x*(cutInverse p τ*p))*c*k := by rw [hfix]
      _ = _ := by simp only [mul_assoc]
  rw [he]
  calc
    ‖(x*cutInverse p τ)*(p*c*k)‖ ≤ ‖x*cutInverse p τ‖*‖p*c*k‖ := norm_mul_le _ _
    _ ≤ (‖x‖*(1/τ))*(r*‖k‖) := by
      apply mul_le_mul
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_cutInverse_le hp hτ) (norm_nonneg x))
      · exact h k hk
      · exact norm_nonneg _
      · positivity
    _ = (r/τ)*‖x‖*‖k‖ := by ring

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.compression_of_conditional_loss := @_root_.OAI.MainGap.compression_of_conditional_loss
