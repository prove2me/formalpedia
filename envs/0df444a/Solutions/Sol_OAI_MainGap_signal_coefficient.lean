-- Prove2me | solution 1 for OAI.MainGap.signal_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:32:08.535774+00:00
-- url     : https://prove2.me/submissions/b7abf150-8f43-4772-b09d-18a74bf0da18

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Signal.lean:L114-L149
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.signal_coefficient. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_Her_cut_lower
import Theorems.Thm_OAI_MainGap_closedIdeal_comparison
import Theorems.Thm_OAI_MainGap_exists_rep_killing_ideal
import Theorems.Thm_OAI_MainGap_norm_sub_cut_le
import Theorems.Thm_OAI_MainGap_scalarCuntzLE_of_inr

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.ClosedIdeal ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]

lemma idealSpan_right {v z : A} (hz : z ∈ idealSpan v) (a : A) : z * a ∈ idealSpan v := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, y, rfl⟩ := hz
    simpa only [mul_assoc] using idealSpan_word v x (y * a)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [add_mul] using (idealSpan v).add_mem ihx ihy
  | smul c x hx ih => simpa only [smul_mul_assoc] using (idealSpan v).smul_mem c ih

lemma closedIdeal_word (v : A) (hv : IsSelfAdjoint v) (x y : A) :
    x * v * y ∈ closedIdeal v hv := subset_closure (idealSpan_word v x y)

lemma self_mem_closedIdeal (v : A) (hv : IsSelfAdjoint v) : v ∈ closedIdeal v hv := by
  simpa using closedIdeal_word v hv 1 1

lemma closedIdeal_left {v z : A} (hv : IsSelfAdjoint v) (hz : z ∈ closedIdeal v hv) (a : A) :
    a * z ∈ closedIdeal v hv := by
  refine (closedIdeal_closed v hv).preimage (continuous_const.mul continuous_id)
    |>.closure_subset_iff.mpr (fun x hx => subset_closure (idealSpan_left hx a)) hz

lemma closedIdeal_right {v z : A} (hv : IsSelfAdjoint v) (hz : z ∈ closedIdeal v hv) (a : A) :
    z * a ∈ closedIdeal v hv := by
  refine (closedIdeal_closed v hv).preimage (continuous_id.mul continuous_const)
    |>.closure_subset_iff.mpr (fun x hx => subset_closure (idealSpan_right hx a)) hz

end MainGap

end

end OAI

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

lemma norm_mem_quasispectrum_of_nonneg {a : A} (ha : 0 ≤ a) :
    ‖a‖ ∈ quasispectrum ℝ a := by
  simpa using quasispectrum.algebraMap_mem ℝ
    (NonUnitalIsometricContinuousFunctionalCalculus.isGreatest_quasispectrum a ha).1

lemma continuous_rampFn (l u : ℝ) : Continuous (rampFn l u) :=
  continuous_const.min (((continuous_id.sub continuous_const).max continuous_const).div_const _)

lemma rampFn_nonneg {l u t : ℝ} (hlu : l ≤ u) : 0 ≤ rampFn l u t :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) (sub_nonneg.mpr hlu))

lemma rampFn_le_one (l u t : ℝ) : rampFn l u t ≤ 1 := min_le_left _ _

lemma rampFn_zero {l u t : ℝ} (ht : t ≤ l) : rampFn l u t = 0 := by
  simp only [rampFn, max_eq_right (sub_nonpos.mpr ht), zero_div, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]

lemma rampFn_one {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) : rampFn l u t = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
  rw [one_mul, max_eq_left (sub_nonneg.mpr (hlu.le.trans ht))]
  linarith

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_ramp_le_one (a : A) {l u : ℝ} (hlu : l ≤ u) : ‖ramp a l u‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t _
  rw [Real.norm_eq_abs, abs_of_nonneg (rampFn_nonneg hlu)]
  exact rampFn_le_one _ _ _

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

lemma norm_ramp_eq_one {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l)
    (hlu : l < u) (hu : u ≤ ‖a‖) : ‖ramp a l u‖ = 1 := by
  apply le_antisymm (norm_ramp_le_one a hlu.le)
  have ht := norm_apply_le_norm_cfcₙ (rampFn l u) a
    (norm_mem_quasispectrum_of_nonneg ha) (continuous_rampFn l u).continuousOn
    (rampFn_zero hl) (.of_nonneg ha)
  change 1 ≤ ‖cfcₙ (rampFn l u) a‖
  simpa only [rampFn_one hlu hu, norm_one] using ht

lemma map_ramp {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) :
    π (ramp a l u) = ramp (π a) l u :=
  π.map_cfcₙ (rampFn l u) a (continuous_rampFn l u).continuousOn (rampFn_zero hl)
    (map_continuous π) (.of_nonneg ha) (.of_nonneg (map_nonneg π ha))

lemma map_cut {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l) :
    π (cut a l) = cut (π a) l :=
  π.map_cfcₙ (fun t : ℝ => max (t-l) 0) a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)]) (map_continuous π)
    (.of_nonneg ha) (.of_nonneg (map_nonneg π ha))

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Nonvanishing ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.nonvanishingPartialOrder
attribute [local instance] OAI.MainGap.nonvanishingStarOrderedRing
attribute [local instance] OAI.MainGap.nonvanishingOperatorPartialOrder
attribute [local instance] OAI.MainGap.nonvanishingOperatorStarOrderedRing
lemma cut_eq_zero_of_norm_le {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : ‖a‖ ≤ l) :
    cut a l = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  change ‖cfcₙ (fun t : ℝ => max (t-l) 0) a‖ ≤ 0
  apply norm_cfcₙ_le
  intro r hr
  have hb := NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a hr
    ha.isSelfAdjoint
  have hb' : |r| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using hb
  have ht : r ≤ l := (le_abs_self r).trans (hb'.trans hl)
  rw [max_eq_right (sub_nonpos.mpr ht), norm_zero]

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Shrinking ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingPartialOrder
attribute [local instance] OAI.MainGap.shrinkingStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingOperatorPartialOrder
attribute [local instance] OAI.MainGap.shrinkingOperatorStarOrderedRing
end MainGap

namespace MainGap
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma matrixMap_mul (π : A →⋆ₙₐ[ℂ] B) {l m n : ℕ}
    (x : CStarMatrix (Fin l) (Fin m) A) (y : CStarMatrix (Fin m) (Fin n) A) :
    matrixMap π (x*y)=matrixMap π x * matrixMap π y := by
  ext i j
  change π (∑ k, x i k * y k j) = ∑ k, π (x i k) * π (y k j)
  simp only [map_sum, map_mul]

lemma matrixMap_star (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ}
    (x : CStarMatrix (Fin m) (Fin n) A) :
    matrixMap π x.conjTranspose=(matrixMap π x).conjTranspose := by
  ext i j
  change π (star (x j i)) = star (π (x j i))
  exact map_star π _

lemma continuous_matrixMap (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ} :
    Continuous (matrixMap π : CStarMatrix (Fin m) (Fin n) A → CStarMatrix (Fin m) (Fin n) B) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (map_continuous π).comp ((continuous_apply j).comp (continuous_apply i))

lemma FiniteCuntzLE.map (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ}
    {d : CStarMatrix (Fin n) (Fin n) A} {v : CStarMatrix (Fin m) (Fin m) A}
    (h : FiniteCuntzLE d v) : FiniteCuntzLE (matrixMap π d) (matrixMap π v) := by
  obtain ⟨r,ht⟩ := h
  refine ⟨fun j => matrixMap π (r j), ?_⟩
  have he := (continuous_matrixMap π).continuousAt.tendsto.comp ht
  change Tendsto (fun j => matrixMap π ((r j).conjTranspose * v * r j)) atTop (𝓝 (matrixMap π d)) at he
  simpa only [matrixMap_mul, matrixMap_star] using he

lemma ProperlyInfinite.map (π : A →⋆ₙₐ[ℂ] B) {h : A} (hh : ProperlyInfinite h) :
    ProperlyInfinite (π h) := by
  have he := FiniteCuntzLE.map π hh
  have hdouble : matrixMap π (doubleCorner h)=doubleCorner (π h) := by
    ext i j
    change π (if i=j then h else 0) = if i=j then π h else 0
    split_ifs <;> simp
  have hsingle : matrixMap π (scalarCorner h)=scalarCorner (π h) := rfl
  change FiniteCuntzLE _ _
  rwa [hdouble, hsingle] at he

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingHerPartialOrder
attribute [local instance] OAI.MainGap.shrinkingHerStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingHerUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingHerUnitizationStarOrderedRing
end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingNonunitalPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationStarOrderedRing
end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.IdealDetection ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.idealDetectionOrder
attribute [local instance] OAI.MainGap.idealDetectionStarOrder
lemma ScalarCuntzLE.exists_approx {u v : A} (h : ScalarCuntzLE u v)
    {ε : ℝ} (hε : 0 < ε) : ∃ w : A, ‖star w * v * w - u‖ < ε := by
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := Metric.mem_closure_iff.mp h ε hε
  exact ⟨w, by simpa only [dist_eq_norm, norm_sub_rev] using hw⟩

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Signal ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalCutPartialOrder
attribute [local instance] OAI.MainGap.signalCutStarOrderedRing
lemma norm_cut_le_sub {a : A} (ha : 0 ≤ a) {M δ : ℝ} (han : ‖a‖ ≤ M)
    (hδ : δ ≤ M) : ‖cut a δ‖ ≤ M - δ := by
  apply norm_cfcₙ_le
  intro t ht
  have htM : t ≤ M := (le_abs_self t).trans
    ((NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a ht ha.isSelfAdjoint).trans han)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) (sub_nonneg.mpr hδ)

end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalComparisonPartialOrder
attribute [local instance] OAI.MainGap.signalComparisonStarOrderedRing
attribute [local instance] OAI.MainGap.signalOperatorPartialOrder
attribute [local instance] OAI.MainGap.signalOperatorStarOrderedRing
lemma signal_cut_comparison (hP : PropertyP A) {a p : A} (ha : 0 ≤ a) {δ : ℝ}
    (hδ : 0 < δ) (hpH : p ∈ Her (ramp a δ (2*δ)))
    (hsignal : NormSignal (ramp a δ (2*δ)) p) :
    ScalarCuntzLE (cut a (2*δ)) (star p * a * p) := by
  let v := star p * a * p
  have hv : 0 ≤ v := star_left_conjugate_nonneg ha p
  let V : Unitization ℂ A := Unitization.inr v
  have hV : 0 ≤ V := Unitization.inr_nonneg_iff.mpr hv
  let J := closedIdeal V hV.isSelfAdjoint
  have hcut : (Unitization.inr (cut a (2*δ)) : Unitization ℂ A) ∈ J := by
    by_contra hh
    obtain ⟨R,hRJ,hRcut⟩ := exists_rep_killing_ideal J
      (closedIdeal_closed V hV.isSelfAdjoint)
      (fun x z hz => closedIdeal_left hV.isSelfAdjoint hz x)
      (fun x z hz => closedIdeal_right hV.isSelfAdjoint hz x) hh
    let π := R.hom.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
    have hvzero : π v = 0 := hRJ V (self_mem_closedIdeal V hV.isSelfAdjoint)
    have hlower := Her_cut_lower ha hδ.le
      (Her_mono_of_mem (ramp_mem_Her_cut ha hδ.le) hpH)
    have hpos := map_nonneg π (sub_nonneg.mpr hlower)
    have hsmul (r : ℝ) (z : A) : π (r • z)=r • π z :=
      LinearMapClass.map_smul_of_tower π r z
    change 0 ≤ π (v - δ • (star p * p)) at hpos
    rw [map_sub, hvzero, hsmul, map_mul, map_star] at hpos
    have hz : δ • (star (π p) * π p) = 0 :=
      le_antisymm (by simpa only [zero_sub, neg_nonneg] using hpos)
        (smul_nonneg hδ.le (star_mul_self_nonneg _))
    have hpzero : π p = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp
      ((smul_eq_zero.mp hz).resolve_left hδ.ne')
    have hnorm : 2*δ < ‖π a‖ := by
      by_contra! hn
      apply hRcut
      change π (cut a (2*δ)) = 0
      rw [map_cut π ha (by positivity), cut_eq_zero_of_norm_le (map_nonneg π ha) hn]
    have hramp : ‖π (ramp a δ (2*δ))‖ = 1 := by
      rw [map_ramp π ha hδ.le]
      exact norm_ramp_eq_one (map_nonneg π ha) hδ.le (by linarith) hnorm.le
    have hpn := hsignal R (by change (1/2:ℝ) < ‖π (ramp a δ (2*δ))‖; rw [hramp]; norm_num)
    change ‖π p‖ = 1 at hpn
    rw [hpzero, norm_zero] at hpn
    norm_num at hpn
  apply scalarCuntzLE_of_inr hv
  exact closedIdeal_comparison (Unitization.inr_nonneg_iff.mpr (cut_nonneg _ _)) hV
    ((hP v hv).map (Unitization.inrNonUnitalStarAlgHom ℂ A)) hcut

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalCoefficientPartialOrder
attribute [local instance] OAI.MainGap.signalCoefficientStarOrderedRing
lemma signal_coefficient (hP : PropertyP A) {a p : A} (ha : 0 ≤ a) (han : ‖a‖ ≤ 1)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1/2) (hρ : 0 < ρ) (hρδ : ρ ≤ 2*δ)
    (hpH : p ∈ Her (ramp a δ (2*δ))) (hsignal : NormSignal (ramp a δ (2*δ)) p) :
    ∃ w : A, ‖star (p*w)*a*(p*w)-a‖ < 2*δ+ρ ∧
      ‖p*w‖ ≤ Real.sqrt δ⁻¹ := by
  have hcomp := signal_cut_comparison hP ha hδ hpH hsignal
  obtain ⟨w,hw⟩ := hcomp.exists_approx hρ
  have hw' : ‖star (p*w)*a*(p*w) - cut a (2*δ)‖ < ρ := by
    simpa only [star_mul, mul_assoc] using hw
  refine ⟨w, ?_, ?_⟩
  · calc
      ‖star (p*w)*a*(p*w)-a‖ ≤
          ‖star (p*w)*a*(p*w)-cut a (2*δ)‖ + ‖cut a (2*δ)-a‖ := by simpa only [dist_eq_norm] using dist_triangle (star (p*w)*a*(p*w)) (cut a (2*δ)) a
      _ < ρ + 2*δ := add_lt_add_of_lt_of_le hw'
        (by simpa only [norm_sub_rev] using norm_sub_cut_le ha (by positivity : 0 ≤ 2*δ))
      _ = 2*δ+ρ := by ring
  · have hlower := star_left_conjugate_le_conjugate
      (Her_cut_lower ha hδ.le (Her_mono_of_mem (ramp_mem_Her_cut ha hδ.le) hpH)) w
    have hlower' : δ • (star (p*w)*(p*w)) ≤ star (p*w)*a*(p*w) := by
      simpa only [star_mul, mul_smul_comm, smul_mul_assoc, mul_assoc] using hlower
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hlower'
      (smul_nonneg hδ.le (star_mul_self_nonneg (p*w)))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hδ, CStarRing.norm_star_mul_self] at hn
    have hupper : ‖star (p*w)*a*(p*w)‖ < 1 := by
      calc
        ‖star (p*w)*a*(p*w)‖ ≤
            ‖star (p*w)*a*(p*w)-cut a (2*δ)‖ + ‖cut a (2*δ)‖ := norm_le_norm_sub_add _ _
        _ < ρ + (1-2*δ) := add_lt_add_of_lt_of_le hw'
          (norm_cut_le_sub ha han (by linarith))
        _ ≤ 1 := by linarith
    have hsq : ‖p*w‖ ^ 2 ≤ δ⁻¹ := by
      have hh : δ * (‖p*w‖ ^ 2) ≤ 1 := by nlinarith
      have hh' := (le_inv_mul_iff₀ hδ).mpr hh
      simpa only [mul_one] using hh'
    have hsqrt := Real.sq_sqrt (inv_nonneg.mpr hδ.le)
    nlinarith [Real.sqrt_nonneg δ⁻¹, norm_nonneg (p*w)]

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.signalProductsPartialOrder
attribute [local instance] OAI.MainGap.signalProductsStarOrderedRing
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.signalCoefficientPartialOrder
attribute [local instance] OAI.MainGap.signalCoefficientStarOrderedRing


theorem solution : type_of% @_root_.OAI.MainGap.signal_coefficient := @_root_.OAI.MainGap.signal_coefficient
