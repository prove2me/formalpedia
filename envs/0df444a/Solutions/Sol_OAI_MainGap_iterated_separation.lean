-- Prove2me | solution 1 for OAI.MainGap.iterated_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:19:31.957842+00:00
-- url     : https://prove2.me/submissions/3c76a69e-0d76-470d-bcda-84e85fbf47ff

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Separation.lean:L66-L109
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.iterated_separation. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_ramp_mul_cut
import Theorems.Thm_OAI_MainGap_uniform_shrinking

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

lemma cut_mem_Her {d : A} (hd : 0 ≤ d) (ε : ℝ) : cut d ε ∈ Her d := by
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her hd)

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

lemma ramp_nonneg (a : A) {l u : ℝ} (hlu : l ≤ u) : 0 ≤ ramp a l u :=
  cfcₙ_nonneg (fun _ _ => rampFn_nonneg hlu)

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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Separation ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.separationPartialOrder
attribute [local instance] OAI.MainGap.separationStarOrderedRing
lemma ramp_mem_Her {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) :
    ramp a l u ∈ Her a :=
  Her_mono_of_mem (cut_mem_Her ha l) (ramp_mem_Her_cut ha hl)

lemma NormSignal.cutoff_ramp {a p : A} (h : NormSignal a p) (hp : 0 ≤ p) :
    NormSignal a (ramp p (1/2) 1) := by
  intro R hR
  let π := R.hom.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  change ‖π (ramp p (1/2) 1)‖=1
  rw [map_ramp π hp (by norm_num : (0:ℝ)≤1/2)]
  apply norm_ramp_eq_one (map_nonneg π hp) (by norm_num) (by norm_num)
  exact (h R hR).symm.le

lemma iteration_step {p q c : A} {r θ : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 < r) (_h : HerCompression p q c r)
    {p' q' : A} (hp'H : p' ∈ Her (ramp p (1/2) 1))
    (hq'H : q' ∈ Her (ramp q (1/2) 1))
    (h' : HerCompression p' q'
      (r⁻¹ • (ramp p (1/4) (1/2)*c*ramp q (1/4) (1/2))) θ) :
    HerCompression p' q' c (r*θ) := by
  have hpg : ramp p (1/4) (1/2)*cut p (1/2)=cut p (1/2) :=
    ramp_mul_cut hp (by norm_num) (by norm_num) le_rfl
  have hqg : ramp q (1/4) (1/2)*cut q (1/2)=cut q (1/2) :=
    ramp_mul_cut hq (by norm_num) (by norm_num) le_rfl
  have hpg' : cut p (1/2)*ramp p (1/4) (1/2)=cut p (1/2) := by
    simpa only [star_mul, (cut_nonneg p (1/2)).isSelfAdjoint.star_eq,
      (ramp_nonneg p (by norm_num : (1/4:ℝ)≤1/2)).isSelfAdjoint.star_eq] using congrArg star hpg
  intro x hx k hk
  have hxcut : x ∈ Her (cut p (1/2)) :=
    Her_mono_of_mem (ramp_mem_Her_cut hp (by norm_num : (0:ℝ)≤1/2))
      (Her_mono_of_mem hp'H hx)
  have hkcut : k ∈ Her (cut q (1/2)) :=
    Her_mono_of_mem (ramp_mem_Her_cut hq (by norm_num : (0:ℝ)≤1/2))
      (Her_mono_of_mem hq'H hk)
  have hxg := Her_fixed_right (cut_nonneg p (1/2)).isSelfAdjoint hpg' hxcut
  have hgk := Her_fixed_left hqg hkcut
  have he : x*(r⁻¹ • (ramp p (1/4) (1/2)*c*ramp q (1/4) (1/2)))*k =
      r⁻¹ • (x*c*k) := by
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [mul_assoc, ← mul_assoc x (ramp p (1/4) (1/2)), hxg, hgk]
  have hb := h' x hx k hk
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hb
  have hbr := mul_le_mul_of_nonneg_left hb hr.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hbr

theorem iterated_separation (hp : PropertyP A) {a b c : A} (ha : 0 ≤ a) (han : ‖a‖ ≤ 1)
    (hb : 0 ≤ b) (hbn : ‖b‖ ≤ 1) (hcn : ‖c‖ ≤ 1) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ (p q : A) (κ : ℝ), 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her b ∧ 0 ≤ κ ∧ κ < ζ ∧
      HerCompression p q c κ ∧ NormSignal a p ∧ NormSignal b q := by
  obtain ⟨θ,hθ0,hθ1,huniform⟩ := uniform_shrinking hp
  have hi : ∀ n : ℕ, ∃ p q : A, 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her b ∧
      HerCompression p q c (θ^(n+1)) ∧ NormSignal a p ∧ NormSignal b q := by
    intro n
    induction n with
    | zero => simpa only [Nat.zero_add, pow_one] using huniform a b c ha han hb hbn hcn
    | succ n ih =>
      obtain ⟨p,q,hp0,hpn,hpH,hq0,hqn,hqH,hcomp,hps,hqs⟩ := ih
      let f : A → A := fun p => ramp p (1/2) 1
      let g : A → A := fun p => ramp p (1/4) (1/2)
      let r := θ^(n+1)
      have hr : 0 < r := pow_pos hθ0 _
      have hgH (p : A) (hp : 0 ≤ p) : g p ∈ Her p := ramp_mem_Her hp (by norm_num)
      have hgn (p : A) : ‖g p‖ ≤ 1 := norm_ramp_le_one p (by norm_num)
      have hf0 (p : A) : 0 ≤ f p := ramp_nonneg p (by norm_num)
      have hfn (p : A) : ‖f p‖ ≤ 1 := norm_ramp_le_one p (by norm_num)
      have hc' : ‖r⁻¹ • (g p*c*g q)‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        have hh : ‖g p*c*g q‖ ≤ r := (hcomp _ (hgH p hp0) _ (hgH q hq0)).trans (by
          calc r*‖g p‖*‖g q‖ ≤ r*1*1 := by gcongr <;> apply hgn
               _ = r := by ring)
        calc r⁻¹*‖g p*c*g q‖ ≤ r⁻¹*r := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hr.le)
             _ = 1 := inv_mul_cancel₀ hr.ne'
      obtain ⟨p',q',hp'0,hp'n,hp'H,hq'0,hq'n,hq'H,hcomp',hps',hqs'⟩ :=
        huniform (f p) (f q) (r⁻¹ • (g p*c*g q)) (hf0 p) (hfn p) (hf0 q) (hfn q) hc'
      refine ⟨p',q',hp'0,hp'n,?_,hq'0,hq'n,?_,?_,?_,?_⟩
      · exact Her_mono_of_mem hpH (Her_mono_of_mem (ramp_mem_Her hp0 (by norm_num)) hp'H)
      · exact Her_mono_of_mem hqH (Her_mono_of_mem (ramp_mem_Her hq0 (by norm_num)) hq'H)
      · have hh := iteration_step hp0 hq0 hr hcomp hp'H hq'H hcomp'
        simpa only [r, pow_succ] using hh
      · intro R hR
        exact hps' R (by rw [hps.cutoff_ramp hp0 R hR]; norm_num)
      · intro R hR
        exact hqs' R (by rw [hqs.cutoff_ramp hq0 R hR]; norm_num)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hζ hθ1
  obtain ⟨p,q,hp0,hpn,hpH,hq0,hqn,hqH,hcomp,hps,hqs⟩ := hi n
  refine ⟨p,q,θ^(n+1),hp0,hpn,hpH,hq0,hqn,hqH,(pow_pos hθ0 _).le,?_,hcomp,hps,hqs⟩
  exact (by rw [pow_succ]; nlinarith [pow_pos hθ0 n] : θ^(n+1)≤θ^n).trans_lt hn
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.separationPartialOrder
attribute [local instance] OAI.MainGap.separationStarOrderedRing


theorem solution.{u} : type_of% @_root_.OAI.MainGap.iterated_separation.{u} := @_root_.OAI.MainGap.iterated_separation.{u}
