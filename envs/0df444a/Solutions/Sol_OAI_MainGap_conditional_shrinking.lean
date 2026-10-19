-- Prove2me | solution 1 for OAI.MainGap.conditional_shrinking
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:10:19.213921+00:00
-- url     : https://prove2.me/submissions/a35edf1d-7155-41f8-a144-a62f163a34ef

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Shrinking.lean:L21-L84
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.conditional_shrinking. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_compression_of_conditional_loss
import Theorems.Thm_OAI_MainGap_conditional_Her_loss
import Theorems.Thm_OAI_MainGap_conditional_defect_bounds
import Theorems.Thm_OAI_MainGap_conditional_q_zero
import Theorems.Thm_OAI_MainGap_quantitative_nonvanishing
import Theorems.Thm_OAI_MainGap_quantitative_nonvanishing_general

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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.FourChoices ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourChoicesPartialOrder
attribute [local instance] OAI.MainGap.fourChoicesStarOrderedRing
end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
attribute [local instance] OAI.MainGap.fourChoicesMapDomainOrder
attribute [local instance] OAI.MainGap.fourChoicesMapDomainStarOrder
attribute [local instance] OAI.MainGap.fourChoicesMapCodomainOrder
attribute [local instance] OAI.MainGap.fourChoicesMapCodomainStarOrder
variable (π : A →⋆ₐ[ℂ] D)

lemma map_cut_sa {a : A} (ha : IsSelfAdjoint a) {l : ℝ} (hl : 0 ≤ l) :
    π (cut a l) = cut (π a) l :=
  π.toNonUnitalStarAlgHom.map_cfcₙ (fun t : ℝ => max (t-l) 0) a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)]) (map_continuous π) ha (ha.map π)

lemma map_ramp_sa {a : A} (ha : IsSelfAdjoint a) {l u : ℝ} (hl : 0 ≤ l) :
    π (ramp a l u) = ramp (π a) l u :=
  π.toNonUnitalStarAlgHom.map_cfcₙ (rampFn l u) a
    (continuous_rampFn l u).continuousOn (rampFn_zero hl)
    (map_continuous π) ha (ha.map π)

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourChoiceStructureOrder
attribute [local instance] OAI.MainGap.fourChoiceStructureStarOrder
universe v

namespace FourChoice
variable {X : A} {B : Fin 4 → A} {E : Finset A} {η : ℝ} (F : FourChoice.{v, _} X B E η)

variable {D : Type v} [CStarAlgebra D]
attribute [local instance] OAI.MainGap.FourChoice.fourChoiceRepresentationOrder
attribute [local instance] OAI.MainGap.FourChoice.fourChoiceRepresentationStarOrder
variable (π : A →⋆ₐ[ℂ] D) (hX : 0 ≤ X) (hη : 0 < η)
  (hmatch : ∀ i, π (F.T i) = π (B i))

end FourChoice
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
theorem conditional_shrinking {a y c p : A} (_ha : 0 ≤ a) (hy : 0 ≤ y)
    (hp : 0 ≤ p) (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    (hpH : p ∈ Her a)
    (hsignal : ∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom a‖ → ‖R.hom p‖=1)
    (hvan : ∀ R : HilbertRep.{u,u} A,
      R.hom (y*(1-star c*(p*p)*c)*y)=0 → ‖R.hom y‖ ≤ (1/4:ℝ)) :
    ∃ (p₁ q₁ : A) (κ : ℝ), 0 ≤ p₁ ∧ ‖p₁‖ ≤ 1 ∧ p₁ ∈ Her a ∧
      0 ≤ q₁ ∧ ‖q₁‖ ≤ 1 ∧ q₁ ∈ Her y ∧ 0 ≤ κ ∧ κ < 1 ∧
      HerCompression p₁ q₁ c κ ∧
      (∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom a‖ → ‖R.hom p₁‖=1) ∧
      (∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom y‖ → ‖R.hom q₁‖=1) := by
  obtain ⟨δ,hδ,hδ₁,hquant⟩ := quantitative_nonvanishing hy hvan
  let d := y*(1-star c*(p*p)*c)*y
  have hd : 0 ≤ d := (conditional_defect_bounds hp hy hpn hyn hcn).1
  let q := y*cut d δ*y
  have hq : 0 ≤ q := by
    simpa only [hy.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg (cut_nonneg d δ) y
  have hqH : q ∈ Her y := by
    simpa only [hy.isSelfAdjoint.star_eq] using sandwich_mem_Her y (cut d δ)
  have hqvan (R : HilbertRep.{u,u} A) (hz : R.hom q=0) : ‖R.hom y‖ ≤ (3/8:ℝ) := by
    have hqzero : R.hom y * cut (R.hom y*(1-star (R.hom c)*(R.hom p*R.hom p)*R.hom c)*R.hom y) δ * R.hom y=0 := by
      change R.hom (y*cut d δ*y)=0 at hz
      rw [map_mul, map_mul, map_cut_sa R.hom hd.isSelfAdjoint hδ.le] at hz
      simpa only [d, map_mul, map_sub, map_one, map_star] using hz
    have hb := conditional_q_zero (map_nonneg R.hom hp) (map_nonneg R.hom hy)
      ((NonUnitalStarAlgHom.norm_apply_le R.hom p).trans hpn)
      ((NonUnitalStarAlgHom.norm_apply_le R.hom y).trans hyn)
      ((NonUnitalStarAlgHom.norm_apply_le R.hom c).trans hcn) hδ hqzero
    have hb' : ‖R.hom d‖ ≤ δ := by
      simpa only [d, map_mul, map_sub, map_one, map_star] using hb
    by_contra! hRy
    exact (not_lt_of_ge hb') (hquant R hRy)
  obtain ⟨δ',hδ',hδ'₁,hquant'⟩ := quantitative_nonvanishing_general hy
    (by norm_num : (0:ℝ)≤3/8) (by norm_num : (3/8:ℝ)<1/2) hqvan
  let r := Real.sqrt (1-δ)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr₁ : r < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr
    linarith
  let τ := (r+1)/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hrτ : r < τ := by dsimp [τ]; linarith
  have hτ₁ : τ < 1 := by dsimp [τ]; linarith
  let p₁ := ramp p τ 1
  let q₁ := ramp q (δ'/2) δ'
  have hp₁ : 0 ≤ p₁ := ramp_nonneg p hτ₁.le
  have hq₁ : 0 ≤ q₁ := ramp_nonneg q (by linarith)
  have hq₁H : q₁ ∈ Her q :=
    Her_mono_of_mem (cut_mem_Her hq (δ'/2)) (ramp_mem_Her_cut hq (by positivity))
  refine ⟨p₁,q₁,r/τ,hp₁,norm_ramp_le_one p hτ₁.le,?_,hq₁,
    norm_ramp_le_one q (by linarith),Her_mono_of_mem hqH hq₁H,
    div_nonneg hr hτ.le,(div_lt_one hτ).mpr hrτ,?_,?_,?_⟩
  · exact Her_mono_of_mem hpH (Her_mono_of_mem (cut_mem_Her hp τ) (ramp_mem_Her_cut hp hτ.le))
  · have hcomp := compression_of_conditional_loss hp hτ hr (conditional_Her_loss hp hy hpn hyn hcn hδ.le hδ₁.le)
    intro x hx k hk
    exact hcomp x hx k (Her_mono_of_mem hq₁H hk)
  · intro R hRa
    change ‖R.hom (ramp p τ 1)‖=1
    rw [map_ramp_sa R.hom hp.isSelfAdjoint hτ.le]
    exact norm_ramp_eq_one (map_nonneg R.hom hp) hτ.le hτ₁ (by rw [hsignal R hRa])
  · intro R hRy
    change ‖R.hom (ramp q (δ'/2) δ')‖=1
    rw [map_ramp_sa R.hom hq.isSelfAdjoint (by positivity)]
    exact norm_ramp_eq_one (map_nonneg R.hom hq) (by positivity) (by linarith) (hquant' R hRy).le

end MainGap

namespace MainGap
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

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

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.shrinkingPartialOrder
attribute [local instance] OAI.MainGap.shrinkingStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingOperatorPartialOrder
attribute [local instance] OAI.MainGap.shrinkingOperatorStarOrderedRing


theorem solution.{u} : type_of% @_root_.OAI.MainGap.conditional_shrinking.{u} := @_root_.OAI.MainGap.conditional_shrinking.{u}
