-- Prove2me | solution 1 for OAI.MainGap.four_limit_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:44:55.790317+00:00
-- url     : https://prove2.me/submissions/33e3055e-be32-44a9-ab14-3b0961c611cb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Avoidance.lean:L25-L85
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.four_limit_impossible. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_four_fixed_impossible
import Theorems.Thm_OAI_MainGap_limitRep_annihilates
import Theorems.Thm_OAI_MainGap_limitRep_nonzero
import Theorems.Thm_OAI_MainGap_norm_sub_cut_le

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Representation ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

section Ultra
variable {ι : Type*} (ω : Ultrafilter ι)

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
variable (f : ι → A →ₚ[ℂ] ℂ) (hf : ∀ i a, ‖f i a‖ ≤ ‖a‖)

end Ultra

section GNS
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

end GNS

section Vector
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

end Vector

section LimitRep
variable {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
variable (ω : Ultrafilter ι) (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
  (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)

end LimitRep
end MainGap

noncomputable section
open scoped Topology ComplexOrder InnerProductSpace
namespace MainGap

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : A)

lemma range_mem_generatedRange (y : H) : π v y ∈ generatedRange π v := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1, y, by simp⟩

lemma rangeRestriction_kills (u : A) (hu : ∀ a : A, π u * π a * π v = 0) :
    rangeRestriction π v u = 0 := by
  have hle : generatedRange π v ≤ (π u).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro x ⟨a, y, rfl⟩
      change π u (π a (π v y)) = 0
      have := congrArg (fun T : H →L[ℂ] H => T y) (hu a)
      simpa using this
    · exact (π u).isClosed_ker
  ext x
  exact hle x.property

lemma rangeRestriction_nonzero (hv : IsSelfAdjoint v) (hne : π v ≠ 0) :
    rangeRestriction π v v ≠ 0 := by
  intro h
  apply hne
  apply (CStarRing.star_mul_self_eq_zero_iff (π v)).mp
  have hv' : IsSelfAdjoint (π v) := hv.map π
  rw [hv'.star_eq]
  ext y
  have hy := congrArg (fun T : generatedRange π v →L[ℂ] generatedRange π v =>
    T ⟨π v y, range_mem_generatedRange π v y⟩) h
  have := congrArg (fun x : generatedRange π v => (x : H)) hy
  simpa using this

end MainGap

end
end

end OAI

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

lemma continuous_rampFn (l u : ℝ) : Continuous (rampFn l u) :=
  continuous_const.min (((continuous_id.sub continuous_const).max continuous_const).div_const _)

lemma rampFn_nonneg {l u t : ℝ} (hlu : l ≤ u) : 0 ≤ rampFn l u t :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) (sub_nonneg.mpr hlu))

lemma rampFn_le_one (l u t : ℝ) : rampFn l u t ≤ 1 := min_le_left _ _

lemma rampFn_zero {l u t : ℝ} (ht : t ≤ l) : rampFn l u t = 0 := by
  simp only [rampFn, max_eq_right (sub_nonpos.mpr ht), zero_div, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]

lemma ramp_nonneg (a : A) {l u : ℝ} (hlu : l ≤ u) : 0 ≤ ramp a l u :=
  cfcₙ_nonneg (fun _ _ => rampFn_nonneg hlu)

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_ramp_le_one (a : A) {l u : ℝ} (hlu : l ≤ u) : ‖ramp a l u‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t _
  rw [Real.norm_eq_abs, abs_of_nonneg (rampFn_nonneg hlu)]
  exact rampFn_le_one _ _ _

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma cut_eq_cfc (d : B) {ε : ℝ} (hε : 0 ≤ ε) :
    cut d ε = cfc (fun t : ℝ => max (t - ε) 0) d := by
  unfold cut
  apply cfcₙ_eq_cfc
  · exact ((continuous_id.sub continuous_const).max continuous_const).continuousOn
  · simp [max_eq_right (neg_nonpos.mpr hε)]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.ChoicePairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.choicePairsPartialOrder
attribute [local instance] OAI.MainGap.choicePairsStarOrderedRing
end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma complement_nonneg {H : A} (hH : IsSelfAdjoint H) (hnorm : ‖H‖ ≤ 1) :
    0 ≤ 1 - H * H := by
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (H * H) ?_).mp
  · calc
      ‖H * H‖ = ‖H‖ ^ 2 := hH.norm_mul_self
      _ ≤ 1 := (sq_le_one_iff₀ (norm_nonneg H)).mpr hnorm
  · simpa only [hH.star_eq] using star_mul_self_nonneg H

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.instPartialOrder_oAI
attribute [local instance] OAI.MainGap.instStarOrderedRing_oAI
lemma prospectiveDefect_nonneg (X B : A) : 0 ≤ prospectiveDefect X B :=
  ramp_nonneg _ (by norm_num)
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

lemma map_deficiency {d : A} (hd : IsSelfAdjoint d) :
    π (deficiency d) = deficiency (π d) :=
  π.map_cfc (fun t : ℝ => max (1/2-t) 0) d
    ((continuous_const.sub continuous_id).max continuous_const).continuousOn
    (map_continuous π) hd (hd.map π)

lemma map_sqrt {a : A} (ha : 0 ≤ a) : π (CFC.sqrt a) = CFC.sqrt (π a) :=
  π.toNonUnitalStarAlgHom.map_cfcₙ NNReal.sqrt a (by fun_prop) (by simp)
    (map_continuous π) ha (map_nonneg π ha)

lemma map_firstX {X : A} (hX : IsSelfAdjoint X) : π (firstX X) = firstX (π X) :=
  map_cut_sa π hX (by norm_num)
lemma map_firstV {X : A} (hX : IsSelfAdjoint X) : π (firstV X) = firstV (π X) :=
  map_cut_sa π hX (by norm_num)
lemma map_firstH {X : A} (hX : IsSelfAdjoint X) : π (firstH X) = firstH (π X) :=
  map_ramp_sa π hX (by norm_num)
lemma map_firstK {X : A} (hX : IsSelfAdjoint X) : π (firstK X) = firstK (π X) :=
  map_ramp_sa π hX (by norm_num)

lemma map_firstU {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (firstU X B) = firstU (π X) (π B) := by
  simp only [firstU, map_mul, map_firstX π hX,
    map_deficiency π (.mul_star_self B), map_star]

lemma map_firstR {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (firstR X B) = firstR (π X) (π B) := by
  change π ((Real.sqrt 2) • (star B * firstH X)) = _
  calc
    π ((Real.sqrt 2) • (star B * firstH X)) = (Real.sqrt 2) • π (star B * firstH X) :=
      π.toAlgHom.map_smul_of_tower _ _
    _ = firstR (π X) (π B) := by simp only [firstR, map_mul, map_star, map_firstH π hX]

lemma map_scalingComplement {H : A} (hH : IsSelfAdjoint H) (hn : ‖H‖ ≤ 1) :
    π (scalingComplement H) = scalingComplement (π H) := by
  simp only [scalingComplement, map_sqrt π (complement_nonneg hH hn), map_sub, map_one, map_mul]

lemma map_scalingDefect {H : A} (hH : IsSelfAdjoint H) (hn : ‖H‖ ≤ 1) (r : A) :
    π (scalingDefect H r) = scalingDefect (π H) (π r) := by
  simp only [scalingDefect, scalingIsometry, map_sub, map_mul, map_star, map_one, map_add,
    map_scalingComplement π hH hn]

lemma scalingDefect_selfAdjoint (H r : A) : IsSelfAdjoint (scalingDefect H r) :=
  (IsSelfAdjoint.one A).sub (.mul_star_self _)

lemma prospective_input_selfAdjoint (X B : A) :
    IsSelfAdjoint (firstK X * scalingDefect (firstH X) (firstR X B) * firstK X) := by
  have hK : IsSelfAdjoint (firstK X) := .of_nonneg (ramp_nonneg X (by norm_num))
  rw [isSelfAdjoint_iff]
  simp only [star_mul, hK.star_eq, scalingDefect_selfAdjoint _ _ |>.star_eq, mul_assoc]

lemma map_prospectiveDefect {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (prospectiveDefect X B) = prospectiveDefect (π X) (π B) := by
  have hH : IsSelfAdjoint (firstH X) := .of_nonneg (ramp_nonneg X (by norm_num))
  have hn : ‖firstH X‖ ≤ 1 := norm_ramp_le_one _ (by norm_num)
  simp only [prospectiveDefect, map_ramp_sa π (prospective_input_selfAdjoint X B) le_rfl,
    map_mul, map_firstK π hX, map_scalingDefect π hH hn, map_firstH π hX,
    map_firstR π hX]

lemma map_lastX {X : A} (hX : IsSelfAdjoint X) (B : A) :
    π (lastX X B) = lastX (π X) (π B) := by
  have hp : IsSelfAdjoint (prospectiveDefect X B) := .of_nonneg (ramp_nonneg _ (by norm_num))
  rw [lastX, map_cut_sa π hp (by norm_num), map_prospectiveDefect π hX]
  rfl

lemma map_lastR {X : A} (hX : IsSelfAdjoint X) (B C : A) :
    π (lastR X B C) = lastR (π X) (π B) (π C) := by
  simp only [lastR, map_mul, map_lastX π hX,
    map_deficiency π (.mul_star_self C), map_star]

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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Ultrafilter ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable (A : Type*)
end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.ultrafilterPartialOrder
attribute [local instance] OAI.MainGap.ultrafilterStarOrderedRing
lemma cut_zero_of_le {d : A} (hd : 0 ≤ d) {h : ℝ} (hh : 0 ≤ h)
    (hle : d ≤ h • (1:A)) : cut d h = 0 := by
  have hdsa : IsSelfAdjoint d := .of_nonneg hd
  have hle' : cfc (fun t : ℝ => t) d ≤ cfc (fun _ : ℝ => h) d := by
    rw [cfc_id' ℝ d hdsa, cfc_const h d hdsa, Algebra.algebraMap_eq_smul_one]
    exact hle
  have hs := (cfc_le_iff _ _ d continuousOn_id continuousOn_const hdsa).mp hle'
  rw [cut_eq_cfc d hh, ← cfc_zero d (R := ℝ)]
  apply cfc_congr
  intro t ht
  exact max_eq_right (sub_nonpos.mpr (hs t ht))

lemma le_of_cut_zero {d : A} (hd : 0 ≤ d) {h : ℝ} (hh : 0 ≤ h)
    (hz : cut d h = 0) : d ≤ h • (1:A) := by
  have hn := norm_sub_cut_le hd hh
  rw [hz, sub_zero] at hn
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (CStarAlgebra.norm_le_iff_le_algebraMap d hh hd).mp hn

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Avoidance ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
open Filter
open scoped Topology
universe u v
variable {ι : Type*} {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.avoidanceLimitPartialOrder
attribute [local instance] OAI.MainGap.avoidanceLimitStarOrderedRing
attribute [local instance] OAI.MainGap.avoidanceLimitOperatorPartialOrder
attribute [local instance] OAI.MainGap.avoidanceLimitOperatorStarOrderedRing
variable {H : ι → Type v} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

theorem four_limit_impossible (ω : Ultrafilter ι)
    (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hV : ∀ᶠ i in (ω : Filter ι), (1/8 : ℝ) ≤ ‖π i (firstV X) (ξ i)‖)
    (hD₁ : ∀ i, π i (B 0) * star (π i (B 0)) ≤ (1/2 : ℝ) • 1)
    (hm₁ : ∀ i, π i (B 1 * star (B 1)) = π i (B 0 * star (B 0)))
    (hc₁ : ∀ i, π i (B 0 * star (B 1)) = 0)
    (hs₀ : ∀ i, π i (firstH X * star (B 0)) = π i (star (B 0)))
    (hs₁ : ∀ i, π i (firstH X * star (B 1)) = π i (star (B 1)))
    (hU : ∀ w : A, Tendsto (fun i => ‖π i (firstU X (B 0) * w * firstV X)‖)
      (ω : Filter ι) (𝓝 0))
    (hD₃ : ∀ i, π i (B 2) * star (π i (B 2)) ≤ (1/2 : ℝ) • 1)
    (hc₃ : ∀ i, π i (star (B 2) * B 3) = 0)
    (hm₃ : ∀ i, π i (star (B 2) * B 2) = π i (star (B 3) * B 3))
    (hR : Tendsto (fun i => ‖π i (lastR X (B 0) (B 2))‖) (ω : Filter ι) (𝓝 0))
    (hs₃ : ∀ i, π i (ramp (prospectiveDefect X (B 0)) 0 (1/2) * B 3) = π i (B 3)) : False := by
  let ρ := limitRep ω π ξ hξ
  let Ψ := rangeRestriction ρ (firstV X)
  have hkill : ∀ a : A, Tendsto (fun i => ‖π i a‖) (ω : Filter ι) (𝓝 0) → Ψ a = 0 := by
    intro a ha
    have hz : ρ a = 0 := limitRep_annihilates ω π ξ hξ a ha
    ext x
    change (ρ a x : LimitHilbert ω π ξ hξ) = 0
    rw [hz, zero_apply]
  have hzero : ∀ a : A, (∀ i, π i a = 0) → Ψ a = 0 := by
    intro a ha
    apply hkill a
    simp only [ha, norm_zero]
    exact tendsto_const_nhds
  have heq : ∀ a b : A, (∀ i, π i a = π i b) → Ψ a = Ψ b := by
    intro a b hab
    have hz := hzero (a-b) (fun i => by rw [map_sub, hab i, sub_self])
    exact sub_eq_zero.mp (by simpa only [map_sub] using hz)
  have hbound (j : Fin 4) (hj : ∀ i, π i (B j) * star (π i (B j)) ≤ (1/2 : ℝ) • 1) := by
    have hz := hzero (cut (B j * star (B j)) (1/2)) (fun i => by
      rw [map_cut_sa (π i) (.mul_star_self _) (by norm_num), map_mul, map_star]
      exact cut_zero_of_le (mul_star_self_nonneg _) (by norm_num) (hj i))
    rw [map_cut_sa (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (IsSelfAdjoint.mul_star_self (B j)) (by norm_num : (0:ℝ) ≤ 1/2), map_mul, map_star] at hz
    exact le_of_cut_zero (mul_star_self_nonneg _) (by norm_num) hz
  have hψV : firstV (Ψ X) ≠ 0 := by
    rw [← map_firstV (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)]
    exact rangeRestriction_nonzero ρ (firstV X) (.of_nonneg (cut_nonneg X _))
      (limitRep_nonzero ω π ξ hξ (firstV X) (by norm_num : (0:ℝ) < 1/8) hV)
  have hψU : firstU (Ψ X) (Ψ (B 0)) = 0 := by
    rw [← map_firstU (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)]
    apply rangeRestriction_kills ρ (firstV X) (firstU X (B 0))
    intro w
    simpa only [map_mul] using limitRep_annihilates ω π ξ hξ _ (hU w)
  apply four_fixed_impossible (map_nonneg Ψ hX) (fun i => Ψ (B i)) hψV
    (hbound 0 hD₁) ?_ ?_ ?_ ?_ hψU (hbound 2 hD₃) ?_ ?_ ?_ ?_
  · simpa only [map_mul, map_star] using heq _ _ hm₁
  · simpa only [map_mul, map_star] using hzero _ hc₁
  · simpa only [map_mul, map_star, map_firstH (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)] using heq _ _ hs₀
  · simpa only [map_mul, map_star, map_firstH (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)] using heq _ _ hs₁
  · simpa only [map_mul, map_star] using hzero _ hc₃
  · simpa only [map_mul, map_star] using heq _ _ hm₃
  · simpa only [map_lastR (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)] using hkill _ hR
  · have hp : IsSelfAdjoint (prospectiveDefect X (B 0)) :=
      .of_nonneg (prospectiveDefect_nonneg X _)
    simpa only [map_mul, map_ramp_sa (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ hp le_rfl, map_prospectiveDefect (D := generatedRange ρ (firstV X) →L[ℂ] generatedRange ρ (firstV X)) Ψ (.of_nonneg hX)] using
      heq _ _ hs₃

end MainGap

namespace MainGap
universe u v
open Filter
open scoped Topology
variable (A : Type u) [CStarAlgebra A]

attribute [instance] HilbertRep.normed HilbertRep.inner HilbertRep.complete

variable {A}
attribute [local instance] OAI.MainGap.avoidancePartialOrder
attribute [local instance] OAI.MainGap.avoidanceStarOrderedRing
attribute [local instance] OAI.MainGap.avoidanceOperatorPartialOrder
attribute [local instance] OAI.MainGap.avoidanceOperatorStarOrderedRing
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open Filter
open scoped Topology
attribute [local instance] OAI.MainGap.avoidanceLimitPartialOrder
attribute [local instance] OAI.MainGap.avoidanceLimitStarOrderedRing
attribute [local instance] OAI.MainGap.avoidanceLimitOperatorPartialOrder
attribute [local instance] OAI.MainGap.avoidanceLimitOperatorStarOrderedRing


theorem solution.{u,v,u_1} : type_of% @_root_.OAI.MainGap.four_limit_impossible.{u,v,u_1} := @_root_.OAI.MainGap.four_limit_impossible.{u,v,u_1}
