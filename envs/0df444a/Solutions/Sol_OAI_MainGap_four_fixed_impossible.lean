-- Prove2me | solution 1 for OAI.MainGap.four_fixed_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:39:40.444685+00:00
-- url     : https://prove2.me/submissions/246ddb6f-63d5-4000-9ce4-e82c9840457f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Defect.lean:L158-L215
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.four_fixed_impossible. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_cut_cut
import Theorems.Thm_OAI_MainGap_last_pair_kills_defect
import Theorems.Thm_OAI_MainGap_ramp_mul_cut

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

lemma Her_killed_left {h t : A} (ht : t * h = 0) {k : A} (hk : k ∈ Her h) : t * k = 0 := by
  have hc : IsClosed {k : A | t * k = 0} := isClosed_eq (by fun_prop) continuous_const
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change t * (h * a * star h) = 0
  simp only [← mul_assoc, ht, zero_mul]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

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

lemma scalingComplement_mul_self {H : A} (hH : IsSelfAdjoint H) (hnorm : ‖H‖ ≤ 1) :
    scalingComplement H * scalingComplement H = 1 - H * H :=
  CFC.sqrt_mul_sqrt_self _ (complement_nonneg hH hnorm)

lemma scalingComplement_selfAdjoint (H : A) : IsSelfAdjoint (scalingComplement H) :=
  IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)

lemma scalingComplement_mul_eq_zero {H r : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHr : H * r = r) : scalingComplement H * r = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  rw [star_mul, (scalingComplement_selfAdjoint H).star_eq]
  calc
    star r * scalingComplement H * (scalingComplement H * r) =
        star r * (scalingComplement H * scalingComplement H) * r := by noncomm_ring
    _ = star r * (1 - H * H) * r := by rw [scalingComplement_mul_self hH hnorm]
    _ = 0 := by simp only [mul_sub, sub_mul, mul_one, mul_assoc, hHr, sub_self]

lemma scalingIsometry_star_mul_self {H r : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHr : H * r = r) (hrr : star r * r = H * H) :
    star (scalingIsometry H r) * scalingIsometry H r = 1 := by
  have hbr := scalingComplement_mul_eq_zero hH hnorm hHr
  have hrb : star r * scalingComplement H = 0 := by
    simpa only [star_mul, star_zero, (scalingComplement_selfAdjoint H).star_eq] using
      congrArg star hbr
  simp only [scalingIsometry, star_add, (scalingComplement_selfAdjoint H).star_eq,
    add_mul, mul_add, hbr, hrb, hrr, scalingComplement_mul_self hH hnorm]
  noncomm_ring

lemma scalingDefect_projection {H r : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHr : H * r = r) (hrr : star r * r = H * H) :
    IsStarProjection (scalingDefect H r) := by
  apply IsStarProjection.one_sub
  constructor
  · change (scalingIsometry H r * star (scalingIsometry H r)) *
        (scalingIsometry H r * star (scalingIsometry H r)) =
      scalingIsometry H r * star (scalingIsometry H r)
    rw [mul_assoc, ← mul_assoc (star (scalingIsometry H r)),
      scalingIsometry_star_mul_self hH hnorm hHr hrr, one_mul]
  · exact IsSelfAdjoint.mul_star_self _

lemma scalingDefect_fixes_second {H r₁ r₂ : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHr₂ : H * r₂ = r₂) (hcross : star r₁ * r₂ = 0) :
    scalingDefect H r₁ * r₂ = r₂ := by
  have hvr : star (scalingIsometry H r₁) * r₂ = 0 := by
    simp only [scalingIsometry, star_add, add_mul,
      (scalingComplement_selfAdjoint H).star_eq, hcross,
      scalingComplement_mul_eq_zero hH hnorm hHr₂, add_zero]
  simp only [scalingDefect, sub_mul, one_mul, mul_assoc, hvr, mul_zero, sub_zero]

lemma scalingDefect_ne_zero {H r₁ r₂ : A} (hH : IsSelfAdjoint H)
    (hnorm : ‖H‖ ≤ 1) (hHne : H ≠ 0) (hHr₂ : H * r₂ = r₂)
    (hcross : star r₁ * r₂ = 0) (hr₂ : star r₂ * r₂ = H * H) :
    scalingDefect H r₁ ≠ 0 := by
  intro hP
  have hr₂zero : r₂ = 0 := by
    have := scalingDefect_fixes_second hH hnorm hHr₂ hcross
    simpa only [hP, zero_mul, eq_comm] using this
  apply hHne
  apply (CStarRing.star_mul_self_eq_zero_iff H).mp
  rw [hH.star_eq, ← hr₂, hr₂zero, star_zero, zero_mul]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.instPartialOrder_oAI
attribute [local instance] OAI.MainGap.instStarOrderedRing_oAI
lemma deficiency_selfAdjoint (d : A) : IsSelfAdjoint (deficiency d) := IsSelfAdjoint.cfc

lemma cut_mem_cutHer {X : A} (hX : 0 ≤ X) {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) :
    cut X u ∈ Her (cut X l) := by
  have heq : cut X u = cut (cut X l) (u-l) := by
    rw [cut_cut hX hl (sub_nonneg.mpr hlu)]
    congr 1
    ring
  rw [heq]
  exact cut_mem_Her (cut_nonneg X l) _

lemma lastX_nonneg (X B : A) : 0 ≤ lastX X B := cut_nonneg _ _
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

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourChoiceStructureOrder
attribute [local instance] OAI.MainGap.fourChoiceStructureStarOrder
universe v

lemma firstH_fixes_V {X : A} (hX : 0 ≤ X) : firstH X * firstV X = firstV X :=
  ramp_mul_cut hX (by norm_num) (by norm_num) le_rfl

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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Defect ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.deficiencyOrder
attribute [local instance] OAI.MainGap.deficiencyStarOrder
lemma deficiency_eq_sub {d : A} (hd : 0 ≤ d) (hb : d ≤ (1/2 : ℝ) • (1 : A)) :
    deficiency d = (1/2 : ℝ) • (1 : A) - d := by
  have hdsa : IsSelfAdjoint d := .of_nonneg hd
  have hb' : cfc (fun t : ℝ => t) d ≤ cfc (fun _ : ℝ => (1/2 : ℝ)) d := by
    rw [cfc_id' ℝ d hdsa, cfc_const (1/2 : ℝ) d hdsa, Algebra.algebraMap_eq_smul_one]
    exact hb
  have hs := (cfc_le_iff _ _ d continuousOn_id continuousOn_const hdsa).mp hb'
  calc
    deficiency d = cfc (fun t : ℝ => (1/2 : ℝ)-t) d := by
      apply cfc_congr
      intro t ht
      exact max_eq_left (sub_nonneg.mpr (hs t ht))
    _ = cfc (fun _ : ℝ => (1/2 : ℝ)) d - cfc (fun t : ℝ => t) d :=
      cfc_sub _ _ d continuousOn_const continuousOn_id
    _ = (1/2 : ℝ) • (1 : A) - d := by
      rw [cfc_const (1/2 : ℝ) d hdsa, cfc_id' ℝ d hdsa, Algebra.algebraMap_eq_smul_one]

lemma sandwich_zero_eigen {x d : A} (hx : 0 ≤ x) (hd : 0 ≤ d)
    (hdle : d ≤ (1/2 : ℝ) • (1 : A))
    (hU : x * deficiency d * deficiency d * x = 0) : d * x = (1/2 : ℝ) • x := by
  have hQx : deficiency d * x = 0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    simpa only [star_mul, IsSelfAdjoint.of_nonneg hx |>.star_eq,
      deficiency_selfAdjoint d |>.star_eq, mul_assoc] using hU
  rw [deficiency_eq_sub hd hdle, sub_mul, smul_mul_assoc, one_mul] at hQx
  exact (sub_eq_zero.mp hQx).symm

lemma Her_eigen_left {x d k : A} {h : ℝ} (hx : d*x=h•x) (hk : k ∈ Her x) :
    d*k=h•k := by
  have hz : (d-h • (1:A))*x=0 := by
    simp only [sub_mul, smul_mul_assoc, one_mul, hx, sub_self]
  have := Her_killed_left hz hk
  simpa only [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] using this

lemma firstH_mem_firstX {X : A} (hX : 0 ≤ X) : firstH X ∈ Her (firstX X) :=
  Her_mono_of_mem (cut_mem_cutHer hX (by norm_num : (0:ℝ) ≤ 1/16)
    (by norm_num : (1/16:ℝ) ≤ 3/32)) (ramp_mem_Her_cut hX (by norm_num))

lemma firstK_fixes_H {X : A} (hX : 0 ≤ X) : firstK X * firstH X = firstH X :=
  Her_fixed_left (ramp_mul_cut hX (by norm_num : (0:ℝ) ≤ 3/64)
    (by norm_num : (3/64:ℝ) < 1/16) le_rfl) (firstH_mem_firstX hX)

lemma firstR_inner {X B C : A} (hmod : B * star C = B * star B)
    (hDH : B * star B * firstH X = (1/2 : ℝ) • firstH X) :
    star (firstR X B) * firstR X C = firstH X * firstH X := by
  have hH : star (firstH X) = firstH X := (IsSelfAdjoint.of_nonneg (ramp_nonneg X (by norm_num : (3/32:ℝ) ≤ 1/8))).star_eq
  simp only [firstR, star_smul, star_trivial, star_mul, hH, star_star,
    smul_mul_smul]
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  calc
    (2:ℝ) • ((firstH X * B) * (star C * firstH X)) =
      (2:ℝ) • (firstH X * ((B * star C) * firstH X)) := by congr 1; noncomm_ring
    _ = firstH X * firstH X := by rw [hmod, hDH, mul_smul_comm, smul_smul]; norm_num

lemma firstR_orthogonal {X B C : A} (hcross : B * star C = 0) :
    star (firstR X B) * firstR X C = 0 := by
  simp only [firstR, star_smul, star_trivial, star_mul, star_star, smul_mul_smul]
  calc
    _ = (Real.sqrt 2 * Real.sqrt 2) • (star (firstH X) * (B * star C) * firstH X) := by
      congr 1; noncomm_ring
    _ = 0 := by rw [hcross, mul_zero, zero_mul, smul_zero]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.scalingDefectOrder
attribute [local instance] OAI.MainGap.scalingDefectStarOrder
lemma ramp_projection {P : A} (hP : IsStarProjection P) {l u : ℝ} (hl : 0 ≤ l)
    (hlu : l < u) (hu : u ≤ 1) : ramp P l u = P := by
  conv_rhs => rw [← cfcₙ_id ℝ P hP.isSelfAdjoint]
  apply cfcₙ_congr
  intro t ht
  rcases Set.mem_insert_iff.mp (hP.isIdempotentElem.quasispectrum_subset ℝ ht) with ht | ht
  · subst t
    exact rampFn_zero hl
  · have ht : t = 1 := Set.mem_singleton_iff.mp ht
    subst t
    exact rampFn_one hlu hu

lemma cut_projection {P : A} (hP : IsStarProjection P) {l : ℝ} (hl : 0 ≤ l) (hl1 : l ≤ 1) :
    cut P l = (1-l) • P := by
  conv_rhs => rw [← cfcₙ_id ℝ P hP.isSelfAdjoint]
  rw [← cfcₙ_smul (1-l) id P continuousOn_id rfl]
  apply cfcₙ_congr
  intro t ht
  rcases Set.mem_insert_iff.mp (hP.isIdempotentElem.quasispectrum_subset ℝ ht) with ht | ht
  · subst t
    simp [max_eq_right (neg_nonpos.mpr hl)]
  · have ht : t = 1 := Set.mem_singleton_iff.mp ht
    subst t
    simp [max_eq_left (sub_nonneg.mpr hl1)]

lemma scalingDefect_expansion {H r : A} (hH : IsSelfAdjoint H) (hnorm : ‖H‖ ≤ 1) :
    scalingDefect H r = H*H-r*star r-r*scalingComplement H-scalingComplement H*star r := by
  have hb := scalingComplement_mul_self hH hnorm
  simp only [scalingDefect, scalingIsometry, star_add, scalingComplement_selfAdjoint H |>.star_eq,
    add_mul, mul_add]
  rw [hb]
  noncomm_ring

lemma scalingDefect_compress {H K r : A} (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    (hnorm : ‖H‖ ≤ 1) (hKH : K*H=H) (hHr : H*r=r) (hrK : r*K=r) :
    K * scalingDefect H r * K = scalingDefect H r := by
  have hHK : H*K=H := by
    simpa only [star_mul, hH.star_eq, hK.star_eq] using congrArg star hKH
  have hKr : K*r=r := by rw [← hHr, ← mul_assoc, hKH]
  have hsrK : star r*K=star r := by
    simpa only [star_mul, hK.star_eq, star_star] using congrArg star hKr
  have hKsr : K*star r=star r := by
    simpa only [star_mul, hK.star_eq, star_star] using congrArg star hrK
  have hcomm : Commute K H := (show K*H=H*K by rw [hKH,hHK])
  have hbcomm : Commute K (scalingComplement H) := by
    exact ((Commute.one_right K).sub_right (hcomm.mul_right hcomm)).symm.cfcₙ_nnreal NNReal.sqrt |>.symm
  have hleft : K * scalingDefect H r = scalingDefect H r := by
    rw [scalingDefect_expansion hH hnorm]
    simp only [mul_sub, ← mul_assoc, hKH, hKr]
    rw [hbcomm.eq, mul_assoc, hKsr]
  have hright : scalingDefect H r * K = scalingDefect H r := by
    simpa only [star_mul, hK.star_eq, show star (scalingDefect H r) = scalingDefect H r from
      ((IsSelfAdjoint.one A).sub (IsSelfAdjoint.mul_star_self _)).star_eq] using congrArg star hleft
  rw [hleft, hright]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourFixedOrder
attribute [local instance] OAI.MainGap.fourFixedStarOrder
theorem four_fixed_impossible {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hV : firstV X ≠ 0)
    (hD : B 0 * star (B 0) ≤ (1/2 : ℝ) • (1 : A))
    (hmod : B 1 * star (B 1) = B 0 * star (B 0))
    (hcross : B 0 * star (B 1) = 0)
    (hHB₀ : firstH X * star (B 0) = star (B 0))
    (hHB₁ : firstH X * star (B 1) = star (B 1))
    (hU : firstU X (B 0) = 0)
    (hD₃ : B 2 * star (B 2) ≤ (1/2 : ℝ) • (1 : A))
    (hc₃ : star (B 2) * B 3 = 0)
    (hm₃ : star (B 2) * B 2 = star (B 3) * B 3)
    (hR : lastR X (B 0) (B 2) = 0)
    (hs₃ : ramp (prospectiveDefect X (B 0)) 0 (1/2) * B 3 = B 3) : False := by
  have hH : IsSelfAdjoint (firstH X) := .of_nonneg (ramp_nonneg X (by norm_num))
  have hK : IsSelfAdjoint (firstK X) := .of_nonneg (ramp_nonneg X (by norm_num))
  have hHnorm : ‖firstH X‖ ≤ 1 := norm_ramp_le_one _ (by norm_num)
  have hHne : firstH X ≠ 0 := by
    intro hz
    apply hV
    simpa only [hz, zero_mul] using (firstH_fixes_V hX).symm
  have hDx : (B 0 * star (B 0)) * firstX X = (1/2 : ℝ) • firstX X :=
    sandwich_zero_eigen (cut_nonneg X _) (mul_star_self_nonneg _) hD hU
  have hDH : (B 0 * star (B 0)) * firstH X = (1/2 : ℝ) • firstH X :=
    Her_eigen_left hDx (firstH_mem_firstX hX)
  have hρ₀ : star (firstR X (B 0)) * firstR X (B 0) = firstH X * firstH X :=
    firstR_inner rfl hDH
  have hρ₁ : star (firstR X (B 1)) * firstR X (B 1) = firstH X * firstH X :=
    firstR_inner rfl (hmod ▸ hDH)
  have hρc : star (firstR X (B 0)) * firstR X (B 1) = 0 := firstR_orthogonal hcross
  have hHr₀ : firstH X * firstR X (B 0) = firstR X (B 0) := by
    simp only [firstR, mul_smul_comm, ← mul_assoc, hHB₀]
  have hHr₁ : firstH X * firstR X (B 1) = firstR X (B 1) := by
    simp only [firstR, mul_smul_comm, ← mul_assoc, hHB₁]
  let P := scalingDefect (firstH X) (firstR X (B 0))
  have hP : IsStarProjection P := scalingDefect_projection hH hHnorm hHr₀ hρ₀
  have hPne : P ≠ 0 := scalingDefect_ne_zero hH hHnorm hHne hHr₁ hρc hρ₁
  have hKH : firstK X * firstH X = firstH X := firstK_fixes_H hX
  have hHK : firstH X * firstK X = firstH X := by
    simpa only [star_mul, hK.star_eq, hH.star_eq] using congrArg star hKH
  have hrK : firstR X (B 0) * firstK X = firstR X (B 0) := by
    simp only [firstR, smul_mul_assoc, mul_assoc, hHK]
  have hP₀ : prospectiveDefect X (B 0) = P := by
    change ramp (firstK X * P * firstK X) 0 1 = P
    rw [scalingDefect_compress hH hK hHnorm hKH hHr₀ hrK]
    exact ramp_projection hP (by norm_num) (by norm_num) le_rfl
  have hx' : lastX X (B 0) = (1/2 : ℝ) • P := by
    simp only [lastX, hP₀, cut_projection hP (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1)]
    norm_num
  have hD₃x : (B 2 * star (B 2)) * lastX X (B 0) = (1/2 : ℝ) • lastX X (B 0) :=
    sandwich_zero_eigen (lastX_nonneg X _) (mul_star_self_nonneg _) hD₃ hR
  have hD₃P : (B 2 * star (B 2)) * P = (1/2 : ℝ) • P := by
    rw [hx', mul_smul_comm, smul_comm] at hD₃x
    exact (smul_right_injective A (by norm_num : (1/2 : ℝ) ≠ 0)) hD₃x
  have hPB : P * B 3 = B 3 := by
    rw [hP₀, ramp_projection hP (by norm_num) (by norm_num) (by norm_num)] at hs₃
    exact hs₃
  exact hPne (last_pair_kills_defect (by norm_num : (1/2 : ℝ) ≠ 0) hPB hc₃ hm₃ hD₃P)

end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
attribute [local instance] OAI.MainGap.defectSandwichOrder
attribute [local instance] OAI.MainGap.defectSandwichStarOrder
attribute [local instance] OAI.MainGap.representedDefectOrder
attribute [local instance] OAI.MainGap.representedDefectStarOrder
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.fourFixedOrder
attribute [local instance] OAI.MainGap.fourFixedStarOrder


theorem solution : type_of% @_root_.OAI.MainGap.four_fixed_impossible := @_root_.OAI.MainGap.four_fixed_impossible
