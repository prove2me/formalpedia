-- Prove2me | solution 1 for OAI.MainGap.first_pair_choice
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:34:02.908526+00:00
-- url     : https://prove2.me/submissions/39ca3e81-a2ae-482e-90ad-6520885eb939

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/ChoicePairs.lean:L41-L70
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.first_pair_choice. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_mem_Her_of_moduli
import Theorems.Thm_OAI_MainGap_orthogonalSlots_of_comparison

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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.OrthogonalSlots ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
open scoped CStarAlgebra
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass
namespace RegularTransport
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

end RegularTransport

namespace OrthogonalSlots
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

lemma represented_norm {B : Type*} [NonUnitalCStarAlgebra B]
    (π : A →⋆ₙₐ[ℂ] B) (i : Fin n) (k : Her h) :
    ‖π (S.carrier i k)‖ = ‖π (k : A)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul,
    S.inner, ite_true]

lemma norm_carrier (i : Fin n) (k : Her h) : ‖S.carrier i k‖ = ‖(k : A)‖ :=
  S.represented_norm (NonUnitalStarAlgHom.id ℂ A) i k

end OrthogonalSlots

section FiniteSum

end FiniteSum
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

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.ChoicePairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.choicePairsPartialOrder
attribute [local instance] OAI.MainGap.choicePairsStarOrderedRing
lemma norm_sqrt_le_one {d : A} (hd : 0 ≤ d) (hn : ‖d‖ ≤ 1) : ‖CFC.sqrt d‖ ≤ 1 := by
  have hh : ‖CFC.sqrt d‖ ^ 2 = ‖d‖ := by
    rw [pow_two, ← CStarRing.norm_star_mul_self,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg d)).star_eq, CFC.sqrt_mul_sqrt_self d hd]
  nlinarith [norm_nonneg (CFC.sqrt d)]

lemma carrier_mem_Her {n : ℕ} {h v k : A} (S : OrthogonalSlots n h v)
    (hv : v ∈ Her k) (i : Fin n) (e : Her h) (he : (e : A) ∈ Her k) :
    S.carrier i e ∈ Her k := by
  apply mem_Her_of_moduli
  · exact Her_mono_of_mem hv (S.outer i i e e)
  · rw [S.inner, ite_eq_left rfl]
    exact (Her k).mul_mem ((Her k).star_mem' he) he

theorem first_pair_choice {d v k : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hdv : FiniteCuntzLE (diagonalCorner 2 d) (scalarCorner v))
    (hdk : d ∈ Her k) (hvk : v ∈ Her k) {η : ℝ} (hη : 0 < η) :
    ∃ T : Fin 2 → A,
      (∀ i, ‖T i‖ ≤ 1) ∧ (∀ i, T i ∈ Her k) ∧
      (∀ i j, T i * star (T j) = if i=j then ramp d η (2*η) else 0) ∧
      (∀ i j, star (T i) * T j ∈ Her v) := by
  let D := ramp d η (2*η)
  have hDpos : 0 ≤ D := ramp_nonneg d (by linarith)
  have hDmem : D ∈ Her (cut d η) := ramp_mem_Her_cut hd hη.le
  let e : Her (cut d η) := ⟨CFC.sqrt D, sqrt_mem_Her hDmem hDpos⟩
  obtain ⟨S⟩ := orthogonalSlots_of_comparison hd hv hdv hη
  have hnorm : ‖(e : A)‖ ≤ 1 := norm_sqrt_le_one hDpos (norm_ramp_le_one d (by linarith))
  have he : (e : A) ∈ Her k :=
    Her_mono_of_mem hdk (Her_mono_of_mem (cut_mem_Her hd η) e.property)
  have hsa : star (e : A) = (e : A) := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)).star_eq
  refine ⟨fun i => star (S.carrier i e), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [norm_star, S.norm_carrier]
    exact hnorm
  · intro i
    exact (Her k).star_mem' (carrier_mem_Her S hvk i e he)
  · intro i j
    rw [star_star, S.inner, hsa]
    split_ifs
    · exact CFC.sqrt_mul_sqrt_self D hDpos
    · rfl
  · intro i j
    rw [star_star]
    exact S.outer i j e e

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.instPartialOrder_oAI
attribute [local instance] OAI.MainGap.instStarOrderedRing_oAI
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.choicePairsPartialOrder
attribute [local instance] OAI.MainGap.choicePairsStarOrderedRing


theorem solution : type_of% @_root_.OAI.MainGap.first_pair_choice := @_root_.OAI.MainGap.first_pair_choice
