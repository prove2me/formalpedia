-- Prove2me | solution 1 for OAI.MainGap.last_pair_choice
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:35:57.076864+00:00
-- url     : https://prove2.me/submissions/150f298c-f443-49fb-9273-0814f10c9307

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/ChoicePairs.lean:L72-L103
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.last_pair_choice. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_ProperlyInfinite_finite_copies
import Theorems.Thm_OAI_MainGap_cut_cut
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

theorem ProperlyInfinite.orthogonalSlots {d : A} (hd : 0 ≤ d) (hp : ProperlyInfinite d)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) : Nonempty (OrthogonalSlots n (cut d ε) d) :=
  orthogonalSlots_of_comparison hd hd (hp.finite_copies n) hε

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
lemma carrier_mem_Her {n : ℕ} {h v k : A} (S : OrthogonalSlots n h v)
    (hv : v ∈ Her k) (i : Fin n) (e : Her h) (he : (e : A) ∈ Her k) :
    S.carrier i e ∈ Her k := by
  apply mem_Her_of_moduli
  · exact Her_mono_of_mem hv (S.outer i i e e)
  · rw [S.inner, ite_eq_left rfl]
    exact (Her k).mul_mem ((Her k).star_mem' he) he

theorem last_pair_choice {R k : A} (hR : 0 ≤ R) (hRk : R ∈ Her k)
    {η : ℝ} (hη : 0 < η) (hp : ProperlyInfinite (cut R η)) :
    ∃ T : Fin 2 → A,
      (∀ i, ‖T i‖ ≤ 1) ∧ (∀ i, T i ∈ Her k) ∧
      (∀ i j, star (T i) * T j = if i=j then ramp R (2*η) (4*η) * ramp R (2*η) (4*η) else 0) ∧
      (∀ i j, T i * star (T j) ∈ Her (cut R η)) ∧
      (∀ {B : Type*} [NonUnitalCStarAlgebra B] (π : A →⋆ₙₐ[ℂ] B),
        4*η ≤ ‖π R‖ → ∀ i, ‖π (T i)‖ = 1) := by
  let t := ramp R (2*η) (4*η)
  have ht : t ∈ Her (cut (cut R η) η) := by
    rw [cut_cut hR hη.le hη.le, ← two_mul η]
    exact ramp_mem_Her_cut hR (by positivity)
  let e : Her (cut (cut R η) η) := ⟨t, ht⟩
  obtain ⟨S⟩ := hp.orthogonalSlots (cut_nonneg R η) 2 hη
  have hcut : cut R η ∈ Her k := Her_mono_of_mem hRk (cut_mem_Her hR η)
  have htk : t ∈ Her k := Her_mono_of_mem hRk
    (Her_mono_of_mem (cut_mem_Her hR (2*η)) (ramp_mem_Her_cut hR (by positivity)))
  refine ⟨fun i => S.carrier i e, ?_, ?_, ?_, (fun i j => S.outer i j e e), ?_⟩
  · intro i
    rw [S.norm_carrier]
    exact norm_ramp_le_one R (by linarith)
  · intro i
    exact carrier_mem_Her S hcut i e htk
  · intro i j
    rw [S.inner, (IsSelfAdjoint.of_nonneg (ramp_nonneg R (by linarith : 2*η ≤ 4*η))).star_eq]
  · intro B _ π hnorm i
    let : PartialOrder B := CStarAlgebra.spectralOrder B
    let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    rw [S.represented_norm]
    change ‖π (ramp R (2*η) (4*η))‖ = 1
    rw [map_ramp π hR (by positivity)]
    exact norm_ramp_eq_one (map_nonneg π hR) (by positivity) (by linarith) hnorm

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


theorem solution : type_of% @_root_.OAI.MainGap.last_pair_choice := @_root_.OAI.MainGap.last_pair_choice
