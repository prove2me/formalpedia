-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.separated_lens
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:09:52.680769+00:00
-- url     : https://prove2.me/submissions/6644664e-2877-4bbf-908b-805de3e3f95d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L1269-L1333
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.separated_lens. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_finite_head_pair
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_intrinsic_tail_sq
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_primal_filter_le

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma sum_units_eq_filter (H : Finset ι) (u : T.Primal) :
    (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) = T.filterPrimal (· ∈ H) u := by
  classical
  apply Finsupp.ext
  intro w
  change T.ofPrimal (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v) w =
    T.ofPrimal (T.filterPrimal (· ∈ H) u) w
  simp only [ofPrimal_sum, ofPrimal_smul, ofPrimal_filter, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp [ofPrimal, unitFinite, Finsupp.single_apply,
    mul_ite, Finset.sum_ite_eq']
  convert (Finsupp.filter_apply (· ∈ H) (T.ofPrimal u) w).symm using 1
  all_goals congr

lemma headPrimal_coe (H : Finset ι) (u : T.Primal) :
    T.headPrimal H (u : T.JamesSpace) =
      (T.filterPrimal (· ∈ H) u : T.JamesSpace) := by
  classical
  rw [headPrimal_apply, ← T.sum_units_eq_filter]
  simp only [coordinate_coe, unitVector]
  change (∑ v ∈ H, T.ofPrimal u v •
    (UniformSpace.Completion.toComplL (𝕜 := ℝ)) (T.unitFinite v)) =
    (UniformSpace.Completion.toComplL (𝕜 := ℝ)) (∑ v ∈ H, T.ofPrimal u v • T.unitFinite v)
  simp only [map_sum, map_smul]

lemma headDual_apply_apply (H : Finset ι) (x : T.Dual) (u : T.JamesSpace) :
    T.headDual H x u = x (T.headPrimal H u) := by
  simp [headDual_apply, headPrimal_apply, mul_comm]

variable {T}

variable (T)

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
lemma headPrimal_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (u : A.segments.JamesSpace) : ‖A.segments.headPrimal H u‖ ≤ ‖u‖ := by
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [SegmentSystem.headPrimal_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact A.primal_filter_le hH u

lemma headDual_norm_le {H : Finset ι} (hH : A.Ancestral (H : Set ι))
    (x : A.segments.Dual) : ‖A.segments.headDual H x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  rw [SegmentSystem.headDual_apply_apply]
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (A.headPrimal_norm_le hH u)
    (norm_nonneg _))

lemma norm_center_le {x y : A.segments.Dual} {R : ℝ}
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) : ‖x‖ ≤ R := by
  have h := (norm_add_le (x+y) (x-y)).trans (add_le_add hplus hminus)
  have he : (x+y)+(x-y) = (2:ℝ) • x := by module
  rw [he, norm_smul, Real.norm_eq_abs] at h
  norm_num at h
  linarith

lemma average_lens {x : A.segments.Dual} (z : ℕ → A.segments.Dual) {R : ℝ}
    (hplus : ∀ i, ‖x+z i‖ ≤ R) (hminus : ∀ i, ‖x-z i‖ ≤ R) (i j : ℕ) :
    ‖x+(1/2:ℝ) • (z i-z j)‖ ≤ R ∧ ‖x-(1/2:ℝ) • (z i-z j)‖ ≤ R := by
  have hp : x+(1/2:ℝ) • (z i-z j) = (1/2:ℝ) • ((x+z i)+(x-z j)) := by module
  have hm : x-(1/2:ℝ) • (z i-z j) = (1/2:ℝ) • ((x-z i)+(x+z j)) := by module
  constructor
  · rw [hp,norm_smul,Real.norm_eq_abs]
    norm_num
    have h := (norm_add_le (x+z i) (x-z j)).trans (add_le_add (hplus i) (hminus j))
    linarith
  · rw [hm,norm_smul,Real.norm_eq_abs]
    norm_num
    have h := (norm_add_le (x-z i) (x+z j)).trans (add_le_add (hminus i) (hplus j))
    linarith

/-- Exact separated-lens consequence of the intrinsic estimate. Its only
    approximation input is explicitly proved for each target model below. -/
lemma separated_lens
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {x : A.segments.Dual}
    (happrox : ∀ η > 0, ∃ H : Finset ι, A.Ancestral (H : Set ι) ∧ ‖A.segments.tailDual H x‖ < η)
    (z : ℕ → A.segments.Dual) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hplus : ∀ i, ‖x+z i‖ ≤ R) (hminus : ∀ i, ‖x-z i‖ ≤ R)
    (hsep : ∀ i j, i ≠ j → ε ≤ ‖z i-z j‖) :
    ‖x‖^2+ε^2/16 ≤ R^2 := by
  have hxr : ‖x‖ ≤ R := A.norm_center_le (hplus 0) (hminus 0)
  have hz (i : ℕ) : ‖z i‖ ≤ R := by
    apply A.norm_center_le (x := z i) (y := x)
    · simpa only [add_comm] using hplus i
    · simpa only [norm_sub_rev] using hminus i
  apply le_of_forall_pos_le_add
  intro δ hδ
  let C : ℝ := 8*R+8*‖x‖+ε+4
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := min (ε/4) (min 1 (δ/C))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by norm_num) (div_pos hδ hC))
  have hηε : η < ε/2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : C*η ≤ δ := by
    have hh : η ≤ δ/C := (min_le_right _ _).trans (min_le_right _ _)
    nlinarith [(le_div_iff₀ hC).mp hh]
  obtain ⟨H,hH,hclose⟩ := happrox η hη
  let p := A.segments.headDual H x
  have hp : ∀ v, v ∉ H → p (A.segments.unitVector v)=0 := by
    intro v hv
    exact (A.segments.headDual_unit H x v).trans (ite_eq_right hv)
  have hpn : ‖p‖ ≤ ‖x‖ := A.headDual_norm_le hH x
  have hsmall : ‖x-p‖ < η := hclose
  have hplower : ‖x‖-η ≤ ‖p‖ := by
    have h := norm_sub_norm_le x p
    linarith
  obtain ⟨i,j,hij,hhead⟩ := A.finite_head_pair hH z hz hη
  let w := (1/2:ℝ) • (z i-z j)
  have hw : ε/2 ≤ ‖w‖ := by
    dsimp [w]
    rw [norm_smul,Real.norm_eq_abs]
    norm_num
    linarith [hsep i j hij]
  have hwl : ε/2-η ≤ ‖A.segments.tailDual H w‖ := by
    have h := norm_sub_norm_le w (A.segments.headDual H w)
    change ‖w‖-‖A.segments.headDual H w‖ ≤ ‖A.segments.tailDual H w‖ at h
    linarith
  obtain ⟨hwp,hwm⟩ := A.average_lens z hplus hminus i j
  have hpp : ‖p+w‖ ≤ R+η := by
    have he : p+w = (x+w)-(x-p) := by module
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hwp hsmall.le)
  have hpm : ‖p-w‖ ≤ R+η := by
    have he : p-w = (x-w)-(x-p) := by module
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hwm hsmall.le)
  have hbudget := A.intrinsic_tail_sq hfin hH (add_nonneg hR hη.le) hp hpp hpm
  have hpsq : ‖x‖^2 - 2*‖x‖*η ≤ ‖p‖^2 := by
    nlinarith [sq_nonneg (‖x‖-‖p‖),mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hplower)]
  have hw2 : (ε/2)^2-ε*η ≤ ‖A.segments.tailDual H w‖^2 := by
    have hh := (sq_le_sq₀ (by linarith : 0 ≤ ε/2-η) (norm_nonneg _)).2 hwl
    nlinarith
  have hη2 : η^2 ≤ η := by nlinarith
  dsimp [C] at hηδ
  nlinarith

end Ancestry

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.separated_lens := @_root_.OAI.DiamondDistortion.Ancestry.separated_lens
