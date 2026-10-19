-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.intrinsic_tail_test
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:59:15.332871+00:00
-- url     : https://prove2.me/submissions/f2572dbb-a317-4b92-8f0e-3444f81e3024

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L1104-L1129
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.intrinsic_tail_test. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_finite_lens_test

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
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

lemma headDual_finite_apply {H : Finset ι} (x : T.Dual) (u : T.Primal)
    (hu : (T.ofPrimal u).support ⊆ H) :
    T.headDual H x (u : T.JamesSpace) = x (u : T.JamesSpace) := by
  rw [dual_coe_apply, dual_coe_apply]
  apply Finset.sum_congr rfl
  intro v hv
  rw [headDual_unit, ite_eq_left (hu hv)]

lemma headDual_commute (H K : Finset ι) (x : T.Dual) :
    T.headDual H (T.headDual K x) = T.headDual K (T.headDual H x) := by
  apply T.dual_ext
  intro v
  simp only [headDual_unit]
  split_ifs <;> rfl

lemma tailDual_headDual (H K : Finset ι) (x : T.Dual) :
    T.tailDual H (T.headDual K x) = T.headDual K (T.tailDual H x) := by
  rw [tailDual_apply, tailDual_apply, map_sub, headDual_commute]

variable {T}

variable (T)

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
/-- Finite restrictions suffice for the full dual estimate: no shrinking or
    reflexivity hypothesis is needed for this intrinsic finite-head bound. -/
lemma intrinsic_tail_test
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ} (hR : 0 < R)
    {x y : A.segments.Dual} (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R)
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H y‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    obtain ⟨K,hsub,hK⟩ := hfin (H ∪ (A.segments.ofPrimal u).support)
    have hHK : H ⊆ K := Finset.Subset.trans Finset.subset_union_left hsub
    have huK : (A.segments.ofPrimal u).support ⊆ K :=
      Finset.Subset.trans Finset.subset_union_right hsub
    have ht := A.finite_lens_test hH hK hHK hR hx hplus hminus p hp hpn
    calc
      _ = ‖A.segments.tailDual H (A.segments.headDual K y) (u : A.segments.JamesSpace)‖ := by
        rw [SegmentSystem.tailDual_headDual, A.segments.headDual_finite_apply _ u huK]
      _ ≤ ‖A.segments.tailDual H (A.segments.headDual K y)‖ * ‖(u : A.segments.JamesSpace)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)

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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.intrinsic_tail_test := @_root_.OAI.DiamondDistortion.Ancestry.intrinsic_tail_test
